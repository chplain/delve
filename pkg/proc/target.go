package proc

import (
	"bytes"
	"errors"
	"fmt"
	"go/ast"
	"go/token"
	"path/filepath"
	"strings"

	"github.com/go-delve/delve/pkg/dwarf/reader"
)

const (
	optStepOver = 0
	optStepInto = 1 << iota
	optInlineStepout
)

// Target represents the process being debugged.
type Target struct {
	Process

	// fncallForG stores a mapping of current active function calls.
	fncallForG map[int]*callInjection

	asyncPreemptChanged bool  // runtime/debug.asyncpreemptoff was changed
	asyncPreemptOff     int64 // cached value of runtime/debug.asyncpreemptoff

	// gcache is a cache for Goroutines that we
	// have read and parsed from the targets memory.
	// This must be cleared whenever the target is resumed.
	gcache goroutineCache
}

// NewTarget returns an initialized Target object.
func NewTarget(p Process, disableAsyncPreempt bool) *Target {
	t := &Target{
		Process:    p,
		fncallForG: make(map[int]*callInjection),
	}
	t.gcache.init(p.BinInfo())

	if disableAsyncPreempt {
		setAsyncPreemptOff(t, 1)
	}

	return t
}

// Continue continues execution of the debugged
// process. It will continue until it hits a breakpoint
// or is otherwise stopped.
func (t *Target) Continue() error {
	if _, err := t.Valid(); err != nil {
		return err
	}
	for _, thread := range t.ThreadList() {
		thread.Common().returnValues = nil
	}
	t.CheckAndClearManualStopRequest()
	defer func() {
		// Make sure we clear internal breakpoints if we simultaneously receive a
		// manual stop request and hit a breakpoint.
		if t.CheckAndClearManualStopRequest() {
			t.ClearInternalBreakpoints()
		}
	}()
	for {
		if t.CheckAndClearManualStopRequest() {
			t.ClearInternalBreakpoints()
			return nil
		}
		t.ClearAllGCache()
		trapthread, err := t.ContinueOnce()
		if err != nil {
			return err
		}

		threads := t.ThreadList()

		callInjectionDone, err := callInjectionProtocol(t, threads)
		if err != nil {
			return err
		}

		if err := pickCurrentThread(t, trapthread, threads); err != nil {
			return err
		}

		curthread := t.CurrentThread()
		curbp := curthread.Breakpoint()

		switch {
		case curbp.Breakpoint == nil:
			// runtime.Breakpoint, manual stop or debugCallV1-related stop
			recorded, _ := t.Recorded()
			if recorded {
				return conditionErrors(threads)
			}

			loc, err := curthread.Location()
			if err != nil || loc.Fn == nil {
				return conditionErrors(threads)
			}
			g, _ := GetG(curthread)
			arch := t.BinInfo().Arch

			switch {
			case loc.Fn.Name == "runtime.breakpoint":
				// In linux-arm64, PtraceSingleStep seems cannot step over BRK instruction
				// (linux-arm64 feature or kernel bug maybe).
				if !arch.BreakInstrMovesPC() {
					curthread.SetPC(loc.PC + uint64(arch.BreakpointSize()))
				}
				// Single-step current thread until we exit runtime.breakpoint and
				// runtime.Breakpoint.
				// On go < 1.8 it was sufficient to single-step twice on go1.8 a change
				// to the compiler requires 4 steps.
				if err := stepInstructionOut(t, curthread, "runtime.breakpoint", "runtime.Breakpoint"); err != nil {
					return err
				}
				return conditionErrors(threads)
			case g == nil || t.fncallForG[g.ID] == nil:
				// a hardcoded breakpoint somewhere else in the code (probably cgo), or manual stop in cgo
				if !arch.BreakInstrMovesPC() {
					bpsize := arch.BreakpointSize()
					bp := make([]byte, bpsize)
					_, err = t.CurrentThread().ReadMemory(bp, uintptr(loc.PC))
					if bytes.Equal(bp, arch.BreakpointInstruction()) {
						curthread.SetPC(loc.PC + uint64(bpsize))
					}
				}
				return conditionErrors(threads)
			}
		case curbp.Active && curbp.Internal:
			switch curbp.Kind {
			case StepBreakpoint:
				// See description of proc.(*Process).next for the meaning of StepBreakpoints
				if err := conditionErrors(threads); err != nil {
					return err
				}
				regs, err := curthread.Registers(false)
				if err != nil {
					return err
				}
				pc := regs.PC()
				text, err := disassemble(curthread, regs, t.Breakpoints(), t.BinInfo(), pc, pc+uint64(t.BinInfo().Arch.MaxInstructionLength()), true)
				if err != nil {
					return err
				}
				// here we either set a breakpoint into the destination of the CALL
				// instruction or we determined that the called function is hidden,
				// either way we need to resume execution
				if err = setStepIntoBreakpoint(t, text, SameGoroutineCondition(t.SelectedGoroutine())); err != nil {
					return err
				}
			default:
				curthread.Common().returnValues = curbp.Breakpoint.returnInfo.Collect(curthread)
				if err := t.ClearInternalBreakpoints(); err != nil {
					return err
				}
				return conditionErrors(threads)
			}
		case curbp.Active:
			onNextGoroutine, err := onNextGoroutine(curthread, t.Breakpoints())
			if err != nil {
				return err
			}
			if onNextGoroutine {
				err := t.ClearInternalBreakpoints()
				if err != nil {
					return err
				}
			}
			if curbp.Name == UnrecoveredPanic {
				t.ClearInternalBreakpoints()
			}
			return conditionErrors(threads)
		default:
			// not a manual stop, not on runtime.Breakpoint, not on a breakpoint, just repeat
		}
		if callInjectionDone {
			// a call injection was finished, don't let a breakpoint with a failed
			// condition or a step breakpoint shadow this.
			return conditionErrors(threads)
		}
	}
}

// Next continues execution until the next source line, stepping
// over function calls. If the end of a function is reached, Next
// will continue to the the function return address.
func (t *Target) Next() (err error) {
	if _, err := t.Valid(); err != nil {
		return err
	}
	if t.Breakpoints().HasInternalBreakpoints() {
		return fmt.Errorf("next while nexting")
	}

	if err = next(t, optStepOver); err != nil {
		t.ClearInternalBreakpoints()
		return
	}

	return t.Continue()
}

// Step will continue until another source line is reached.
// Step will step into functions instead of stepping over them.
func (t *Target) Step() (err error) {
	if _, err := t.Valid(); err != nil {
		return err
	}
	if t.Breakpoints().HasInternalBreakpoints() {
		return fmt.Errorf("next while nexting")
	}

	if err = next(t, optStepInto); err != nil {
		switch err.(type) {
		case ErrThreadBlocked: // Noop
		default:
			t.ClearInternalBreakpoints()
			return
		}
	}

	return t.Continue()
}

// StepInstruction will continue the current thread for exactly
// one instruction. This method affects only the thread
// associated with the selected goroutine. All other
// threads will remain stopped.
func (t *Target) StepInstruction() (err error) {
	thread := t.CurrentThread()
	g := t.SelectedGoroutine()
	if g != nil {
		if g.Thread == nil {
			// Step called on parked goroutine
			if _, err := t.SetBreakpoint(g.PC, NextBreakpoint,
				SameGoroutineCondition(t.SelectedGoroutine())); err != nil {
				return err
			}
			return t.Continue()
		}
		thread = g.Thread
	}
	t.ClearAllGCache()
	if ok, err := t.Valid(); !ok {
		return err
	}
	thread.Breakpoint().Clear()
	err = thread.StepInstruction()
	if err != nil {
		return err
	}
	err = thread.SetCurrentBreakpoint(true)
	if err != nil {
		return err
	}
	if tg, _ := GetG(thread); tg != nil {
		t.SetSelectedGoroutine(tg)
	}
	return nil
}

// StepOut will continue until the current goroutine exits the
// function currently being executed or a deferred function is executed
func (t *Target) StepOut() error {
	if _, err := t.Valid(); err != nil {
		return err
	}
	if t.Breakpoints().HasInternalBreakpoints() {
		return fmt.Errorf("next while nexting")
	}

	selg := t.SelectedGoroutine()
	curthread := t.CurrentThread()

	topframe, retframe, err := topframe(selg, curthread)
	if err != nil {
		return err
	}

	success := false
	defer func() {
		if !success {
			t.ClearInternalBreakpoints()
		}
	}()

	if topframe.Inlined {
		if err := next(t, optInlineStepout); err != nil {
			return err
		}

		success = true
		return t.Continue()
	}

	sameGCond := SameGoroutineCondition(selg)
	retFrameCond := andFrameoffCondition(sameGCond, retframe.FrameOffset())

	var deferpc uint64
	if filepath.Ext(topframe.Current.File) == ".go" {
		if topframe.TopmostDefer != nil && topframe.TopmostDefer.DeferredPC != 0 {
			deferfn := t.BinInfo().PCToFunc(topframe.TopmostDefer.DeferredPC)
			deferpc, err = FirstPCAfterPrologue(t, deferfn, false)
			if err != nil {
				return err
			}
		}
	}

	if deferpc != 0 && deferpc != topframe.Current.PC {
		bp, err := t.SetBreakpoint(deferpc, NextDeferBreakpoint, sameGCond)
		if err != nil {
			if _, ok := err.(BreakpointExistsError); !ok {
				return err
			}
		}
		if bp != nil {
			// For StepOut we do not want to step into the deferred function
			// when it's called by runtime.deferreturn so we do not populate
			// DeferReturns.
			bp.DeferReturns = []uint64{}
		}
	}

	if topframe.Ret == 0 && deferpc == 0 {
		return errors.New("nothing to stepout to")
	}

	if topframe.Ret != 0 {
		bp, err := t.SetBreakpoint(topframe.Ret, NextBreakpoint, retFrameCond)
		if err != nil {
			if _, isexists := err.(BreakpointExistsError); !isexists {
				return err
			}
		}
		if bp != nil {
			configureReturnBreakpoint(t.BinInfo(), bp, &topframe, retFrameCond)
		}
	}

	if bp := curthread.Breakpoint(); bp.Breakpoint == nil {
		curthread.SetCurrentBreakpoint(false)
	}

	success = true
	return t.Continue()
}

func conditionErrors(threads []Thread) error {
	var condErr error
	for _, th := range threads {
		if bp := th.Breakpoint(); bp.Breakpoint != nil && bp.CondError != nil {
			if condErr == nil {
				condErr = bp.CondError
			} else {
				return fmt.Errorf("multiple errors evaluating conditions")
			}
		}
	}
	return condErr
}

// pick a new dbp.currentThread, with the following priority:
// 	- a thread with onTriggeredInternalBreakpoint() == true
// 	- a thread with onTriggeredBreakpoint() == true (prioritizing trapthread)
// 	- trapthread
func pickCurrentThread(dbp Process, trapthread Thread, threads []Thread) error {
	for _, th := range threads {
		if bp := th.Breakpoint(); bp.Active && bp.Internal {
			return dbp.SwitchThread(th.ThreadID())
		}
	}
	if bp := trapthread.Breakpoint(); bp.Active {
		return dbp.SwitchThread(trapthread.ThreadID())
	}
	for _, th := range threads {
		if bp := th.Breakpoint(); bp.Active {
			return dbp.SwitchThread(th.ThreadID())
		}
	}
	return dbp.SwitchThread(trapthread.ThreadID())
}

// stepInstructionOut repeatedly calls StepInstruction until the current
// function is neither fnname1 or fnname2.
// This function is used to step out of runtime.Breakpoint as well as
// runtime.debugCallV1.
func stepInstructionOut(dbp Process, curthread Thread, fnname1, fnname2 string) error {
	for {
		if err := curthread.StepInstruction(); err != nil {
			return err
		}
		loc, err := curthread.Location()
		if err != nil || loc.Fn == nil || (loc.Fn.Name != fnname1 && loc.Fn.Name != fnname2) {
			g, _ := GetG(curthread)
			selg := dbp.SelectedGoroutine()
			if g != nil && selg != nil && g.ID == selg.ID {
				selg.CurrentLoc = *loc
			}
			return curthread.SetCurrentBreakpoint(true)
		}
	}
}

// Set breakpoints at every line, and the return address. Also look for
// a deferred function and set a breakpoint there too.
// If stepInto is enabled it will also set breakpoints inside all
// functions called on the current source line, for non-absolute CALLs
// a breakpoint of kind StepBreakpoint is set on the CALL instruction,
// Continue will take care of setting a breakpoint to the destination
// once the CALL is reached.
//
// Regardless of stepInto the following breakpoints will be set:
// - a breakpoint on the first deferred function with NextDeferBreakpoint
//   kind, the list of all the addresses to deferreturn calls in this function
//   and condition checking that we remain on the same goroutine
// - a breakpoint on each line of the function, with a condition checking
//   that we stay on the same stack frame and goroutine.
// - a breakpoint on the return address of the function, with a condition
//   checking that we move to the previous stack frame and stay on the same
//   goroutine.
//
// The breakpoint on the return address is *not* set if the current frame is
// an inlined call. For inlined calls topframe.Current.Fn is the function
// where the inlining happened and the second set of breakpoints will also
// cover the "return address".
//
// If inlinedStepOut is enabled this function implements the StepOut operation
// for an inlined function call. Everything works the same as normal except
// when removing instructions belonging to inlined calls we also remove all
// instructions belonging to the current inlined call.
func next(dbp Process, opts uint64) error {
	var (
		selg           = dbp.SelectedGoroutine()
		curthread      = dbp.CurrentThread()
		stepInto       = (opts & optStepInto) != 0
		inlinedStepOut = (opts & optInlineStepout) != 0
	)

	topframe, retframe, err := topframe(selg, curthread)
	if err != nil {
		return err
	}

	if topframe.Current.Fn == nil {
		return &ErrNoSourceForPC{topframe.Current.PC}
	}

	// sanity check
	if inlinedStepOut && !topframe.Inlined {
		panic("next called with inlinedStepOut but topframe was not inlined")
	}

	success := false
	defer func() {
		if !success {
			dbp.ClearInternalBreakpoints()
		}
	}()

	ext := filepath.Ext(topframe.Current.File)
	csource := ext != ".go" && ext != ".s"
	var thread MemoryReadWriter = curthread
	var regs Registers
	if selg != nil && selg.Thread != nil {
		thread = selg.Thread
		regs, err = selg.Thread.Registers(false)
		if err != nil {
			return err
		}
	}

	text, err := disassemble(thread, regs, dbp.Breakpoints(), dbp.BinInfo(), topframe.Current.Fn.Entry, topframe.Current.Fn.End, false)
	if err != nil && stepInto {
		return err
	}

	sameGCond := SameGoroutineCondition(selg)
	retFrameCond := andFrameoffCondition(sameGCond, retframe.FrameOffset())
	sameFrameCond := andFrameoffCondition(sameGCond, topframe.FrameOffset())
	var sameOrRetFrameCond ast.Expr
	if sameGCond != nil {
		if topframe.Inlined {
			sameOrRetFrameCond = sameFrameCond
		} else {
			sameOrRetFrameCond = &ast.BinaryExpr{
				Op: token.LAND,
				X:  sameGCond,
				Y: &ast.BinaryExpr{
					Op: token.LOR,
					X:  frameoffCondition(topframe.FrameOffset()),
					Y:  frameoffCondition(retframe.FrameOffset()),
				},
			}
		}
	}

	if stepInto {
		for _, instr := range text {
			if instr.Loc.File != topframe.Current.File || instr.Loc.Line != topframe.Current.Line || !instr.IsCall() {
				continue
			}

			if instr.DestLoc != nil && instr.DestLoc.Fn != nil {
				if err := setStepIntoBreakpoint(dbp, []AsmInstruction{instr}, sameGCond); err != nil {
					return err
				}
			} else {
				// Non-absolute call instruction, set a StepBreakpoint here
				if _, err := dbp.SetBreakpoint(instr.Loc.PC, StepBreakpoint, sameGCond); err != nil {
					if _, ok := err.(BreakpointExistsError); !ok {
						return err
					}
				}
			}
		}
	}

	if !csource {
		deferreturns := FindDeferReturnCalls(text)

		// Set breakpoint on the most recently deferred function (if any)
		var deferpc uint64
		if topframe.TopmostDefer != nil && topframe.TopmostDefer.DeferredPC != 0 {
			deferfn := dbp.BinInfo().PCToFunc(topframe.TopmostDefer.DeferredPC)
			var err error
			deferpc, err = FirstPCAfterPrologue(dbp, deferfn, false)
			if err != nil {
				return err
			}
		}
		if deferpc != 0 && deferpc != topframe.Current.PC {
			bp, err := dbp.SetBreakpoint(deferpc, NextDeferBreakpoint, sameGCond)
			if err != nil {
				if _, ok := err.(BreakpointExistsError); !ok {
					return err
				}
			}
			if bp != nil && stepInto {
				bp.DeferReturns = deferreturns
			}
		}
	}

	// Add breakpoints on all the lines in the current function
	pcs, err := topframe.Current.Fn.cu.lineInfo.AllPCsBetween(topframe.Current.Fn.Entry, topframe.Current.Fn.End-1, topframe.Current.File, topframe.Current.Line)
	if err != nil {
		return err
	}

	if !stepInto {
		// Removing any PC range belonging to an inlined call
		frame := topframe
		if inlinedStepOut {
			frame = retframe
		}
		pcs, err = removeInlinedCalls(dbp, pcs, frame)
		if err != nil {
			return err
		}
	}

	if !csource {
		var covered bool
		for i := range pcs {
			if topframe.Current.Fn.Entry <= pcs[i] && pcs[i] < topframe.Current.Fn.End {
				covered = true
				break
			}
		}

		if !covered {
			fn := dbp.BinInfo().PCToFunc(topframe.Ret)
			if selg != nil && fn != nil && fn.Name == "runtime.goexit" {
				return nil
			}
		}
	}

	for _, pc := range pcs {
		if _, err := dbp.SetBreakpoint(pc, NextBreakpoint, sameFrameCond); err != nil {
			if _, ok := err.(BreakpointExistsError); !ok {
				dbp.ClearInternalBreakpoints()
				return err
			}
		}

	}
	if !topframe.Inlined {
		// Add a breakpoint on the return address for the current frame.
		// For inlined functions there is no need to do this, the set of PCs
		// returned by the AllPCsBetween call above already cover all instructions
		// of the containing function.
		bp, err := dbp.SetBreakpoint(topframe.Ret, NextBreakpoint, retFrameCond)
		if err != nil {
			if _, isexists := err.(BreakpointExistsError); isexists {
				if bp.Kind == NextBreakpoint {
					// If the return address shares the same address with one of the lines
					// of the function (because we are stepping through a recursive
					// function) then the corresponding breakpoint should be active both on
					// this frame and on the return frame.
					bp.Cond = sameOrRetFrameCond
				}
			}
			// Return address could be wrong, if we are unable to set a breakpoint
			// there it's ok.
		}
		if bp != nil {
			configureReturnBreakpoint(dbp.BinInfo(), bp, &topframe, retFrameCond)
		}
	}

	if bp := curthread.Breakpoint(); bp.Breakpoint == nil {
		curthread.SetCurrentBreakpoint(false)
	}
	success = true
	return nil
}

// Removes instructions belonging to inlined calls of topframe from pcs.
// If includeCurrentFn is true it will also remove all instructions
// belonging to the current function.
func removeInlinedCalls(dbp Process, pcs []uint64, topframe Stackframe) ([]uint64, error) {
	image := topframe.Call.Fn.cu.image
	dwarf := image.dwarf
	irdr := reader.InlineStack(dwarf, topframe.Call.Fn.offset, 0)
	for irdr.Next() {
		e := irdr.Entry()
		if e.Offset == topframe.Call.Fn.offset {
			continue
		}
		ranges, err := dwarf.Ranges(e)
		if err != nil {
			return pcs, err
		}
		for _, rng := range ranges {
			pcs = removePCsBetween(pcs, rng[0], rng[1], image.StaticBase)
		}
		irdr.SkipChildren()
	}
	return pcs, irdr.Err()
}

func removePCsBetween(pcs []uint64, start, end, staticBase uint64) []uint64 {
	out := pcs[:0]
	for _, pc := range pcs {
		if pc < start+staticBase || pc >= end+staticBase {
			out = append(out, pc)
		}
	}
	return out
}

func setStepIntoBreakpoint(dbp Process, text []AsmInstruction, cond ast.Expr) error {
	if len(text) <= 0 {
		return nil
	}

	instr := text[0]

	if instr.DestLoc == nil {
		// Call destination couldn't be resolved because this was not the
		// current instruction, therefore the step-into breakpoint can not be set.
		return nil
	}

	fn := instr.DestLoc.Fn

	// Skip unexported runtime functions
	if fn != nil && strings.HasPrefix(fn.Name, "runtime.") && !isExportedRuntime(fn.Name) {
		return nil
	}

	//TODO(aarzilli): if we want to let users hide functions
	// or entire packages from being stepped into with 'step'
	// those extra checks should be done here.

	pc := instr.DestLoc.PC

	// We want to skip the function prologue but we should only do it if the
	// destination address of the CALL instruction is the entry point of the
	// function.
	// Calls to runtime.duffzero and duffcopy inserted by the compiler can
	// sometimes point inside the body of those functions, well after the
	// prologue.
	if fn != nil && fn.Entry == instr.DestLoc.PC {
		pc, _ = FirstPCAfterPrologue(dbp, fn, false)
	}

	// Set a breakpoint after the function's prologue
	if _, err := dbp.SetBreakpoint(pc, NextBreakpoint, cond); err != nil {
		if _, ok := err.(BreakpointExistsError); !ok {
			return err
		}
	}

	return nil
}

// SupportsFunctionCalls returns whether or not the backend supports
// calling functions during a debug session.
// Currently only non-recorded processes running on AMD64 support
// function calls.
func (t *Target) SupportsFunctionCalls() bool {
	if ok, _ := t.Process.Recorded(); ok {
		return false
	}
	_, ok := t.Process.BinInfo().Arch.(*AMD64)
	return ok
}

// ClearAllGCache clears the internal Goroutine cache.
// This should be called anytime the target process executes instructions.
func (t *Target) ClearAllGCache() {
	t.gcache.Clear()
}

func (t *Target) Restart(from string) error {
	t.ClearAllGCache()
	return t.Process.Restart(from)
}

func (t *Target) Detach(kill bool) error {
	if !kill && t.asyncPreemptChanged {
		setAsyncPreemptOff(t, t.asyncPreemptOff)
	}
	return t.Process.Detach(kill)
}
