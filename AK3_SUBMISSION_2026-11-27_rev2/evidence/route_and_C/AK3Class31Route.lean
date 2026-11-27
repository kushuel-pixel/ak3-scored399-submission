import Verify.AtomicSemantics
import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms

/-! Exact 187-step class (3,1) route, ac-r2-v1. Git input is
`ak3-class31-entry/endpoint_moves.json` in checkpoint 3907077dfec23739ada721bddb964cd7bcc57d20.
Fixture SHA-256 7bed96dff38fb8754307dd737b4692a22f3cfa53387debd0ba3cf8a2acb554f2. -/

namespace AK3.Class31Route

open Verify.AtomicSemantics Verify.ReducedWords

def S : WordState := ([XLetter, yLetter, yLetter, yLetter, xLetter, YLetter, YLetter, YLetter, YLetter], [xLetter, xLetter, YLetter, YLetter, YLetter, YLetter, YLetter, XLetter, yLetter, yLetter, yLetter, yLetter, yLetter])
def q : Word := [xLetter, xLetter, YLetter, XLetter, yLetter]
def Q : WordState := ([XLetter, yLetter, yLetter, yLetter, xLetter, YLetter, YLetter, YLetter, YLetter], q)
def E3 : WordState := ([XLetter, yLetter, yLetter, yLetter, xLetter, YLetter, YLetter, YLetter, YLetter], [xLetter, xLetter, YLetter, YLetter, YLetter, YLetter, XLetter, yLetter, yLetter, yLetter, yLetter])
private def s1 : WordState := ([yLetter, yLetter, yLetter, xLetter, yLetter, xLetter, YLetter, XLetter, XLetter, YLetter, YLetter, xLetter], [xLetter, xLetter, YLetter, XLetter, yLetter])
private def s2 : WordState := ([xLetter, yLetter, yLetter, xLetter, YLetter, XLetter, XLetter, YLetter, YLetter, YLetter, XLetter, yLetter], [xLetter, xLetter, YLetter, XLetter, yLetter])
private def s3 : WordState := ([xLetter, yLetter, XLetter, yLetter, XLetter, YLetter, YLetter, xLetter, yLetter, yLetter, xLetter, YLetter], [xLetter, xLetter, YLetter, XLetter, yLetter])
private def s4 : WordState := ([yLetter, XLetter, XLetter, XLetter, YLetter, XLetter, yLetter, xLetter, YLetter, xLetter, YLetter, XLetter], [xLetter, xLetter, YLetter, XLetter, yLetter])
private def s5 : WordState := ([YLetter, xLetter, YLetter, YLetter, XLetter, yLetter, yLetter, XLetter, XLetter], [xLetter, xLetter, YLetter, XLetter, yLetter])
private def s6 : WordState := ([YLetter], [XLetter, YLetter])
private def s7 : WordState := ([yLetter, yLetter, yLetter, xLetter, YLetter, YLetter, YLetter, YLetter, XLetter], [XLetter, YLetter])

private def w0 : List Move := [.m0, .m9, .m9, .m9, .m9, .m6, .m2, .m0, .m8, .m7, .m9, .m6, .m2, .m0, .m8, .m7, .m9, .m6, .m2, .m8, .m6, .m8, .m8, .m7]
private theorem step0 : wordRun w0 Q = s1 := by decide +kernel
private theorem group0 : groupRun w0 (evalState Q) = evalState s1 :=
  (eval_wordRun w0 Q).symm.trans (congrArg evalState step0)

private def w1 : List Move := [.m9, .m9, .m9, .m7, .m9, .m7, .m8, .m6, .m6, .m2, .m0, .m8, .m7, .m9, .m9, .m6, .m2, .m8, .m6, .m8, .m8, .m8, .m6, .m9]
private theorem step1 : wordRun w1 s1 = s2 := by decide +kernel
private theorem group1 : groupRun w1 (evalState s1) = evalState s2 :=
  (eval_wordRun w1 s1).symm.trans (congrArg evalState step1)

private def w2 : List Move := [.m7, .m9, .m9, .m7, .m8, .m6, .m6, .m8, .m8, .m8, .m6, .m9, .m1, .m2, .m1, .m7, .m9, .m9, .m7, .m8, .m6, .m2, .m0, .m8]
private theorem step2 : wordRun w2 s2 = s3 := by decide +kernel
private theorem group2 : groupRun w2 (evalState s2) = evalState s3 :=
  (eval_wordRun w2 s2).symm.trans (congrArg evalState step2)

private def w3 : List Move := [.m7, .m9, .m6, .m9, .m6, .m8, .m2, .m0, .m8, .m7, .m9, .m6, .m1, .m12, .m2, .m13, .m1, .m6, .m9, .m7, .m8, .m7, .m8, .m6]
private theorem step3 : wordRun w3 s3 = s4 := by decide +kernel
private theorem group3 : groupRun w3 (evalState s3) = evalState s4 :=
  (eval_wordRun w3 s3).symm.trans (congrArg evalState step3)

private def w4 : List Move := [.m9, .m6, .m6, .m2, .m6, .m8, .m6, .m9, .m7, .m8, .m7, .m8, .m6, .m6, .m2, .m9, .m6, .m8, .m6, .m9, .m1, .m2, .m1, .m7]
private theorem step4 : wordRun w4 s4 = s5 := by decide +kernel
private theorem group4 : groupRun w4 (evalState s4) = evalState s5 :=
  (eval_wordRun w4 s4).symm.trans (congrArg evalState step4)

private def w5 : List Move := [.m8, .m7, .m8, .m8, .m6, .m9, .m9, .m6, .m6, .m2, .m8, .m7, .m8, .m8, .m6, .m2, .m8, .m7, .m1, .m12, .m11, .m13, .m4, .m10]
private theorem step5 : wordRun w5 s5 = s6 := by decide +kernel
private theorem group5 : groupRun w5 (evalState s5) = evalState s6 :=
  (eval_wordRun w5 s5).symm.trans (congrArg evalState step5)

private def w6 : List Move := [.m13, .m1, .m6, .m8, .m8, .m8, .m7, .m9, .m3, .m9, .m9, .m9, .m7, .m9, .m0, .m3, .m8, .m8, .m8, .m8, .m0, .m1, .m12, .m6]
private theorem step6 : wordRun w6 s6 = s7 := by decide +kernel
private theorem group6 : groupRun w6 (evalState s6) = evalState s7 :=
  (eval_wordRun w6 s6).symm.trans (congrArg evalState step6)

private def w7 : List Move := [.m9, .m9, .m9, .m5, .m8, .m8, .m8, .m7, .m11, .m12, .m12, .m12, .m12, .m10, .m13, .m13, .m13, .m13, .m1]
private theorem step7 : wordRun w7 s7 = E3 := by decide +kernel
private theorem group7 : groupRun w7 (evalState s7) = evalState E3 :=
  (eval_wordRun w7 s7).symm.trans (congrArg evalState step7)

def route : List Move := w0 ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6 ++ w7

theorem route_length : route.length = 187 := by decide +kernel

theorem groupRun_append (a b : List Move) (s : GroupState) :
    groupRun (a ++ b) s = groupRun b (groupRun a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons m ms ih => exact ih (groupStep m s)

theorem forward : groupRun route (evalState Q) = evalState E3 := by
  simp only [route, groupRun_append, group0, group1, group2, group3, group4, group5, group6, group7]

def undoMove : Move → Move
  | .m0 => .m0
  | .m1 => .m1
  | .m2 => .m3
  | .m3 => .m2
  | .m4 => .m5
  | .m5 => .m4
  | .m6 => .m7
  | .m7 => .m6
  | .m8 => .m9
  | .m9 => .m8
  | .m10 => .m11
  | .m11 => .m10
  | .m12 => .m13
  | .m13 => .m12

theorem undoStep (m : Move) (s : GroupState) :
    groupStep (undoMove m) (groupStep m s) = s := by
  rcases s with ⟨r, t⟩
  cases m <;> simp [undoMove, groupStep, Verify.X, Verify.Y, mul_assoc]

def undo (moves : List Move) : List Move := moves.reverse.map undoMove

theorem undoRun (m : List Move) (s : GroupState) :
    groupRun (undo m) (groupRun m s) = s := by
  induction m generalizing s with
  | nil => rfl
  | cons a t ih =>
    simp only [undo, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      groupRun_append, groupRun]
    have h := ih (groupStep a s)
    rw [undo] at h
    rw [h]
    exact undoStep a s

theorem backward : groupRun (undo route) (evalState E3) = evalState Q := by
  rw [← forward]
  exact undoRun route (evalState Q)

open Lean in
run_cmd do
  for n in [``route_length, ``forward, ``undoRun, ``backward] do
    let used ← Lean.collectAxioms n
    unless used.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError m!"Unexpected axioms: {used}"
end AK3.Class31Route
