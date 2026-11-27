import VFiveSixPairCensus
import VFiveSixPairOrder

namespace AK3.SubVPicture.RingGeneralSix
open Equiv AK3.SSeven AK3.SSeven.Relative AK3.SSeven.FreeCap
open AK3.SSeven.FreeCap.CapSchedule AK3.SSeven.FreeCap.SewnCount
open AK3.SSeven.FreeCap.BandOverlay AK3.SSeven.FreeCap.BandDeletion
open AK3.SSeven.FreeCap.SlotPrune AK3.SSeven.FreeCap.Switch
open AK3.SSeven.Endpoint.Weighted AK3.SSeven.Endpoint.Weighted.VFiveBoundary
open AK3.CoefficientDiagram AK3.SSeven.Curvature AK3.SubVPicture.Literal
open AK3.SubVPicture.RingPrefix (atCorner)
open AK3.SSeven.FreeCap.ScaffoldBands
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32000
noncomputable section


def digonMismatch (u v : Tape) (phase : Nat) : Nat :=
  (List.range u.length).countP (fun j =>
    let a := atCorner u j
    let b := atCorner v ((phase + u.length - j) % u.length)
    (a.2 + b.2) % 5 != 0)
def digonWrongFactor (u v : Tape) (phase : Nat) : Bool :=
  (List.range u.length).any (fun j =>
    (atCorner u j).1 != (atCorner v ((phase + u.length - j) % u.length)).1)

private def candidateA : FaceTriple := ((1,true),(4,false),(4,false))
private def candidateB : FaceTriple := ((2,false),(5,false),(6,true))

/-- Checked numerical minima over compatible reverse alignments. These
are tests on literal tapes, not a transport theorem for actual diagrams. -/
theorem survivorA_reverse_min :
    let u := sixTapeAt candidateA 4
    let v := sixTapeAt candidateA 5
    (((List.range u.length).filter (fun j => !digonWrongFactor u v j)).all
      (fun j => decide (10 ≤ digonMismatch u v j))) = true ∧
    digonWrongFactor u v 12 = false ∧ digonMismatch u v 12 = 10 := by decide +kernel

theorem survivorB_reverse_min :
    let u := sixTapeAt candidateB 3
    let v := sixTapeAt candidateB 5
    (((List.range u.length).filter (fun j => !digonWrongFactor u v j)).all
      (fun j => decide (22 ≤ digonMismatch u v j))) = true ∧
    digonWrongFactor u v 9 = false ∧ digonMismatch u v 9 = 22 := by decide +kernel

open Lean in
run_cmd do
  for n in [``survivorA_reverse_min,``survivorB_reverse_min] do
    unless (← Lean.collectAxioms n).all
      (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "Unexpected axiom in reverse tape test"
#print axioms survivorA_reverse_min
#print axioms survivorB_reverse_min
end
end AK3.SubVPicture.RingGeneralSix
