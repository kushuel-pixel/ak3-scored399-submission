import VFiveSixPairProfile

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



def contactRowCount (m : Nat) : Nat :=
  (List.finRange 6).countP (fun i => m.testBit i.val)

def chargedPairSides (t : FaceTriple) : List (Nat × Fin 2 × ZMod 5) :=
  (noSingletonContactInputs t).filter fun e =>
    decide (contactRowCount e.1 = 2 ∨ contactRowCount e.1 = 4)

def chargedTripleSides (t : FaceTriple) : List (Nat × Fin 2 × ZMod 5) :=
  (noSingletonContactInputs t).filter fun e => decide (contactRowCount e.1 = 3)

theorem charged_pair_count : (certifiedTriples.map fun t => (chargedPairSides t).length).sum = 68 := by
  decide +kernel

theorem charged_triple_count : (certifiedTriples.map fun t => (chargedTripleSides t).length).sum = 23 := by
  decide +kernel

theorem charged_allocations_covered :
    certifiedTriples.all (fun t => (noSingletonContactInputs t).all (fun entry =>
      decide (entry ∈ chargedPairSides t ∨ entry ∈ chargedTripleSides t))) = true := by
  decide +kernel

open Lean in
run_cmd do
  for n in [``charged_pair_count,``charged_triple_count,``charged_allocations_covered] do
    unless (← Lean.collectAxioms n).all
      (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "Unexpected axiom in two-row catalogue"
#print axioms charged_allocations_covered
#print axioms charged_pair_count
#print axioms charged_triple_count
end
end AK3.SubVPicture.RingGeneralSix
