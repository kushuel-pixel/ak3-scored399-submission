import VFiveSixSplitTable
import VFiveSixComponentAnchor

namespace AK3.SubVPicture.RingGeneralSix
open Equiv AK3.SSeven AK3.SSeven.Relative AK3.SSeven.FreeCap
open AK3.SSeven.FreeCap.CapSchedule AK3.SSeven.FreeCap.SewnCount
open AK3.SSeven.FreeCap.BandOverlay AK3.SSeven.FreeCap.BandDeletion
open AK3.SSeven.FreeCap.SlotPrune AK3.SSeven.FreeCap.Switch
open AK3.SSeven.Endpoint.Weighted AK3.SSeven.Endpoint.Weighted.VFiveBoundary
open AK3.CoefficientDiagram AK3.SSeven.Curvature AK3.SubVPicture.Literal
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32000
noncomputable section
variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)

def exceptionalNegative (t : FaceTriple) (m : Nat) : Prop :=
  (t = ((0,false),(2,true),(3,false)) ∧ m = 44) ∨
  ((t = ((2,true),(3,true),(5,false)) ∨ t = ((2,true),(4,false),(5,true))) ∧ m = 52)

private theorem negative_mask_table (t : FaceTriple) (H : t ∈ coefficientTriples)
    (m : Fin 64) (hm : m.val ∈ sparseProperMasks t) (on : m.val.testBit 2 = true) :
    m.val = 5 ∨ m.val = 6 ∨ exceptionalNegative t m.val := by
  rw [← roster_binding] at H
  simp only [certifiedTriples,List.mem_cons,List.not_mem_nil,or_false] at H
  rcases H with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    unfold exceptionalNegative <;> revert m <;> decide +kernel

/-- If the component containing the negative anchor is separated in
both coefficient factors, only the three exceptional types are possible. -/
theorem negative_component_only_exceptional_if_closed (H : t ∈ coefficientTriples)
    (split : 2 ≤ Nat.card (SixGapComponent g))
    (closed : ∀ f : Fin 2, regionClosedInFactor t s ds g
      (sixGapComponent g (rowGap t s ds g 2)) f) :
    exceptionalNegative t (componentMask t s ds g
      (sixGapComponent g (rowGap t s ds g 2))).val := by
  let c := sixGapComponent g (rowGap t s ds g 2)
  let m := componentMask t s ds g c
  have on : m.val.testBit 2 = true := (componentMask_spec t s ds g c 2).mpr rfl
  have ok := region_closed_component_classified t s ds g H c split closed
  have excluded := anchor_component_mask_excluded t s ds g H c
  rcases negative_mask_table t H m ok on with five | six | remaining
  · exact (excluded.1 five).elim
  · exact (excluded.2 six).elim
  · exact remaining

open Lean in
run_cmd do
  unless (← Lean.collectAxioms ``negative_component_only_exceptional_if_closed).all
    (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
    throwError "Unexpected axiom in negative anchor classification"
#print axioms negative_component_only_exceptional_if_closed
end
end AK3.SubVPicture.RingGeneralSix
