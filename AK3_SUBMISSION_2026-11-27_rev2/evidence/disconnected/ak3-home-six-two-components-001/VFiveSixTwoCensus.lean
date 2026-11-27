import VFiveSixTwoMixed

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
/-- Proper negative-anchor masks, omitting masks 5 and 6 already
excluded geometrically, evaluated in one coefficient factor at a time. -/
def negativeFactorMasks (t : FaceTriple) (f : Fin 2) : List Nat :=
  ((List.range 62).map (· + 1)).filter fun m =>
    m.testBit 2 && m != 5 && m != 6 &&
      decide (coordinate (selectedCharge (chartCharges t) m) f = 0)

/-- Kernel-checked exact table in certifiedTriples order (factor 0, factor 1). -/
theorem two_component_factor_table :
    certifiedTriples.map (fun t => (negativeFactorMasks t 0, negativeFactorMasks t 1)) =
    [([20,31,37,38,52],[15,23,36,45,46,53,54]),
     ([29,30,39,52],[15,28,53,54]),
     ([28,44,52],[15,44,53,54]),
     ([20,36],[12,23,29,30,39,45,46]),
     ([15,23,36,45,46,53,54],[12,20]),
     ([15,44,53,54],[12,36]),
     ([15,21,22,31,37,38,47,53,54],[12,23,29,30,39,45,46]),
     ([31,37,38],[29,30,39,44]),
     ([21,22,47],[20,36]),
     ([23,28,45,46],[29,30,39,44]),
     ([29,30,39,52],[28,44,52]),
     ([21,22,36,47,52],[23,45,46,52])] := by decide +kernel

/-- Count distinct masks per signed type, not separately per factor. -/
theorem two_component_candidate_count :
    (certifiedTriples.map (fun t =>
      ((negativeFactorMasks t 0 ++ negativeFactorMasks t 1).eraseDups).length)).sum = 100 := by
  decide +kernel

variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)


/-- The mask of the actual negative-anchor component passes the one-factor
census whenever the literal diagram has exactly two components. -/
theorem two_component_negative_mask_in_census (H : t ∈ coefficientTriples)
    (two : Nat.card (SixGapComponent g) = 2) :
    ∃ f : Fin 2, (componentMask t s ds g
      (sixGapComponent g (rowGap t s ds g 2))).val ∈ negativeFactorMasks t f := by
  obtain ⟨f,closed⟩ := two_components_have_closed_factor t s ds g two
  let c := sixGapComponent g (rowGap t s ds g 2)
  let m := (componentMask t s ds g c).val
  have zero := (chart_mask_coordinate t s ds g H c f).trans
    (componentFactorSum_zero t s ds g c f (closed c))
  have bounds := componentMask_proper t s ds g c (by omega)
  have on := (componentMask_spec t s ds g c 2).mpr rfl
  have no := anchor_component_mask_excluded t s ds g H c
  refine ⟨f,List.mem_filter.mpr ⟨?_,?_⟩⟩
  · apply List.mem_map.mpr
    refine ⟨m-1,List.mem_range.mpr ?_,?_⟩
    · change 0 < m ∧ m < 63 at bounds
      omega
    · change m-1+1 = m
      change 0 < m ∧ m < 63 at bounds
      omega
  · change m.testBit 2 && m != 5 && m != 6 &&
      decide (coordinate (selectedCharge (chartCharges t) m) f = 0) = true
    change m.testBit 2 = true at on
    change coordinate (selectedCharge (chartCharges t) m) f = 0 at zero
    have no5 : m ≠ 5 := no.1
    have no6 : m ≠ 6 := no.2
    simp [on,zero,no5,no6]

open Lean in
run_cmd do
  for n in [``two_component_factor_table, ``two_component_candidate_count,
      ``two_component_negative_mask_in_census] do
    unless (← Lean.collectAxioms n).all
      (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "Unexpected axiom in the literal mask census: {n}"

#print axioms two_component_factor_table
#print axioms two_component_candidate_count
#print axioms two_component_negative_mask_in_census
end
end AK3.SubVPicture.RingGeneralSix
