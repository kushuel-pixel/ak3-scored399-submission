import VFiveSixRowFactors

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

/-- The six rows are in literal chart order, not the order used by
the abstract coefficient equation. -/
def chartCharges (t : FaceTriple) : List Residue :=
  [vResidue,vResidue,vResidue⁻¹,(residue t.1)⁻¹,(residue t.2.1)⁻¹,(residue t.2.2)⁻¹]

def coordinate (a : Residue) (f : Fin 2) : ZMod 5 :=
  if f = 0 then (Multiplicative.toAdd a).1 else (Multiplicative.toAdd a).2

def sparseProperMasks (t : FaceTriple) : List Nat :=
  if t = ((0,false),(2,true),(3,false)) then [5,6,19,44,57,58]
  else if t = ((2,true),(3,true),(5,false)) ∨ t = ((2,true),(4,false),(5,true))
       then [5,6,11,52,57,58]
       else [5,6,57,58]

private theorem coordinate_row (t : FaceTriple) (H : t ∈ coefficientTriples) (i : Fin 6) (f : Fin 2) :
    coordinate ((chartCharges t)[i.val]'(by simp [chartCharges])) f =
      tapeFactorSum (sixTapeAt t i) f := by
  rw [← roster_binding] at H
  simp only [certifiedTriples,List.mem_cons,List.not_mem_nil,or_false] at H
  rcases H with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    fin_cases i <;> fin_cases f <;> decide +kernel

private theorem coordinate_product (f : Fin 2) (a b : Residue) :
    coordinate (a*b) f = coordinate a f + coordinate b f := by
  fin_cases f <;> rfl

private theorem coordinate_selected (t : FaceTriple) (m : Nat) (f : Fin 2) :
    coordinate (selectedCharge (chartCharges t) m) f =
      ∑ i : Fin 6, if m.testBit i.val then coordinate ((chartCharges t)[i.val]'(by simp [chartCharges])) f else 0 := by
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Finset.univ_eq_empty,Finset.sum_empty]
  change coordinate (selectedCharge (chartCharges t) m) f =
    (if m.testBit 0 then coordinate vResidue f else 0) +
    ((if m.testBit 1 then coordinate vResidue f else 0) +
    ((if m.testBit 2 then coordinate (vResidue⁻¹) f else 0) +
    ((if m.testBit 3 then coordinate (residue t.1)⁻¹ f else 0) +
    ((if m.testBit 4 then coordinate (residue t.2.1)⁻¹ f else 0) +
    ((if m.testBit 5 then coordinate (residue t.2.2)⁻¹ f else 0) + 0)))))
  have co : coordinate 1 f = 0 := by fin_cases f <;> rfl
  have ci (a : Residue) : coordinate a⁻¹ f = -(coordinate a f) := by fin_cases f <;> rfl
  change coordinate (([(vResidue,0),(vResidue,1),(vResidue⁻¹,2),
    ((residue t.1)⁻¹,3),((residue t.2.1)⁻¹,4),((residue t.2.2)⁻¹,5)].filter
      (fun z => m.testBit z.2)).map Prod.fst).prod f = _
  cases a : (m.testBit 0) <;> cases b : (m.testBit 1) <;> cases c : (m.testBit 2) <;>
    cases d : (m.testBit 3) <;> cases e : (m.testBit 4) <;> cases h : (m.testBit 5) <;>
    simp [a,b,c,d,e,h,coordinate_product,co,ci,← add_assoc]

variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)

theorem chart_mask_coordinate (H : t ∈ coefficientTriples) (c : SixGapComponent g) (f : Fin 2) :
    coordinate (selectedCharge (chartCharges t) (componentMask t s ds g c).val) f =
      componentFactorSum t s ds g c f := by
  rw [componentFactorSum_as_rows t s ds g c f,coordinate_selected]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinate_row t H]

theorem chart_neutral_table (H : t ∈ coefficientTriples) :
    properNeutral (chartCharges t) = sparseProperMasks t := by
  rw [← roster_binding] at H
  simp only [certifiedTriples,List.mem_cons,List.not_mem_nil,or_false] at H
  rcases H with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

/-- With no joined region straddling the chosen component, an actual
disconnected picture must use one of the exact checked neutral masks. -/
theorem region_closed_component_classified (H : t ∈ coefficientTriples)
    (c : SixGapComponent g) (split : 2 ≤ Nat.card (SixGapComponent g))
    (closed : ∀ f : Fin 2, regionClosedInFactor t s ds g c f) :
    (componentMask t s ds g c).val ∈ sparseProperMasks t := by
  let m := (componentMask t s ds g c).val
  let a := selectedCharge (chartCharges t) m
  have zero (f : Fin 2) : coordinate a f = 0 :=
    (chart_mask_coordinate t s ds g H c f).trans (componentFactorSum_zero t s ds g c f (closed f))
  have eq : a = 1 := by
    apply Multiplicative.toAdd.injective
    exact Prod.ext (zero 0) (zero 1)
  have ⟨pos,lt⟩ := componentMask_proper t s ds g c split
  rw [← chart_neutral_table t H]
  apply List.mem_filter.mpr
  refine ⟨?_,decide_eq_true eq⟩
  apply List.mem_map.mpr
  refine ⟨m-1,List.mem_range.mpr ?_,by omega⟩
  change m-1 < 62
  change m < 63 at lt
  omega

open Lean in
run_cmd do
  unless (← Lean.collectAxioms ``region_closed_component_classified).all
    (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
    throwError "Unexpected axiom in six-row split classification"
#print axioms region_closed_component_classified
end
end AK3.SubVPicture.RingGeneralSix
