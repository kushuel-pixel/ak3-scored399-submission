import VFiveSixPairPlanar
import VFiveSixDegreeProfile

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

variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)






private theorem pair_seed (c : SixGapComponent g) (a b : Fin 6) (ne : a ≠ b)
    (desc : ∀ x : g.Gap, sixGapComponent g x = c ↔
      gapOwner g x = a.val ∨ gapOwner g x = b.val) :
    ∃ x : g.Gap, gapOwner g x = a.val ∧ gapOwner g (g.gapMate x) = b.val := by
  classical
  by_contra! no
  let A := rowGap t s ds g a
  let B := rowGap t s ds g b
  have ha : gapOwner g A = a.val := rowGap_owner t s ds g a
  have hb : gapOwner g B = b.val := rowGap_owner t s ds g b
  have stable (x : g.Gap) (p : gapOwner g x = a.val) :
      gapOwner g (g.gapMate x) = a.val := by
    have e : sixGapComponent g x = sixGapComponent g (g.gapMate x) := Quot.sound (Or.inr rfl)
    exact ((desc _).mp (e.symm.trans ((desc x).mpr (Or.inl p)))).resolve_right (no x p)
  let label : SixGapComponent g → Bool := Quot.lift (fun x : g.Gap => decide (gapOwner g x = a.val)) (by
    intro x y h
    have agrees : gapOwner g x = a.val ↔ gapOwner g y = a.val := by
      rcases h with h | rfl
      · rw [(gapCycle_iff_owner g (literalSix_padded t s ds) _ _).mp h]
      · exact ⟨stable x,fun h => g.gap_invol x ▸ stable (g.gapMate x) h⟩
    by_cases h : gapOwner g x = a.val
    · simp [h,agrees.mp h]
    · simp [h,mt agrees.mpr h])
  have eq : sixGapComponent g A = sixGapComponent g B :=
    ((desc A).mpr (Or.inl ha)).trans ((desc B).mpr (Or.inr hb)).symm
  have e := congrArg label eq
  change decide (gapOwner g A = a.val) = decide (gapOwner g B = a.val) at e
  have d : b.val ≠ a.val := fun h => ne (Fin.ext h.symm)
  simp [ha,hb,d] at e

/-- Degree profile valid for either side of an actual 2+4 split if
the coefficient region crosses between the two components. -/
theorem actual_two_row_degree_profile (H : t ∈ coefficientTriples)
    (two : Nat.card (SixGapComponent g) = 2)
    (r : Subtype g.joinedHitsGap) (hr : sixCrossComponentRegion g r)
    (c : SixGapComponent g) (a b : Fin 6) (ne : a ≠ b)
    (desc : ∀ x : g.Gap, sixGapComponent g x = c ↔ gapOwner g x = a.val ∨ gapOwner g x = b.val) :
    let i := (a.val,b.val)
    let v := faces (pairRowRotation g i) (pairRowBands g i)
    (∀ z, vertexDegree v z = 2) ∨
      ∃ x y, vertexDegree v x = 1 ∧ vertexDegree v y = 3 ∧
        ∀ z, z ≠ x → z ≠ y → vertexDegree v z = 2 := by
  let i := (a.val,b.val)
  let v := faces (pairRowRotation g i) (pairRowBands g i)
  let D := Subtype (pairRowGap g i)
  let view := pairRowToGap g i
  have side (x : g.Gap) : pairRowGap g i x.val ↔ sixGapComponent g x = c := by
    refine ⟨fun h => (desc x).mpr h.2,fun h => ⟨x.property,(desc x).mp h⟩⟩
  have iso (x : g.Gap) : pairRowGap g i x.val ↔ pairRowGap g i (g.gapMate x).val := by
    have e : sixGapComponent g x = sixGapComponent g (g.gapMate x) := Quot.sound (Or.inr rfl)
    rw [side x,side (g.gapMate x),e]
  obtain ⟨seed,sa,sb⟩ := pair_seed t s ds g c a b ne desc
  have d : a.val ≠ b.val := fun h => ne (Fin.ext h)
  obtain ⟨euler,darts⟩ := pair_row_counts g i d (literalSix_padded t s ds) iso seed sa sb
  have balanced : Nat.card D = 2 * Nat.card (Orbits v) := darts.trans (congrArg (2 * ·) euler.symm)
  have unique (x y : D) (hx : v x = x) (hy : v y = y) : x = y := by
    have vx : g.GapVertexPerm (view x) = view x :=
      (pair_row_vertex_agrees g i (literalSix_padded t s ds) iso x).symm.trans (congrArg view hx)
    have vy : g.GapVertexPerm (view y) = view y :=
      (pair_row_vertex_agrees g i (literalSix_padded t s ds) iso y).symm.trans (congrArg view hy)
    have mx : sixGapComponent g (view x) = c := (desc _).mpr x.property.2
    have my : sixGapComponent g (view y) = c := (desc _).mpr y.property.2
    have eq := fixed_gaps_unique_in_component t s ds g H two r hr (view x) (view y)
      vx vy (mx.trans my.symm)
    exact Subtype.ext (congrArg (fun x : g.Gap => x.val) eq)
  exact permutation_degree_two_profile v balanced unique

open Lean in
run_cmd do
  unless (← Lean.collectAxioms ``actual_two_row_degree_profile).all
    (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
    throwError "Unexpected axiom in two-row topology"
#print axioms actual_two_row_degree_profile
end
end AK3.SubVPicture.RingGeneralSix
