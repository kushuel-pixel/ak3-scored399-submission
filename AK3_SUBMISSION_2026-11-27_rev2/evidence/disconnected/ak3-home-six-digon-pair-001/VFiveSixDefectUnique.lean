import VFiveSixPairOrder
import VFiveSixPairProfile

namespace AK3.SubVPicture.RingGeneralSix
open Equiv AK3.SSeven AK3.SSeven.Relative AK3.SSeven.FreeCap
open AK3.SSeven.FreeCap.CapSchedule AK3.SSeven.FreeCap.SewnCount
open AK3.SSeven.FreeCap.BandOverlay AK3.SSeven.FreeCap.BandDeletion
open AK3.SSeven.FreeCap.SlotPrune AK3.SSeven.FreeCap.Switch
open AK3.SSeven.Endpoint.Weighted AK3.SSeven.Endpoint.Weighted.VFiveBoundary
open AK3.CoefficientDiagram AK3.SSeven.Curvature AK3.SubVPicture.Literal
open AK3.SubVPicture.RingPrefix (atCorner)
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





theorem nonzero_gap_orbit_is_shared (x : g.Gap)
    (nz : orbitResidue t s ds g x ≠ 0) :
    sharedFiber g.gapVertexJoined (rep g.GapVertexPerm x) := by
  classical
  by_contra off
  let S := sixNonauxDarts t s ds g
  have eq : S.filter (fun d => g.joined d = g.joined x.val) =
      S.filter (fun d => rep g.chartVertexPerm d = rep g.chartVertexPerm x.val) := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd,h⟩
      exact ⟨hd,Quotient.sound ((nonaux_same_chart_of_single_gap t s ds g x off hd h).symm)⟩
    · rintro ⟨hd,h⟩
      exact ⟨hd,congrArg g.chartVertexJoined h⟩
  have zero := nonaux_joined_residue_zero t s ds g (g.joined x.val)
  change (∑ d ∈ S.filter (fun d => g.joined d = g.joined x.val), (g.signed d : ZMod 5)) = 0 at zero
  rw [eq] at zero
  change orbitResidue t s ds g x = 0 at zero
  exact nz zero

/-- Only one orbit of nonzero residue is allowed on either component
at a crossing. There is no degree assumption here. -/
theorem nonzero_orbits_unique_in_component
    (two : Nat.card (SixGapComponent g) = 2)
    (r : Subtype g.joinedHitsGap) (hr : sixCrossComponentRegion g r)
    (x y : g.Gap) (nx : orbitResidue t s ds g x ≠ 0) (ny : orbitResidue t s ds g y ≠ 0)
    (same : sixGapComponent g x = sixGapComponent g y) :
    rep g.GapVertexPerm x = rep g.GapVertexPerm y := by
  obtain ⟨a,b,_,_,diff,exactly⟩ := two_components_crossing_spends_budget g two hr
  have hx := (exactly _).mp (nonzero_gap_orbit_is_shared t s ds g x nx)
  have hy := (exactly _).mp (nonzero_gap_orbit_is_shared t s ds g y ny)
  rcases hx with hx|hx <;> rcases hy with hy|hy
  · exact hx.trans hy.symm
  · exact (diff ((congrArg (sixGapVertexComponent g) hx).symm.trans
      (same.trans (congrArg (sixGapVertexComponent g) hy)))).elim
  · exact (diff ((congrArg (sixGapVertexComponent g) hy).symm.trans
      (same.symm.trans (congrArg (sixGapVertexComponent g) hx)))).elim
  · exact hx.trans hy.symm

/-- The residual test for a degree-two vertex is exactly the sum of the
two literal coefficients, not a sum over a larger joined region. -/
theorem digon_residue_two_corners (H : t ∈ coefficientTriples) (x : g.Gap)
    (twice : g.GapVertexPerm (g.GapVertexPerm x) = x) (notfixed : g.GapVertexPerm x ≠ x) :
    orbitResidue t s ds g x =
      ((atCorner (sixTapeAt t (cornerRow t s ds g x)) (cornerTag t s ds g x)).2 : ZMod 5) +
      ((atCorner (sixTapeAt t (cornerRow t s ds g (g.GapVertexPerm x)))
         (cornerTag t s ds g (g.GapVertexPerm x))).2 : ZMod 5) := by
  classical
  let v := g.GapVertexPerm
  let O := {y : g.Gap // v.SameCycle x y}
  let a : O := ⟨x,Perm.SameCycle.refl v x⟩
  let b : O := ⟨v x,(Perm.SameCycle.refl v x).apply_right⟩
  have ab : a ≠ b := fun h => notfixed (congrArg Subtype.val h).symm
  have cover : (Finset.univ : Finset O) = {a,b} := by
    ext z
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
    obtain ⟨k,eq⟩ := z.property
    rcases Perm.zpow_apply_eq_of_apply_apply_eq_self twice k with l|r
    · exact Or.inl (Subtype.ext (eq.symm.trans l))
    · exact Or.inr (Subtype.ext (eq.symm.trans r))
  rw [orbitResidue_eq_literal_sum t s ds g H x]
  change (∑ y ∈ (Finset.univ : Finset O), _) = _
  rw [cover,Finset.sum_insert (by simpa using ab),Finset.sum_singleton]

open Lean in
run_cmd do
  for n in [``nonzero_orbits_unique_in_component,``digon_residue_two_corners] do
    unless (← Lean.collectAxioms n).all
      (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "Unexpected axiom in nonzero orbit uniqueness"
#print axioms nonzero_orbits_unique_in_component
#print axioms digon_residue_two_corners
end
end AK3.SubVPicture.RingGeneralSix
