import VFiveSixContactOrbit

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



/-- At the unique crossing the two actual chart vertices supply opposite
signed coefficients, after ignoring auxiliary torsion-disc letters. -/
theorem crossing_opposite_coefficients
    (two : Nat.card (SixGapComponent g) = 2)
    (r : Subtype g.joinedHitsGap) (hr : sixCrossComponentRegion g r)
    (x y : g.Gap) (xr : g.joined x.val = r.val) (yr : g.joined y.val = r.val)
    (diff : sixGapComponent g x ≠ sixGapComponent g y) :
    orbitResidue t s ds g x = - orbitResidue t s ds g y := by
  classical
  obtain ⟨a,b,_,exactly⟩ := two_components_crossing_has_two_orbits g two hr
  let X := rep g.GapVertexPerm x
  let Y := rep g.GapVertexPerm y
  have xy : X ≠ Y := fun eq => diff (congrArg (sixGapVertexComponent g) eq)
  have Xr : g.gapVertexJoined X = r := Subtype.ext xr
  have Yr : g.gapVertexJoined Y = r := Subtype.ext yr
  have cover (z : Orbits g.GapVertexPerm) (h : g.gapVertexJoined z = r) :
      z = X ∨ z = Y := by
    rcases (exactly X).mp Xr with hx|hx <;>
      rcases (exactly Y).mp Yr with hy|hy
    · exact (xy (hx.trans hy.symm)).elim
    · simpa only [hx,hy] using (exactly z).mp h
    · simpa only [hx,hy,or_comm] using (exactly z).mp h
    · exact (xy (hx.trans hy.symm)).elim
  let sites := sixNonauxDarts t s ds g
  let A := sites.filter (fun d => rep g.chartVertexPerm d = rep g.chartVertexPerm x.val)
  let B := sites.filter (fun d => rep g.chartVertexPerm d = rep g.chartVertexPerm y.val)
  have partition : sites.filter (fun d => g.joined d = r.val) = A ∪ B := by
    ext d
    simp only [A,B,Finset.mem_union,Finset.mem_filter]
    constructor
    · rintro ⟨hd,hc⟩
      obtain ⟨z,cyc⟩ := six_chart_vertex_hits_of_main t s ds g d
        (six_nonaux_is_main t s ds g d (Finset.mem_filter.mp hd).2)
      have zd := congrArg g.chartVertexJoined (Quotient.sound cyc)
      have zs : g.gapVertexJoined (rep g.GapVertexPerm z) = r := Subtype.ext (zd.trans hc)
      rcases cover _ zs with zx|zy
      · exact Or.inl ⟨hd,(Quotient.sound cyc).symm.trans (congrArg g.gapVertexToChart zx)⟩
      · exact Or.inr ⟨hd,(Quotient.sound cyc).symm.trans (congrArg g.gapVertexToChart zy)⟩
    · rintro (⟨hd,xd⟩|⟨hd,yd⟩)
      · exact ⟨hd,(congrArg g.chartVertexJoined xd).trans xr⟩
      · exact ⟨hd,(congrArg g.chartVertexJoined yd).trans yr⟩
  have disj : Disjoint A B := Finset.disjoint_left.mpr (by
    intro d hd he
    exact xy (g.gapVertexToChart_injective
      ((Finset.mem_filter.mp hd).2.symm.trans (Finset.mem_filter.mp he).2)))
  have zero := nonaux_joined_residue_zero t s ds g r.val
  change (∑ d ∈ sites.filter (fun d => g.joined d = r.val), (g.signed d : ZMod 5)) = 0 at zero
  rw [partition,Finset.sum_union disj] at zero
  exact eq_neg_iff_add_eq_zero.mpr zero

open Lean in
run_cmd do
  unless (← Lean.collectAxioms ``crossing_opposite_coefficients).all
    (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
    throwError "Unexpected axiom for opposite contact weights"

#print axioms crossing_opposite_coefficients
end
end AK3.SubVPicture.RingGeneralSix
