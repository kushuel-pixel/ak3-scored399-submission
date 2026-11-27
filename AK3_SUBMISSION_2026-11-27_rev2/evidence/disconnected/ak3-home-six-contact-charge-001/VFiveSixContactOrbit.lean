import VFiveSixContactCharge

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


/-- Non-auxiliary coefficient at one actual chart vertex. -/
def orbitResidue (x : g.Gap) : ZMod 5 := by
  classical
  exact ∑ d ∈ (sixNonauxDarts t s ds g).filter
    (fun d => rep g.chartVertexPerm d = rep g.chartVertexPerm x.val), (g.signed d : ZMod 5)

theorem crossing_residue_on_one_orbit
    (two : Nat.card (SixGapComponent g) = 2)
    (r : Subtype g.joinedHitsGap) (hr : sixCrossComponentRegion g r)
    (x : g.Gap) (atR : g.joined x.val = r.val) :
    contactResidue t s ds g (sixGapComponent g x) r.val = orbitResidue t s ds g x := by
  classical
  obtain ⟨a,b,ab,exactly⟩ := two_components_crossing_has_two_orbits g two hr
  have unique (z w : Orbits g.GapVertexPerm) (hz : g.gapVertexJoined z = r)
      (hw : g.gapVertexJoined w = r)
      (same : sixGapVertexComponent g z = sixGapVertexComponent g w) : z = w := by
    rcases (exactly z).mp hz with rfl|rfl <;>
      rcases (exactly w).mp hw with rfl|rfl
    · rfl
    · exact (ab same).elim
    · exact (ab same.symm).elim
    · rfl
  let c := sixGapComponent g x
  change (∑ d ∈ ((sixNonauxDarts t s ds g).filter
    (fun d => chosenDart t s ds g c d = true)).filter (fun d => g.joined d = r.val),
    (g.signed d : ZMod 5)) = orbitResidue t s ds g x
  unfold orbitResidue
  congr 1
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hd,flag⟩,dr⟩
    obtain ⟨y,yc⟩ := six_chart_vertex_hits_of_main t s ds g d
      (six_nonaux_is_main t s ds g d (Finset.mem_filter.mp hd).2)
    have yr : g.joined y.val = r.val :=
      (congrArg g.chartVertexJoined (Quotient.sound yc)).trans dr
    have yflag : chosenDart t s ds g c y.val = true :=
      (same_from_step (p := g.chartVertexPerm) (chosenDart_chart_step t s ds g c) yc).trans flag
    have same : sixGapComponent g y = c := (componentMask_gap t s ds g c y).mp yflag
    have yx : rep g.GapVertexPerm y = rep g.GapVertexPerm x :=
      unique _ _ (Subtype.ext yr) (Subtype.ext atR) same
    exact ⟨hd,(Quotient.sound yc).symm.trans (congrArg g.gapVertexToChart yx)⟩
  · rintro ⟨hd,eq⟩
    have step := same_from_step (p := g.chartVertexPerm) (chosenDart_chart_step t s ds g c)
      (Quotient.exact eq)
    have flag : chosenDart t s ds g c x.val = true := (componentMask_gap t s ds g c x).mpr rfl
    exact ⟨⟨hd,step.trans flag⟩,(congrArg g.chartVertexJoined eq).trans atR⟩

/-- The required coordinate of the literal row mask is the actual
signed coefficient at its unique point of contact. -/
theorem crossing_orbit_reads_row_mask (H : t ∈ coefficientTriples)
    (two : Nat.card (SixGapComponent g) = 2)
    (r : Subtype g.joinedHitsGap) (hr : sixCrossComponentRegion g r)
    (x : g.Gap) (atR : g.joined x.val = r.val) :
    coordinate (selectedCharge (chartCharges t) (componentMask t s ds g
      (sixGapComponent g x)).val) (g.factor x.val) = orbitResidue t s ds g x := by
  rw [chart_mask_coordinate t s ds g H, component_charge_localized t s ds g two _ r hr]
  have same : sixJoinedFactor g r.val = g.factor x.val :=
    atR ▸ six_joined_factor_read g x.val
  rw [if_pos same, crossing_residue_on_one_orbit t s ds g two r hr x atR]

open Lean in
run_cmd do
  for n in [``component_charge_localized,``crossing_residue_on_one_orbit,
      ``crossing_orbit_reads_row_mask] do
    unless (← Lean.collectAxioms n).all
      (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "Unexpected axiom for contact charge: {n}"

#print axioms crossing_orbit_reads_row_mask
end
end AK3.SubVPicture.RingGeneralSix
