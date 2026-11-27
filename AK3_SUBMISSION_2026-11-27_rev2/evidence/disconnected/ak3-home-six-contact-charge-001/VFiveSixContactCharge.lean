import VFiveSixTwoReduction

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

private def localComponentDarts (c : SixGapComponent g) : Finset g.Dart :=
  (sixNonauxDarts t s ds g).filter (fun d => chosenDart t s ds g c d = true)

private theorem chosen_agree (c : SixGapComponent g) (r : g.Joined)
    (separated : ∀ x y : g.Gap, g.joined x.val = r → g.joined y.val = r →
      sixGapComponent g x = sixGapComponent g y)
    {d e : g.Dart} (hd : d ∈ sixNonauxDarts t s ds g)
    (he : e ∈ sixNonauxDarts t s ds g)
    (dr : g.joined d = r) (er : g.joined e = r) :
    chosenDart t s ds g c d = chosenDart t s ds g c e := by
  classical
  obtain ⟨x,hx⟩ := six_chart_vertex_hits_of_main t s ds g d
    (six_nonaux_is_main t s ds g d (Finset.mem_filter.mp hd).2)
  obtain ⟨y,hy⟩ := six_chart_vertex_hits_of_main t s ds g e
    (six_nonaux_is_main t s ds g e (Finset.mem_filter.mp he).2)
  have a : g.joined x.val = g.joined d := congrArg g.chartVertexJoined (Quotient.sound hx)
  have b : g.joined y.val = g.joined e := congrArg g.chartVertexJoined (Quotient.sound hy)
  have yes := separated x y (a.trans dr) (b.trans er)
  have opt : chosenDart t s ds g c x.val = chosenDart t s ds g c y.val := by
    apply Bool.eq_iff_iff.mpr
    exact (componentMask_gap t s ds g c x).trans
      ((show sixGapComponent g x = c ↔ sixGapComponent g y = c by rw [yes]).trans (componentMask_gap t s ds g c y).symm)
  have dx := same_from_step (p := g.chartVertexPerm) (chosenDart_chart_step t s ds g c) hx
  have ey := same_from_step (p := g.chartVertexPerm) (chosenDart_chart_step t s ds g c) hy
  exact dx.symm.trans (opt.trans ey)

private theorem chosen_joined_zero (c : SixGapComponent g) (r : g.Joined)
    (separated : ∀ x y : g.Gap, g.joined x.val = r → g.joined y.val = r →
      sixGapComponent g x = sixGapComponent g y) :
    sixJoinedResidue t s ds g (localComponentDarts t s ds g c) r = 0 := by
  classical
  let A := (localComponentDarts t s ds g c).filter (fun d => g.joined d = r)
  let E := (sixNonauxDarts t s ds g).filter (fun d => g.joined d = r)
  change ∑ d ∈ A, (g.signed d : ZMod 5) = 0
  by_cases on : A.Nonempty
  · obtain ⟨d,hd⟩ := on
    obtain ⟨keep,atR⟩ := Finset.mem_filter.mp hd
    obtain ⟨main,flag⟩ := Finset.mem_filter.mp keep
    have eq : A = E := by
      ext e
      constructor
      · intro he
        obtain ⟨hp,hc⟩ := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,hc⟩
      · intro he
        obtain ⟨hm,hc⟩ := Finset.mem_filter.mp he
        have step := chosen_agree t s ds g c r separated hm main hc atR
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hm,step.trans flag⟩,hc⟩
    rw [eq]
    exact nonaux_joined_residue_zero t s ds g r
  · rw [Finset.not_nonempty_iff_eq_empty.mp on,Finset.sum_empty]

/-- Contribution of the selected component to a single joined region. -/
def contactResidue (c : SixGapComponent g) (r : g.Joined) : ZMod 5 :=
    sixJoinedResidue t s ds g (localComponentDarts t s ds g c) r

theorem contactResidue_zero_off_crossing (two : Nat.card (SixGapComponent g) = 2)
    (c : SixGapComponent g) (r : Subtype g.joinedHitsGap) (hr : sixCrossComponentRegion g r)
    (p : g.Joined) (ne : p ≠ r.val) : contactResidue t s ds g c p = 0 := by
  apply chosen_joined_zero
  intro x y hx hy
  by_contra diff
  obtain ⟨q,hq,mixed⟩ := mixed_of_gap_pair t s ds g x y (hx.trans hy.symm) diff
  have one := six_mixed_region_subsingleton t s ds g two
  have eq : q = r := congrArg Subtype.val (one.elim ⟨q,mixed⟩ ⟨r,hr⟩)
  exact ne (hx.symm.trans (hq.symm.trans (congrArg Subtype.val eq)))

/-- For a genuine crossing, the entire coefficient in its factor is
contributed by that region; the other factor has coefficient zero. -/
theorem component_charge_localized (two : Nat.card (SixGapComponent g) = 2)
    (c : SixGapComponent g) (r : Subtype g.joinedHitsGap) (hr : sixCrossComponentRegion g r)
    (f : Fin 2) : componentFactorSum t s ds g c f =
      if sixJoinedFactor g r.val = f then contactResidue t s ds g c r.val else 0 := by
  classical
  let A := (localComponentDarts t s ds g c).filter (fun d => g.factor d = f)
  let T := insert r.val (A.image g.joined)
  change ∑ d ∈ A, (g.signed d : ZMod 5) = _
  rw [← Finset.sum_fiberwise_of_maps_to (s := A) (t := T) (g := g.joined)
     (fun d hd => Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hd,rfl⟩))
     (fun d => (g.signed d : ZMod 5))]
  have fiber (p : g.Joined) :
      (∑ d ∈ A.filter (fun d => g.joined d = p), (g.signed d : ZMod 5)) =
      if sixJoinedFactor g p = f then contactResidue t s ds g c p else 0 := by
    by_cases h : sixJoinedFactor g p = f
    · rw [if_pos h]
      have eq : A.filter (fun d => g.joined d = p) =
          (localComponentDarts t s ds g c).filter (fun d => g.joined d = p) := by
        ext d
        simp only [A,Finset.mem_filter]
        constructor
        · rintro ⟨⟨hd,_⟩,j⟩; exact ⟨hd,j⟩
        · rintro ⟨hd,j⟩
          exact ⟨⟨hd,(six_joined_factor_read g d).symm.trans
            ((congrArg (sixJoinedFactor g) j).trans h)⟩,j⟩
      rw [eq]
      rfl
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro d hd
      obtain ⟨hf,hp⟩ := Finset.mem_filter.mp hd
      exact (h (hp ▸ (six_joined_factor_read g d).trans
        (Finset.mem_filter.mp hf).2)).elim
  calc
    _ = ∑ p ∈ T, (if sixJoinedFactor g p = f then contactResidue t s ds g c p else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      exact fiber p
    _ = _ := by
      apply Finset.sum_eq_single r.val
      · intro p _ ne
        simp [contactResidue_zero_off_crossing t s ds g two c r hr p ne]
      · intro abs
        exact (abs (Finset.mem_insert_self _ _)).elim

#print axioms component_charge_localized
end
end AK3.SubVPicture.RingGeneralSix
