import VFiveSixComponentMask
import VFiveHomeFullChartClosure

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
section Factor
variable {rows : List (Word × Word)} {outer : BoundarySchedule (combine rows)}
  {q : Perm (Pos rows)} {tr : List (Pos rows × Pos rows)} (g : PlanarCore rows outer q tr)

def sixJoinedFactor : g.Joined → Fin 2 := Quot.lift g.regionFactor (by
  intro c d h
  cases h with
  | zeroSide x _ =>
    have mate := g.gap_mate_flips x
    have turn := (g.changes_iff (g.gapMate x).val).mp (g.gapMate x).property
    have same : g.factor x.val = g.factor (g.turn (g.gapMate x).val) := by
      apply Fin.ext
      omega
    simpa only [g.regionFactor_read, PlanarCore.factor] using same)

theorem six_joined_factor_read (d : g.Dart) : sixJoinedFactor g (g.joined d) = g.factor d :=
  g.regionFactor_read d
end Factor

variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)


/-- A cut does not cross a joined coefficient region when all its
non-auxiliary positions agree on membership in the chosen component. -/
def regionClosedInFactor (c : SixGapComponent g) (f : Fin 2) : Prop :=
  ∀ x y : g.Gap, g.factor x.val = f → g.joined x.val = g.joined y.val →
    (sixGapComponent g x = c ↔ sixGapComponent g y = c)

private def componentDarts (c : SixGapComponent g) : Finset g.Dart :=
  (sixNonauxDarts t s ds g).filter (fun d => chosenDart t s ds g c d = true)

private theorem chosen_agree (c : SixGapComponent g) (f : Fin 2)
    (separated : regionClosedInFactor t s ds g c f)
    {d e : g.Dart} (hd : d ∈ sixNonauxDarts t s ds g)
    (he : e ∈ sixNonauxDarts t s ds g)
    (df : g.factor d = f) (same : g.joined d = g.joined e) :
    chosenDart t s ds g c d = chosenDart t s ds g c e := by
  classical
  obtain ⟨x,hx⟩ := six_chart_vertex_hits_of_main t s ds g d
    (six_nonaux_is_main t s ds g d (Finset.mem_filter.mp hd).2)
  obtain ⟨y,hy⟩ := six_chart_vertex_hits_of_main t s ds g e
    (six_nonaux_is_main t s ds g e (Finset.mem_filter.mp he).2)
  have a : g.joined x.val = g.joined d := congrArg g.chartVertexJoined (Quotient.sound hx)
  have b : g.joined y.val = g.joined e := congrArg g.chartVertexJoined (Quotient.sound hy)
  have xf : g.factor x.val = f := by
    rw [← six_joined_factor_read g x.val, a, six_joined_factor_read]
    exact df
  have yes := separated x y xf (a.trans (same.trans b.symm))
  have opt : chosenDart t s ds g c x.val = chosenDart t s ds g c y.val := by
    apply Bool.eq_iff_iff.mpr
    exact (componentMask_gap t s ds g c x).trans
      (yes.trans (componentMask_gap t s ds g c y).symm)
  have dx := same_from_step (p := g.chartVertexPerm) (chosenDart_chart_step t s ds g c) hx
  have ey := same_from_step (p := g.chartVertexPerm) (chosenDart_chart_step t s ds g c) hy
  exact dx.symm.trans (opt.trans ey)

private theorem chosen_joined_zero (c : SixGapComponent g) (f : Fin 2)
    (separated : regionClosedInFactor t s ds g c f)
    (r : g.Joined) (rf : sixJoinedFactor g r = f) :
    sixJoinedResidue t s ds g (componentDarts t s ds g c) r = 0 := by
  classical
  let A := (componentDarts t s ds g c).filter (fun d => g.joined d = r)
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
        have factor : g.factor e = f := by
          rw [← six_joined_factor_read g e, hc, rf]
        have step := chosen_agree t s ds g c f separated hm main factor (hc.trans atR.symm)
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hm,step.trans flag⟩,hc⟩
    rw [eq]
    exact nonaux_joined_residue_zero t s ds g r
  · rw [Finset.not_nonempty_iff_eq_empty.mp on,Finset.sum_empty]

def componentFactorSum (c : SixGapComponent g) (f : Fin 2) : ZMod 5 := by
  classical
  exact ∑ d ∈ (componentDarts t s ds g c).filter (fun d => g.factor d = f), (g.signed d : ZMod 5)

theorem componentFactorSum_zero (c : SixGapComponent g) (f : Fin 2)
    (separated : regionClosedInFactor t s ds g c f) :
    componentFactorSum t s ds g c f = 0 := by
  classical
  let A := (componentDarts t s ds g c).filter (fun d => g.factor d = f)
  let targets := A.image g.joined
  change ∑ d ∈ A, (g.signed d : ZMod 5) = 0
  rw [← Finset.sum_fiberwise_of_maps_to (s := A) (t := targets) (g := g.joined)
    (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) (fun d => (g.signed d : ZMod 5))]
  apply Finset.sum_eq_zero
  intro r hr
  obtain ⟨d,hd,dc⟩ := Finset.mem_image.mp hr
  have fact : sixJoinedFactor g r = f := by
    rw [← dc, six_joined_factor_read]
    exact (Finset.mem_filter.mp hd).2
  have eq : A.filter (fun d => g.joined d = r) =
      (componentDarts t s ds g c).filter (fun d => g.joined d = r) := by
    ext e
    constructor
    · intro he
      obtain ⟨hm,hc⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm).1,hc⟩
    · intro he
      obtain ⟨hm,hc⟩ := Finset.mem_filter.mp he
      have factor := (six_joined_factor_read g e).symm.trans
        ((congrArg (sixJoinedFactor g) hc).trans fact)
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hm,factor⟩,hc⟩
  rw [eq]
  exact chosen_joined_zero t s ds g c f separated r fact

#print axioms componentFactorSum_zero
end
end AK3.SubVPicture.RingGeneralSix
