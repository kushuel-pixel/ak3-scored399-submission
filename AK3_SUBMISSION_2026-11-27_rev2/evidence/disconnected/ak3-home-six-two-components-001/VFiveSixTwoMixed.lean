import VFiveSixNegativeSplit

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
section Generic
variable {rows : List (Word × Word)} {outer : BoundarySchedule (combine rows)}
  {q : Perm (Pos rows)} {tr : List (Pos rows × Pos rows)} (g : PlanarCore rows outer q tr)

local notation "C" => SixGapComponent g
local notation "component" => sixGapComponent g

private theorem shared_at_same_label {A B : Type} [Finite A] (f : A → B) {x y : A}
    (ne : x ≠ y) (h : f x = f y) : sharedFiber f x := by
  let pick : Bool → {v // f v = f x}
    | false => ⟨x,rfl⟩
    | true => ⟨y,h.symm⟩
  have inj : Function.Injective pick := by
    intro u v eq
    cases u <;> cases v
    · rfl
    · exact (ne (congrArg Subtype.val eq)).elim
    · exact (ne (congrArg Subtype.val eq).symm).elim
    · rfl
  simpa [sharedFiber] using Nat.card_le_card_of_injective pick inj

def sixGapVertexComponent : Orbits g.GapVertexPerm → C :=
  Quotient.lift (component) (fun _ _ same => same_from_step (p := g.GapVertexPerm)
    (fun x => by
      have across : (component) x = (component) (g.gapMate x) := Quot.sound (Or.inr rfl)
      have forward : g.rotationOnGaps.SameCycle (g.gapMate x) (g.GapVertexPerm x) :=
        (Perm.SameCycle.refl g.rotationOnGaps (g.gapMate x)).apply_right
      exact across.trans (Quot.sound (Or.inl forward))) same)

def sixCrossComponentRegion (c : Subtype g.joinedHitsGap) : Prop :=
  ∃ x y : Orbits g.GapVertexPerm, g.gapVertexJoined x = c ∧ g.gapVertexJoined y = c ∧
    sixGapVertexComponent g x ≠ sixGapVertexComponent g y

end Generic
variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)

local notation "C" => SixGapComponent g
local notation "component" => sixGapComponent g

/-- Two components leave room for at most one shared coefficient region
that actually meets different chart components. -/
theorem six_mixed_region_subsingleton (two : Nat.card C = 2) : Subsingleton (Subtype (sixCrossComponentRegion g)) := by
  classical
  let marked := Subtype (sharedFiber g.gapVertexJoined)
  let _ : Fintype marked := Fintype.ofFinite _
  have cap : Nat.card marked ≤ 2 := by
    have bound := gap_shared_budget g (rowGap t s ds g 2)
    change Nat.card marked + 2 ≤ 2 * Nat.card C at bound
    omega
  constructor
  rintro ⟨u,x,y,hx,hy,diff⟩ ⟨w,z,t,hz,ht,diff'⟩
  apply Subtype.ext
  by_contra ne
  have xy : x ≠ y := fun e => diff (congrArg (sixGapVertexComponent g) e)
  have zt : z ≠ t := fun e => diff' (congrArg (sixGapVertexComponent g) e)
  let a : marked := ⟨x,shared_at_same_label g.gapVertexJoined xy (hx.trans hy.symm)⟩
  let b : marked := ⟨y,shared_at_same_label g.gapVertexJoined (Ne.symm xy) (hy.trans hx.symm)⟩
  let c : marked := ⟨z,shared_at_same_label g.gapVertexJoined zt (hz.trans ht.symm)⟩
  have ab : a ≠ b := fun e => xy (congrArg Subtype.val e)
  have ac : a ≠ c := fun e => ne (hx.symm.trans ((congrArg (g.gapVertexJoined ∘ Subtype.val) e).trans hz))
  have bc : b ≠ c := fun e => ne (hy.symm.trans ((congrArg (g.gapVertexJoined ∘ Subtype.val) e).trans hz))
  have card : ({a,b,c} : Finset marked).card = 3 := by simp [ab,ac,bc]
  have atLeast := Finset.card_le_univ ({a,b,c} : Finset marked)
  rw [card, ← Nat.card_eq_fintype_card] at atLeast
  omega



/-- Mixedness witnessed on the actual gaps is mixedness of their two vertex orbits. -/
theorem mixed_of_gap_pair (x y : g.Gap) (same : g.joined x.val = g.joined y.val)
    (diff : component x ≠ component y) :
    ∃ r : Subtype g.joinedHitsGap, r.val = g.joined x.val ∧ sixCrossComponentRegion g r := by
  let r := g.gapVertexJoined (rep g.GapVertexPerm x)
  exact ⟨r, rfl, rep g.GapVertexPerm x, rep g.GapVertexPerm y, rfl,
    Subtype.ext same.symm, diff⟩

/-- A two-component diagram has a coefficient factor separating all
components simultaneously. There is no assumption of full closure. -/
theorem two_components_have_closed_factor (two : Nat.card C = 2) :
    ∃ f : Fin 2, ∀ c : C, regionClosedInFactor t s ds g c f := by
  classical
  let unique := six_mixed_region_subsingleton t s ds g two
  by_cases existsMixed : Nonempty (Subtype (sixCrossComponentRegion g))
  · obtain ⟨⟨r,hr⟩⟩ := existsMixed
    let f : Fin 2 := if sixJoinedFactor g r.val = 0 then 1 else 0
    have different : sixJoinedFactor g r.val ≠ f := by
      dsimp [f]
      split <;> rename_i h
      · rw [h]; decide
      · exact h
    refine ⟨f, ?_⟩
    intro c x y xf same
    by_cases xy : component x = component y
    · rw [xy]
    · obtain ⟨p,hp,mp⟩ := mixed_of_gap_pair t s ds g x y same xy
      have pr : p = r := congrArg Subtype.val (unique.elim ⟨p,mp⟩ ⟨r,hr⟩)
      exact (different (by rw [← pr,hp,six_joined_factor_read]; exact xf)).elim
  · refine ⟨0, ?_⟩
    intro c x y _ same
    by_cases xy : component x = component y
    · rw [xy]
    · obtain ⟨p,_,mp⟩ := mixed_of_gap_pair t s ds g x y same xy
      exact (existsMixed ⟨⟨p,mp⟩⟩).elim

open Lean in
run_cmd do
  for n in [``six_mixed_region_subsingleton,``two_components_have_closed_factor] do
    unless (← Lean.collectAxioms n).all
      (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "Unexpected axiom in two-component split: {n}"

#print axioms six_mixed_region_subsingleton
#print axioms two_components_have_closed_factor
end
end AK3.SubVPicture.RingGeneralSix
