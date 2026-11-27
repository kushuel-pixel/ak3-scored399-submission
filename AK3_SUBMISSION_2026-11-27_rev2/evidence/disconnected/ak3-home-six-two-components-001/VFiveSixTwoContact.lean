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
section Generic
variable {rows : List (Word × Word)} {outer : BoundarySchedule (combine rows)}
  {q : Perm (Pos rows)} {tr : List (Pos rows × Pos rows)} (g : PlanarCore rows outer q tr)

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


/-- One crossing uses the full budget of two shared gap-vertex orbits.
There are no other shared gap-vertex orbits, even within either component. -/
theorem two_components_crossing_spends_budget
    (two : Nat.card (SixGapComponent g) = 2)
    {r : Subtype g.joinedHitsGap} (hr : sixCrossComponentRegion g r) :
    ∃ x y : Orbits g.GapVertexPerm,
      g.gapVertexJoined x = r ∧ g.gapVertexJoined y = r ∧
      sixGapVertexComponent g x ≠ sixGapVertexComponent g y ∧
      ∀ z, sharedFiber g.gapVertexJoined z ↔ z = x ∨ z = y := by
  classical
  obtain ⟨x,y,hx,hy,diff⟩ := hr
  have xy : x ≠ y := fun h => diff (congrArg (sixGapVertexComponent g) h)
  let marked := Subtype (sharedFiber g.gapVertexJoined)
  let _ : Fintype marked := Fintype.ofFinite _
  have seed : g.Gap := Quot.out x
  have cap := gap_shared_budget g seed
  change Nat.card marked + 2 ≤ 2 * Nat.card (SixGapComponent g) at cap
  let a : marked := ⟨x,shared_at_same_label g.gapVertexJoined xy (hx.trans hy.symm)⟩
  let b : marked := ⟨y,shared_at_same_label g.gapVertexJoined xy.symm (hy.trans hx.symm)⟩
  refine ⟨x,y,hx,hy,diff,?_⟩
  intro z
  constructor
  · intro hz
    by_contra! outside
    let c : marked := ⟨z,hz⟩
    have ab : a ≠ b := fun e => xy (congrArg Subtype.val e)
    have ac : a ≠ c := fun e => outside.1 (congrArg Subtype.val e).symm
    have bc : b ≠ c := fun e => outside.2 (congrArg Subtype.val e).symm
    have card : ({a,b,c} : Finset marked).card = 3 := by simp [ab,ac,bc]
    have atLeast := Finset.card_le_univ ({a,b,c} : Finset marked)
    rw [card, ← Nat.card_eq_fintype_card] at atLeast
    omega
  · rintro (rfl|rfl)
    · exact a.property
    · exact b.property

/-- The two orbits are precisely the entire fiber over the crossing. -/
theorem two_components_crossing_has_two_orbits
    (two : Nat.card (SixGapComponent g) = 2)
    {r : Subtype g.joinedHitsGap} (hr : sixCrossComponentRegion g r) :
    ∃ x y : Orbits g.GapVertexPerm,
      sixGapVertexComponent g x ≠ sixGapVertexComponent g y ∧
      ∀ z, g.gapVertexJoined z = r ↔ z = x ∨ z = y := by
  obtain ⟨x,y,hx,hy,diff,exactly⟩ := two_components_crossing_spends_budget g two hr
  refine ⟨x,y,diff,fun z => ⟨?_,?_⟩⟩
  · intro hz
    rcases eq_or_ne z x with e|e
    · exact Or.inl e
    · exact (exactly z).mp (shared_at_same_label g.gapVertexJoined e (hz.trans hx.symm))
  · rintro (rfl|rfl)
    · exact hx
    · exact hy

open Lean in
run_cmd do
  for n in [``two_components_crossing_spends_budget,``two_components_crossing_has_two_orbits] do
    unless (← Lean.collectAxioms n).all
      (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "Unexpected axiom in crossing fiber: {n}"

#print axioms two_components_crossing_spends_budget
#print axioms two_components_crossing_has_two_orbits
end Generic
end
end AK3.SubVPicture.RingGeneralSix
