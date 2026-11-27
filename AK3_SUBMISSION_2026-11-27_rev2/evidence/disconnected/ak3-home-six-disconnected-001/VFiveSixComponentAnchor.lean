import VFiveSixComponentMask
import VFiveSixIsolatedAnchor

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

private theorem owner_lt_six (x : g.Gap) : gapOwner g x < 6 :=
  auxiliary_no_gap g (literalSix_padded t s ds) (literalSix_aux t s ds) x

private theorem anchor_mask_rows (c : SixGapComponent g) (plus : Fin 2)
    (mask : (componentMask t s ds g c).val = 5 + plus.val) :
    ∀ x : g.Gap, sixGapComponent g x = c ↔
      gapOwner g x = plus.val ∨ gapOwner g x = 2 := by
  have bits : ∀ (a : Fin 2) (i : Fin 6),
      ((5:Nat)+a.val).testBit i.val = true ↔ i.val = a.val ∨ i.val = 2 := by
    decide +kernel
  intro x
  have e := componentMask_gap t s ds g c x
  rw [mask] at e
  exact e.symm.trans (bits plus ⟨gapOwner g x,owner_lt_six t s ds g x⟩)

private theorem anchor_component_isolated (plus : Fin 2) (c : SixGapComponent g)
    (describes : ∀ x : g.Gap, sixGapComponent g x = c ↔ gapOwner g x = plus.val ∨ gapOwner g x = 2) :
    ∀ x : g.Gap, remainingGap g (deletedAnchors plus) x.val ↔
      remainingGap g (deletedAnchors plus) (g.gapMate x).val := by
  intro x
  have e : sixGapComponent g x = sixGapComponent g (g.gapMate x) := Quot.sound (Or.inr rfl)
  have keep (y : g.Gap) : remainingGap g (deletedAnchors plus) y.val ↔ ¬ sixGapComponent g y = c := by
    rw [describes y]
    exact ⟨fun h e => e.elim h.2.1 h.2.2,
      fun h => ⟨y.property,fun e => h (Or.inl e),fun e => h (Or.inr e)⟩⟩
  rw [keep x,keep (g.gapMate x),e]

private theorem anchor_component_seed (plus : Fin 2) (c : SixGapComponent g)
    (describes : ∀ x : g.Gap, sixGapComponent g x = c ↔ gapOwner g x = plus.val ∨ gapOwner g x = 2) :
    ∃ x : g.Gap, gapOwner g x = plus.val ∧ gapOwner g (g.gapMate x) = 2 := by
  classical
  by_contra! no
  let pos : Fin 6 := ⟨plus.val,plus.isLt.trans (by decide)⟩
  let p := rowGap t s ds g pos
  let n := rowGap t s ds g 2
  have hp : gapOwner g p = plus.val := rowGap_owner t s ds g pos
  have hn : gapOwner g n = 2 := rowGap_owner t s ds g 2
  have stable (x : g.Gap) (positive : gapOwner g x = plus.val) :
      gapOwner g (g.gapMate x) = plus.val := by
    have e : sixGapComponent g x = sixGapComponent g (g.gapMate x) := Quot.sound (Or.inr rfl)
    have same := (describes (g.gapMate x)).mp (e.symm.trans ((describes x).mpr (Or.inl positive)))
    exact same.resolve_right (no x positive)
  let label : SixGapComponent g → Bool := Quot.lift (fun x : g.Gap => decide (gapOwner g x = plus.val)) (by
    intro x y h
    have agrees : gapOwner g x = plus.val ↔ gapOwner g y = plus.val := by
      rcases h with h | rfl
      · rw [(gapCycle_iff_owner g (literalSix_padded t s ds) _ _).mp h]
      · exact ⟨stable x,fun h => g.gap_invol x ▸ stable (g.gapMate x) h⟩
    by_cases h : gapOwner g x = plus.val
    · simp [h, agrees.mp h]
    · simp [h, mt agrees.mpr h])
  have eq : sixGapComponent g p = sixGapComponent g n :=
    ((describes p).mpr (Or.inl hp)).trans ((describes n).mpr (Or.inr hn)).symm
  have result := congrArg label eq
  change decide (gapOwner g p = plus.val) = decide (gapOwner g n = plus.val) at result
  have ne : 2 ≠ plus.val := by have := plus.isLt; omega
  simp [hp,hn,ne] at result

/-- Neither positive/negative two-row component can occur. This is an
actual component exclusion, with no digon or given seed premise. -/
theorem anchor_component_mask_excluded (H : t ∈ coefficientTriples) (c : SixGapComponent g) :
    (componentMask t s ds g c).val ≠ 5 ∧ (componentMask t s ds g c).val ≠ 6 := by
  have exclude (p : Fin 2) (hm : (componentMask t s ds g c).val = 5+p.val) : False := by
    have desc := anchor_mask_rows t s ds g c p hm
    obtain ⟨seed,positive,negative⟩ := anchor_component_seed t s ds g p c desc
    exact six_isolated_anchor_pair_excluded t s ds g p H seed positive negative
      (anchor_component_isolated t s ds g p c desc)
  exact ⟨exclude 0,exclude 1⟩

open Lean in
run_cmd do
  unless (← Lean.collectAxioms ``anchor_component_mask_excluded).all
    (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
    throwError "Unexpected axiom"
#print axioms anchor_component_mask_excluded
end
end AK3.SubVPicture.RingGeneralSix
