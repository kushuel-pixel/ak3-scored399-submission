import VFiveSixRingClosed

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
abbrev SixGapComponent := Mix g.rotationOnGaps g.gapMate
def sixGapComponent (x : g.Gap) : SixGapComponent g :=
  mrep g.rotationOnGaps g.gapMate x

end Generic

variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)

def rowGap (i : Fin 6) : g.Gap :=
  (main_has_gaps g (literalSix_padded t s ds) (literalSix_main t s ds) i).choose

theorem rowGap_owner (i : Fin 6) : gapOwner g (rowGap t s ds g i) = i.val :=
  (main_has_gaps g (literalSix_padded t s ds) (literalSix_main t s ds) i).choose_spec

theorem same_row_same_component (x y : g.Gap) (h : gapOwner g x = gapOwner g y) :
    sixGapComponent g x = sixGapComponent g y :=
  Quot.sound (Or.inl ((gapCycle_iff_owner g (literalSix_padded t s ds) x y).mpr h))

theorem component_rows_surj :
    Function.Surjective (sixGapComponent g ∘ rowGap t s ds g) := by
  intro c
  induction c using Quot.inductionOn with
  | _ x =>
    let i : Fin 6 := ⟨gapOwner g x,auxiliary_no_gap g (literalSix_padded t s ds)
      (literalSix_aux t s ds) x⟩
    exact ⟨i,same_row_same_component t s ds g _ _ (rowGap_owner t s ds g i)⟩

private theorem pack_six_bits : ∀ a : Fin 6 → Bool, ∃ m : Fin 64, ∀ i : Fin 6, m.val.testBit i.val = a i := by
  decide +kernel

def componentMask (c : SixGapComponent g) : Fin 64 := by
  classical
  exact   (pack_six_bits (fun i => decide (sixGapComponent g (rowGap t s ds g i) = c))).choose

theorem componentMask_spec (c : SixGapComponent g) (i : Fin 6) :
    (componentMask t s ds g c).val.testBit i.val = true ↔
      sixGapComponent g (rowGap t s ds g i) = c := by
  classical
  let a : Fin 6 → Bool := fun j => decide (sixGapComponent g (rowGap t s ds g j) = c)
  have h := (pack_six_bits a).choose_spec i
  change (pack_six_bits a).choose.val.testBit i.val = true ↔ _
  rw [h]
  change decide (sixGapComponent g (rowGap t s ds g i) = c) = true ↔ _
  exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

theorem componentMask_gap (c : SixGapComponent g) (x : g.Gap) :
    (componentMask t s ds g c).val.testBit (gapOwner g x) = true ↔ sixGapComponent g x = c := by
  let i : Fin 6 := ⟨gapOwner g x,auxiliary_no_gap g (literalSix_padded t s ds) (literalSix_aux t s ds) x⟩
  have e := same_row_same_component t s ds g (rowGap t s ds g i) x (rowGap_owner t s ds g i)
  exact (componentMask_spec t s ds g c i).trans (by rw [e])

theorem componentMask_proper (c : SixGapComponent g) (split : 2 ≤ Nat.card (SixGapComponent g)) :
    0 < (componentMask t s ds g c).val ∧ (componentMask t s ds g c).val < 63 := by
  classical
  let m := componentMask t s ds g c
  obtain ⟨i,hi⟩ := component_rows_surj t s ds g c
  have on := (componentMask_spec t s ds g c i).2 hi
  have positive : 0 < m.val := by
    by_contra! h
    have zero : m.val = 0 := by omega
    change m.val.testBit i.val = true at on
    simp [zero] at on
  have nfull : m.val ≠ 63 := by
    intro full
    have all : ∀ j : Fin 6, (63 : Nat).testBit j.val = true := by decide +kernel
    let _ : Subsingleton (SixGapComponent g) := ⟨fun a b => by
      obtain ⟨ia,rfl⟩ := component_rows_surj t s ds g a
      obtain ⟨ib,rfl⟩ := component_rows_surj t s ds g b
      exact ((componentMask_spec t s ds g c ia).mp (full.symm ▸ all ia)).trans
        ((componentMask_spec t s ds g c ib).mp (full.symm ▸ all ib)).symm⟩
    let _ : Fintype (SixGapComponent g) := Fintype.ofFinite _
    have size : Nat.card (SixGapComponent g) ≤ 1 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    omega
  exact ⟨positive,by have := m.isLt; omega⟩

def chosenDart (c : SixGapComponent g) (d : g.Dart) : Bool :=
  (componentMask t s ds g c).val.testBit (g.rowOwner d).val

theorem chosenDart_chart_step (c : SixGapComponent g) (d : g.Dart) :
    chosenDart t s ds g c d = chosenDart t s ds g c (g.chartVertexPerm d) := by
  change chosenDart t s ds g c d = chosenDart t s ds g c (g.turn (bandPerm g.gapBands d))
  have turn (x : g.Dart) : chosenDart t s ds g c (g.turn x) = chosenDart t s ds g c x := by
    unfold chosenDart
    rw [g.turn_owner (literalSix_padded t s ds)]
  rw [turn]
  by_cases h : g.factor (g.gapWalk d) ≠ g.factor d
  · let x : g.Gap := ⟨d,h⟩
    change chosenDart t s ds g c x.val = chosenDart t s ds g c (bandPerm g.gapBands x.val)
    rw [g.bandPerm_gapMate]
    have eq : sixGapComponent g x = sixGapComponent g (g.gapMate x) := Quot.sound (Or.inr rfl)
    apply Bool.eq_iff_iff.mpr
    exact (componentMask_gap t s ds g c x).trans
      (Iff.trans (by rw [eq]) (componentMask_gap t s ds g c (g.gapMate x)).symm)
  · have off : d ∉ used g.gapBands := fun e => h ((g.changes_iff d).mpr ((g.gapBands_cover d).mp e))
    rw [unused_band _ _ off]

#print axioms componentMask_proper
#print axioms chosenDart_chart_step
end
end AK3.SubVPicture.RingGeneralSix
