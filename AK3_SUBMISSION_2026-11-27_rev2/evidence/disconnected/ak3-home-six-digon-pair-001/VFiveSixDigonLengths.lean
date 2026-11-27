import VFiveSixPairCensus
import VFiveSixPairOrder

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






local notation "rows" => (literalSix t s ++ discRows ds)

private theorem reverseSlot_owner (i : Fin (rows).length) (j : Fin rows[i].2.length) :
    g.rowOwner (g.reverseSlot i j) = i :=
  Fin.ext ((g.owner_coord _).symm.trans (congrArg Prod.fst (g.reverseSlot_site i j)))

private theorem reverseSlot_injective (i : Fin (rows).length) :
    Function.Injective (g.reverseSlot i) := by
  intro j k eq
  have e := congrArg (fun x : g.Dart => (coord rows x.val).2.2) eq
  rw [g.reverseSlot_site, g.reverseSlot_site] at e
  exact backwardsIndex_involutive.injective (Fin.ext e)

theorem pairCycle_iff_owner (i : Nat × Nat) (x y : Subtype (pairRowGap g i)) :
    (pairRowRotation g i).SameCycle x y ↔ g.rowOwner x.val = g.rowOwner y.val :=
  (project_same g.turn (pairRowGap g i) x y).trans
    (g.turn_sameCycle_iff_row (literalSix_padded t s ds) x.val y.val)

/-- Each raw boundary cycle is exactly the set of literal factor changes
on its original expanded word, with no extra cuts from the sewing. -/
def pairFaceCutsEquiv (i : Nat × Nat) (x : Subtype (pairRowGap g i)) :
    Subtype (literalCut rows[g.rowOwner x.val].2) ≃
      {y : Subtype (pairRowGap g i) //
        (pairRowRotation g i).SameCycle x y} := by
  let o := g.rowOwner x.val
  let dart (j : Subtype (literalCut rows[o].2)) : Subtype (pairRowGap g i) :=
    ⟨g.reverseSlot o j.val,
      (g.reverseSlot_cut o j.val (literalSix_padded t s ds o)).mpr j.property,
      by rw [reverseSlot_owner t s ds g]; exact x.property.2⟩
  let lift (j : Subtype (literalCut rows[o].2)) :
      {y : Subtype (pairRowGap g i) //
        (pairRowRotation g i).SameCycle x y} :=
    ⟨dart j, (pairCycle_iff_owner t s ds g i x (dart j)).mpr
      (reverseSlot_owner t s ds g o j.val).symm⟩
  refine Equiv.ofBijective lift ⟨?_, ?_⟩
  · intro j k eq
    exact Subtype.ext (reverseSlot_injective t s ds g o
      (congrArg (fun u => u.val.val) eq))
  · intro y
    have owner : g.rowOwner y.val.val = o :=
      ((pairCycle_iff_owner t s ds g i x y.val).mp y.property).symm
    have hasSlot (d : g.Dart) (index : Fin (rows).length) (e : g.rowOwner d = index) :
        ∃ j : Fin rows[index].2.length, g.reverseSlot index j = d := by
      subst index
      exact g.reverseSlot_covers d
    obtain ⟨j, hj⟩ := hasSlot y.val.val o owner
    have cut := (g.reverseSlot_cut o j (literalSix_padded t s ds o)).mp
      (hj.symm ▸ y.val.property.1)
    exact ⟨⟨j, cut⟩, Subtype.ext (Subtype.ext hj)⟩



theorem actual_pair_cycle_length (H : t ∈ coefficientTriples)
    (i : Nat × Nat) (x : Subtype (pairRowGap g i)) (a : Fin 6)
    (owner : (g.rowOwner x.val).val = a.val) :
    Nat.card {y : Subtype (pairRowGap g i) // (pairRowRotation g i).SameCycle x y} =
      (sixTapeAt t a).length := by
  have e : g.rowOwner x.val = mainIndex t s ds a := Fin.ext owner
  have h := (Nat.card_congr (pairFaceCutsEquiv t s ds g i x)).symm
  rw [card_literalCut] at h
  have word := (congrArg (fun j : Fin (rows).length => rows[j].2) e).trans
    (sixTapeAt_expanded t s ds a)
  exact h.trans ((congrArg literalCutCount word).trans (six_tape_facts t H a).cuts)

private theorem digon_pair_seed (c : SixGapComponent g) (a b : Fin 6) (ne : a ≠ b)
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

/-- In the 2-row component with all degrees 2, the actual gap pairing
takes an entire row bijectively to the other row. Hence their tape lengths agree. -/
theorem actual_digon_pair_lengths (H : t ∈ coefficientTriples)
    (c : SixGapComponent g) (a b : Fin 6) (ne : a ≠ b)
    (desc : ∀ x : g.Gap, sixGapComponent g x = c ↔ gapOwner g x = a.val ∨ gapOwner g x = b.val)
    (all : ∀ z, vertexDegree (faces (pairRowRotation g (a.val,b.val))
      (pairRowBands g (a.val,b.val))) z = 2) :
    (sixTapeAt t a).length = (sixTapeAt t b).length := by
  let i := (a.val,b.val)
  let D := Subtype (pairRowGap g i)
  let p := pairRowRotation g i
  let m := bandPerm (pairRowBands g i)
  let view := pairRowToGap g i
  have side (x : g.Gap) : pairRowGap g i x.val ↔ sixGapComponent g x = c :=
    ⟨fun h => (desc x).mpr h.2,fun h => ⟨x.property,(desc x).mp h⟩⟩
  have iso (x : g.Gap) : pairRowGap g i x.val ↔ pairRowGap g i (g.gapMate x).val := by
    have e : sixGapComponent g x = sixGapComponent g (g.gapMate x) := Quot.sound (Or.inr rfl)
    rw [side x,side (g.gapMate x),e]
  obtain ⟨seed,sa,sb⟩ := digon_pair_seed t s ds g c a b ne desc
  let x : D := ⟨seed.val,seed.property,Or.inl sa⟩
  have mate (z : D) : view (m z) = g.gapMate (view z) :=
    Subtype.ext (pair_row_mate_agrees g i iso z)
  have inv : Function.Involutive m := by
    intro z
    have eq : view (m (m z)) = view z := (mate (m z)).trans (by rw [mate z,g.gap_invol])
    exact Subtype.ext (congrArg (fun w : g.Gap => w.val) eq)
  have double (z : D) : (p*m) ((p*m) z) = z :=
    degree_two_forces_double_return (p*m) z (all _)
  let E : {z : D // p.SameCycle x z} ≃ {z : D // p.SameCycle (m x) z} := {
    toFun := fun z => ⟨m z.val,return_two_reverses_rows p m inv double _ _ z.property⟩
    invFun := fun z => ⟨m z.val,by
      have h := return_two_reverses_rows p m inv double _ _ z.property
      rwa [inv x] at h⟩
    left_inv := fun z => Subtype.ext (inv z.val)
    right_inv := fun z => Subtype.ext (inv z.val) }
  have ob : (g.rowOwner (m x).val).val = b.val := by
    change gapOwner g (view (m x)) = b.val
    rw [mate x]
    exact sb
  exact (actual_pair_cycle_length t s ds g H i x a sa).symm.trans
    ((Nat.card_congr E).trans (actual_pair_cycle_length t s ds g H i (m x) b ob))

#print axioms actual_digon_pair_lengths
end
end AK3.SubVPicture.RingGeneralSix
