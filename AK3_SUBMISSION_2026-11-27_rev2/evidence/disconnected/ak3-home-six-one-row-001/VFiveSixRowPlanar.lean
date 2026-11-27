import VFiveSixFixedGap

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

variable {rows : List (Word × Word)}
  {outer : BoundarySchedule (combine rows)}
  {q : Perm (Pos rows)} {tr : List (Pos rows × Pos rows)}
  (g : PlanarCore rows outer q tr)


def oneRowGap (i : Nat) (x : g.Dart) : Prop :=
  g.factor (g.gapWalk x) ≠ g.factor x ∧ (g.rowOwner x).val = i

def oneRowRotation (i : Nat) : Perm (Subtype (oneRowGap g i)) := prune g.turn (oneRowGap g i)

def oneRowBands (i : Nat) : List (Subtype (oneRowGap g i) × Subtype (oneRowGap g i)) :=
  restrictBands (oneRowGap g i) g.gapBands

def oneRowToGap (i : Nat) (x : Subtype (oneRowGap g i)) : g.Gap :=
  ⟨x.val,x.property.1⟩

theorem one_row_rotation_agrees (stems : ∀ i : Fin rows.length, rows[i].1 ≠ []) (drop : Nat)
    (x : Subtype (oneRowGap g drop)) :
    (oneRowRotation g drop x).val =
      (g.rotationOnGaps (oneRowToGap g drop x)).val := by
  let K := fun y : g.Dart => g.factor (g.gapWalk y) ≠ g.factor y
  let y : Subtype K := oneRowToGap g drop x
  let n := len g.turn K y
  have same (k : Nat) : g.rowOwner ((g.turn^k) x.val) = g.rowOwner x.val := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ',Perm.mul_apply,g.turn_owner stems,ih]
  have t := len_spec g.turn K y
  have t' : First g.turn (oneRowGap g drop) x.val n := by
    refine ⟨t.1, ⟨t.2.1, ?_⟩, fun j hj jn both => t.2.2 j hj jn both.1⟩
    rw [same n]
    exact x.property.2
  change (prune g.turn (oneRowGap g drop) x).val =
    (prune g.turn K y).val
  rw [prune_spec, prune_spec,
    first_length_unique (oneRowGap g drop)
      (len_spec g.turn (oneRowGap g drop) x) t']
  rfl

/-- If the two omitted faces are isolated under the gap pairing, every
old partner of a retained side is kept and no new partner is introduced. -/
theorem one_row_mate_agrees (drop : Nat)
    (isolated : ∀ y : g.Gap,
      oneRowGap g drop y.val ↔
        oneRowGap g drop (g.gapMate y).val)
    (x : Subtype (oneRowGap g drop)) :
    (bandPerm (oneRowBands g drop) x).val =
      (g.gapMate (oneRowToGap g drop x)).val := by
  have closed : ∀ e ∈ g.gapBands,
      oneRowGap g drop e.1 ↔ oneRowGap g drop e.2 := by
    intro e mem
    let y : g.Gap := ⟨e.1, (g.changes_iff _).mpr ((g.gapBands_cover _).mp
      (used_mem.mpr ⟨e,mem,Or.inl rfl⟩))⟩
    have matchSide : (g.gapMate y).val = e.2 :=
      (g.bandPerm_gapMate y).symm.trans
        ((partners g.gapBands g.gapBands_distinct e.1 e.2 mem).1)
    have h := isolated y
    change oneRowGap g drop e.1 ↔
      oneRowGap g drop (g.gapMate y).val at h
    rw [matchSide] at h
    exact h
  calc
    _ = bandPerm g.gapBands x.val := restrictBands_perm_closed
      (oneRowGap g drop) g.gapBands g.gapBands_distinct closed x
    _ = _ := g.bandPerm_gapMate (oneRowToGap g drop x)


/-- For an isolated literal row, its retained chart is planar, and
all its corners are on one boundary cycle. -/
theorem one_row_planar_counts (i : Nat)
    (stems : ∀ j : Fin rows.length, rows[j].1 ≠ [])
    (seed : g.Gap) (on : gapOwner g seed = i) :
    let p := oneRowRotation g i
    let bs := oneRowBands g i
    Nat.card (Orbits (faces p bs)) = bs.length + 1 := by
  let p := oneRowRotation g i
  let bs := oneRowBands g i
  let D := Subtype (oneRowGap g i)
  let x : D := ⟨seed.val,seed.property,on⟩
  have cyc (u v : D) : p.SameCycle u v := by
    apply (project_same g.turn (oneRowGap g i) u v).mpr
    exact (g.turn_sameCycle_iff_row stems u.val v.val).mpr
      (Fin.ext (u.property.2.trans v.property.2.symm))
  let F : Orbits p ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => rep p x
      left_inv := by
        intro a
        induction a using Quotient.inductionOn with
        | _ a => exact Quotient.sound (cyc x a)
      right_inv := fun u => by cases u; rfl }
  let C : Mix p (bandPerm bs) ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => mrep p (bandPerm bs) x
      left_inv := by
        intro a
        induction a using Quot.inductionOn with
        | _ a => exact Quot.sound (Or.inl (cyc x a))
      right_inv := fun u => by cases u; rfl }
  have A := Nat.card_congr F
  have nd : (used bs).Nodup :=
    restrictBands_distinct (oneRowGap g i) g.gapBands g.gapBands_distinct
  have B := (Nat.card_congr (bandMix p bs nd)).trans (Nat.card_congr C)
  have e := restrict_gap_zero (oneRowGap g i) g.turn g.gapBands
    g.gapBands_distinct (g.gapBands_zero g.letterBands_zero)
  change deficit (Nat.card (Orbits p)) bs.length (Nat.card (Orbits (faces p bs)))
    (Nat.card (Quotient (comp p bs))) = 0 at e
  rw [A,B,Nat.card_unique] at e
  unfold deficit at e
  change Nat.card (Orbits (faces p bs)) = bs.length + 1
  omega

#print axioms one_row_planar_counts
end
end AK3.SubVPicture.RingGeneralSix
