import VFiveSixRowExclusion

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


def pairRowGap (i : Nat × Nat) (x : g.Dart) : Prop :=
  g.factor (g.gapWalk x) ≠ g.factor x ∧ ((g.rowOwner x).val = i.1 ∨ (g.rowOwner x).val = i.2)

def pairRowRotation (i : Nat × Nat) : Perm (Subtype (pairRowGap g i)) := prune g.turn (pairRowGap g i)

def pairRowBands (i : Nat × Nat) : List (Subtype (pairRowGap g i) × Subtype (pairRowGap g i)) :=
  restrictBands (pairRowGap g i) g.gapBands

def pairRowToGap (i : Nat × Nat) (x : Subtype (pairRowGap g i)) : g.Gap :=
  ⟨x.val,x.property.1⟩

theorem pair_row_rotation_agrees (stems : ∀ i : Fin rows.length, rows[i].1 ≠ []) (drop : Nat × Nat)
    (x : Subtype (pairRowGap g drop)) :
    (pairRowRotation g drop x).val =
      (g.rotationOnGaps (pairRowToGap g drop x)).val := by
  let K := fun y : g.Dart => g.factor (g.gapWalk y) ≠ g.factor y
  let y : Subtype K := pairRowToGap g drop x
  let n := len g.turn K y
  have same (k : Nat) : g.rowOwner ((g.turn^k) x.val) = g.rowOwner x.val := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ',Perm.mul_apply,g.turn_owner stems,ih]
  have t := len_spec g.turn K y
  have t' : First g.turn (pairRowGap g drop) x.val n := by
    refine ⟨t.1, ⟨t.2.1, ?_⟩, fun j hj jn both => t.2.2 j hj jn both.1⟩
    rw [same n]
    exact x.property.2
  change (prune g.turn (pairRowGap g drop) x).val =
    (prune g.turn K y).val
  rw [prune_spec, prune_spec,
    first_length_unique (pairRowGap g drop)
      (len_spec g.turn (pairRowGap g drop) x) t']
  rfl

/-- If the two omitted faces are isolated under the gap pairing, every
old partner of a retained side is kept and no new partner is introduced. -/
theorem pair_row_mate_agrees (drop : Nat × Nat)
    (isolated : ∀ y : g.Gap,
      pairRowGap g drop y.val ↔
        pairRowGap g drop (g.gapMate y).val)
    (x : Subtype (pairRowGap g drop)) :
    (bandPerm (pairRowBands g drop) x).val =
      (g.gapMate (pairRowToGap g drop x)).val := by
  have closed : ∀ e ∈ g.gapBands,
      pairRowGap g drop e.1 ↔ pairRowGap g drop e.2 := by
    intro e mem
    let y : g.Gap := ⟨e.1, (g.changes_iff _).mpr ((g.gapBands_cover _).mp
      (used_mem.mpr ⟨e,mem,Or.inl rfl⟩))⟩
    have matchSide : (g.gapMate y).val = e.2 :=
      (g.bandPerm_gapMate y).symm.trans
        ((partners g.gapBands g.gapBands_distinct e.1 e.2 mem).1)
    have h := isolated y
    change pairRowGap g drop e.1 ↔
      pairRowGap g drop (g.gapMate y).val at h
    rw [matchSide] at h
    exact h
  calc
    _ = bandPerm g.gapBands x.val := restrictBands_perm_closed
      (pairRowGap g drop) g.gapBands g.gapBands_distinct closed x
    _ = _ := g.bandPerm_gapMate (pairRowToGap g drop x)



theorem pair_row_counts (i : Nat × Nat) (different : i.1 ≠ i.2)
    (stems : ∀ j : Fin rows.length, rows[j].1 ≠ [])
    (iso : ∀ y : g.Gap, pairRowGap g i y.val ↔ pairRowGap g i (g.gapMate y).val)
    (seed : g.Gap) (a : gapOwner g seed = i.1)
    (b : gapOwner g (g.gapMate seed) = i.2) :
    let D := Subtype (pairRowGap g i)
    let p := pairRowRotation g i
    let bs := pairRowBands g i
    Nat.card (Orbits (faces p bs)) = bs.length ∧ Nat.card D = 2 * bs.length := by
  classical
  let D := Subtype (pairRowGap g i)
  let p := pairRowRotation g i
  let bs := pairRowBands g i
  let x : D := ⟨seed.val,seed.property,Or.inl a⟩
  let y : D := ⟨(g.gapMate seed).val,(g.gapMate seed).property,Or.inr b⟩
  let own (d : D) := (g.rowOwner d.val).val
  have ox : own x = i.1 := a
  have oy : own y = i.2 := b
  have cyc (u v : D) : p.SameCycle u v ↔ own u = own v := by
    change (prune g.turn (pairRowGap g i)).SameCycle u v ↔ _
    rw [project_same g.turn (pairRowGap g i) u v, g.turn_sameCycle_iff_row stems]
    exact Fin.ext_iff
  have join : bandPerm bs x = y := Subtype.ext (pair_row_mate_agrees g i iso x)
  let color (d : D) : Bool := decide (own d = i.1)
  let B : Orbits p → Bool := Quotient.lift color (fun u v same => by
    have eq := (cyc u v).mp same
    simp [color,eq])
  let back (j : Bool) : Orbits p := if j then rep p x else rep p y
  have A : Nat.card (Orbits p) = 2 := by
    have E : Orbits p ≃ Bool := {
      toFun := B, invFun := back
      left_inv := by
        intro z
        induction z using Quotient.inductionOn with
        | _ d =>
          change back (color d) = rep p d
          rcases d.property.2 with yes | no
          · have e : own d = i.1 := yes
            simp only [color,e,decide_true,back,ite_true]
            exact Quotient.sound ((cyc x d).mpr (ox.trans yes.symm))
          · have e : own d ≠ i.1 := fun h => different (h.symm.trans no)
            simp only [color,e,decide_false,back]
            exact Quotient.sound ((cyc y d).mpr (oy.trans no.symm))
      right_inv := by
        intro j
        cases j
        · change color y = false
          simp [color,oy,different.symm]
        · change color x = true
          simp [color,ox] }
    simpa using Nat.card_congr E
  have nd : (used bs).Nodup :=
    restrictBands_distinct (pairRowGap g i) g.gapBands g.gapBands_distinct
  let K : Mix p (bandPerm bs) ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => mrep p (bandPerm bs) x
      left_inv := by
        intro z
        induction z using Quot.inductionOn with
        | _ d =>
          rcases d.property.2 with yes | no
          · exact Quot.sound (Or.inl ((cyc x d).mpr (ox.trans yes.symm)))
          · have qxy : mrep p (bandPerm bs) x = mrep p (bandPerm bs) y :=
              Quot.sound (Or.inr join)
            exact qxy.trans (Quot.sound (Or.inl ((cyc y d).mpr (oy.trans no.symm))))
      right_inv := fun u => by cases u; rfl }
  have C := (Nat.card_congr (bandMix p bs nd)).trans (Nat.card_congr K)
  have e := restrict_gap_zero (pairRowGap g i) g.turn g.gapBands
    g.gapBands_distinct (g.gapBands_zero g.letterBands_zero)
  change deficit (Nat.card (Orbits p)) bs.length (Nat.card (Orbits (faces p bs)))
    (Nat.card (Quotient (comp p bs))) = 0 at e
  have hUnit : Nat.card Unit = 1 := Nat.card_unique
  rw [A,C,hUnit] at e
  unfold deficit at e
  have euler : Nat.card (Orbits (faces p bs)) = bs.length := by omega
  let _ : Fintype D := Fintype.ofFinite D
  have covers (d : D) : d ∈ used bs := by
    by_contra hu
    have fix := unused_band bs d hu
    have old := pair_row_mate_agrees g i iso d
    change (bandPerm bs d).val = _ at old
    rw [fix] at old
    exact g.gap_free (pairRowToGap g i d) (Subtype.ext old.symm)
  have all : (used bs).toFinset = Finset.univ := by
    ext d; simp [covers d]
  have darts : Nat.card D = 2 * bs.length := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← all, List.toFinset_card_of_nodup nd]
    exact band_endpoint_count bs
  exact ⟨euler,darts⟩

theorem pair_row_vertex_agrees (i : Nat × Nat)
    (stems : ∀ j : Fin rows.length, rows[j].1 ≠ [])
    (iso : ∀ y : g.Gap, pairRowGap g i y.val ↔ pairRowGap g i (g.gapMate y).val)
    (x : Subtype (pairRowGap g i)) :
    pairRowToGap g i (faces (pairRowRotation g i) (pairRowBands g i) x) =
      g.GapVertexPerm (pairRowToGap g i x) := by
  apply Subtype.ext
  change (pairRowRotation g i (bandPerm (pairRowBands g i) x)).val = _
  rw [pair_row_rotation_agrees g stems]
  have e : pairRowToGap g i (bandPerm (pairRowBands g i) x) = g.gapMate (pairRowToGap g i x) :=
    Subtype.ext (pair_row_mate_agrees g i iso x)
  rw [e]
  rfl

#print axioms pair_row_counts
#print axioms pair_row_vertex_agrees
end
end AK3.SubVPicture.RingGeneralSix
