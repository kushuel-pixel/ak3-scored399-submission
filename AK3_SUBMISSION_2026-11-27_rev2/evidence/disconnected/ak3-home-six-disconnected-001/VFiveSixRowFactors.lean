import VFiveSixComponentResidue

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
section LiteralSlots

variable {rows : List (Word × Word)} {outer : BoundarySchedule (combine rows)}
  {q : Perm (Pos rows)} {tr : List (Pos rows × Pos rows)} (g : PlanarCore rows outer q tr)

variable (o : Fin rows.length) {w : Tape} (word : rows[o].2 = expand w)

private def rowSlot (j : TapeSlot w) : g.Dart :=
  g.reverseSlot o (Fin.cast (congrArg List.length word.symm) j)

private theorem rowSlot_owner (j : TapeSlot w) : g.rowOwner (rowSlot g o word j) = o := by
  apply Fin.ext
  rw [← g.owner_coord, rowSlot, g.reverseSlot_site]

private theorem rowSlot_offset (j : TapeSlot w) : literalOffset g (rowSlot g o word j) = j.val := by
  have size := congrArg (fun k : Fin rows.length => rows[k].2.length) (rowSlot_owner g o word j)
  unfold literalOffset
  change rows[g.rowOwner (rowSlot g o word j)].2.length = rows[o].2.length at size
  rw [size, rowSlot, g.reverseSlot_site]
  change rows[o].2.length - 1 - (rows[o].2.length - 1 - j.val) = j.val
  have bound : j.val < rows[o].2.length := by rw [word]; exact j.isLt
  omega

private theorem rowSlot_read (j : TapeSlot w) :
    g.read (rowSlot g o word j) = (expand w)[backwardsIndex j] := by
  let k := Fin.cast (congrArg List.length word.symm) j
  change g.read (g.reverseSlot o k) = _
  rw [g.reverseSlot_read]
  have index : (backwardsIndex k).val = (backwardsIndex j).val := by
    change rows[o].2.length - 1 - j.val = (expand w).length - 1 - j.val
    rw [word]
  have h := congrArg (fun v : Word => v[(backwardsIndex k).val]?) word
  change rows[o].2[(backwardsIndex k).val]? = (expand w)[(backwardsIndex k).val]? at h
  rw [show (expand w)[(backwardsIndex k).val]? = (expand w)[(backwardsIndex j).val]?
    from congrArg (fun l : Nat => (expand w)[l]?) index] at h
  simp only [List.getElem?_eq_getElem (backwardsIndex k).isLt,
    List.getElem?_eq_getElem (backwardsIndex j).isLt, Option.some.injEq] at h
  exact h

private theorem rowSlot_turn (j : TapeSlot w) (stem : rows[o].1 ≠ []) :
    g.turn (rowSlot g o word j) = rowSlot g o word (nextOffset j) := by
  unfold rowSlot
  rw [g.reverseSlot_turn _ _ stem]
  apply congrArg (g.reverseSlot o)
  apply Fin.ext
  change (j.val+1) % rows[o].2.length = (j.val+1) % (expand w).length
  rw [word]

private def rowSlotsEquiv : TapeSlot w ≃ {d : g.Dart // g.rowOwner d = o} := by
  let f (j : TapeSlot w) : {d : g.Dart // g.rowOwner d = o} :=
    ⟨rowSlot g o word j, rowSlot_owner g o word j⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro j k eq
    have h := congrArg (fun d : {d : g.Dart // g.rowOwner d = o} => literalOffset g d.val) eq
    change literalOffset g (rowSlot g o word j) = literalOffset g (rowSlot g o word k) at h
    rw [rowSlot_offset, rowSlot_offset] at h
    exact Fin.ext h
  · rintro ⟨d, hd⟩
    have hasSlot (e : g.rowOwner d = o) : ∃ j : Fin rows[o].2.length, g.reverseSlot o j = d := by
      subst o
      exact g.reverseSlot_covers d
    obtain ⟨j, hj⟩ := hasSlot hd
    refine ⟨Fin.cast (congrArg List.length word) j, Subtype.ext ?_⟩
    simpa [f, rowSlot] using hj


include word in
theorem every_literal_row_factor_sum (f : Fin 2) :
    let _ : Fintype {d : g.Dart // g.rowOwner d = o} := Fintype.ofFinite _
    (∑ d : {d : g.Dart // g.rowOwner d = o},
      if g.factor d.val = f then (g.signed d.val : ZMod 5) else 0) = tapeFactorSum w f := by
  dsimp only
  let _ : Fintype {d : g.Dart // g.rowOwner d = o} := Fintype.ofFinite _
  let e := rowSlotsEquiv g o word
  let weight (d : {d : g.Dart // g.rowOwner d = o}) : ZMod 5 :=
    if g.factor d.val = f then (g.signed d.val : ZMod 5) else 0
  change (∑ d, weight d) = tapeFactorSum w f
  rw [← Equiv.sum_comp e weight]
  apply Finset.sum_congr rfl
  intro j _
  have read := rowSlot_read g o word j
  have mem : g.read (rowSlot g o word j) ∈ expand w := read.symm ▸ List.getElem_mem _
  obtain ⟨z,_,hz⟩ := List.mem_flatMap.mp mem
  have positive : (g.read (rowSlot g o word j)).2 = true :=
    congrArg Prod.snd (List.mem_replicate.mp hz).2
  have signed : g.signed (rowSlot g o word j) = 1 := by simp [PlanarCore.signed,positive]
  change (if g.factor (rowSlot g o word j) = f then (g.signed (rowSlot g o word j) : ZMod 5) else 0) = _
  simp [PlanarCore.factor, signed, read]

end LiteralSlots

variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)

def sixTapeAt (i : Fin 6) : Tape :=
  (sixTapes t)[i.val]'(by simp [sixTapes])

theorem sixTapeAt_expanded (i : Fin 6) :
    (literalSix t s ++ discRows ds)[mainIndex t s ds i].2 =
      expand (sixTapeAt t i) := by
  have h : i.val < (literalSix t s).length := by
    simpa [literalSix] using i.isLt
  have eq : (literalSix t s ++ discRows ds)[mainIndex t s ds i] =
      (literalSix t s)[i.val]'h := List.getElem_append_left h
  rw [eq]
  fin_cases i <;> rfl

theorem componentFactorSum_as_rows (c : SixGapComponent g) (f : Fin 2) :
    componentFactorSum t s ds g c f =
      ∑ i : Fin 6, if (componentMask t s ds g c).val.testBit i.val
        then tapeFactorSum (sixTapeAt t i) f else 0 := by
  classical
  let a (d : g.Dart) : Fin 6 := if h : (g.rowOwner d).val < 6 then ⟨_,h⟩ else 0
  let A := ((sixNonauxDarts t s ds g).filter (fun d => chosenDart t s ds g c d = true)).filter
    (fun d => g.factor d = f)
  let weight (d : g.Dart) := (g.signed d : ZMod 5)
  change ∑ d ∈ A, weight d = _
  rw [← Finset.sum_fiberwise A a weight]
  apply Finset.sum_congr rfl
  intro i _
  let o := mainIndex t s ds i
  let bit := (componentMask t s ds g c).val.testBit i.val
  have info (d : g.Dart) (h : d ∈ A) :
      (g.rowOwner d).val < 6 ∧ chosenDart t s ds g c d = true ∧ g.factor d = f := by
    obtain ⟨part,fac⟩ := Finset.mem_filter.mp h
    obtain ⟨nonaux,chosen⟩ := Finset.mem_filter.mp part
    exact ⟨six_nonaux_is_main t s ds g d (Finset.mem_filter.mp nonaux).2,chosen,fac⟩
  have owner (d : g.Dart) (hm : (g.rowOwner d).val < 6) (h : a d = i) :
      g.rowOwner d = o := by
    apply Fin.ext
    have p := congrArg Fin.val h
    simpa [a,hm,o,mainIndex] using p
  change ∑ d ∈ A.filter (fun d => a d = i), weight d =
    if bit then tapeFactorSum (sixTapeAt t i) f else 0
  by_cases on : bit = true
  · have seteq : A.filter (fun d => a d = i) =
        (Finset.univ.filter (fun d : g.Dart => g.rowOwner d = o)).filter (fun d => g.factor d = f) := by
      ext d
      constructor
      · rintro h
        obtain ⟨inA,ai⟩ := Finset.mem_filter.mp h
        have j := info d inA
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,owner d j.1 ai⟩,j.2.2⟩
      · intro h
        obtain ⟨ho,hf⟩ := Finset.mem_filter.mp h
        have e := (Finset.mem_filter.mp ho).2
        have hm : (g.rowOwner d).val < 6 := by rw [e]; exact i.isLt
        have chosen : chosenDart t s ds g c d = true := by
          unfold chosenDart
          rw [e]
          exact on
        have yes : d ∈ sixNonauxDarts t s ds g := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,six_main_dart_not_aux t s ds g d hm⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨yes,chosen⟩,hf⟩,?_⟩
        dsimp [a]
        rw [dite_eq_left hm]
        exact Fin.ext (congrArg (fun x : Fin (literalSix t s ++ discRows ds).length => x.val) e)
    rw [ite_eq_left on,seteq,Finset.sum_filter]
    let _ : Fintype {d : g.Dart // g.rowOwner d = o} := Fintype.ofFinite _
    rw [Finset.sum_subtype _ (p := fun d : g.Dart => g.rowOwner d = o) (by simp)]
    exact every_literal_row_factor_sum g o (sixTapeAt_expanded t s ds i) f
  · have empty : A.filter (fun d => a d = i) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d q
      obtain ⟨inA,ai⟩ := Finset.mem_filter.mp q
      have j := info d inA
      have choose := j.2.1
      unfold chosenDart at choose
      rw [owner d j.1 ai] at choose
      exact on choose
    rw [ite_eq_right on,empty,Finset.sum_empty]

#print axioms componentFactorSum_as_rows
end
end AK3.SubVPicture.RingGeneralSix
