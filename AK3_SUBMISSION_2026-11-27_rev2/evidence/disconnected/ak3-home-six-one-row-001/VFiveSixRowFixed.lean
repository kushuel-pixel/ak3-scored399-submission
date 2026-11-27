import VFiveSixRowPlanar

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


section Degree
variable {D : Type} [Finite D]

/-- If a finite permutation has at most one fixed point, each orbit
except for at most one accounts for at least two distinct darts. -/
theorem twice_orbits_le_of_fixed_unique (v : Perm D) (seed : D)
    (unique : ∀ x y : D, v x = x → v y = y → x = y) :
    2 * Nat.card (Orbits v) ≤ Nat.card D + 1 := by
  classical
  let _ : Fintype (Orbits v) := Fintype.ofFinite _
  let deg (o : Orbits v) := Nat.card {x : D // rep v x = o}
  have degrees : (∑ o : Orbits v, deg o) = Nat.card D := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (rep v)),Nat.card_sigma]
  have select : ∃ a : D, ∀ x : D, v x = x → x = a := by
    by_cases found : ∃ x, v x = x
    · obtain ⟨a,h⟩ := found
      exact ⟨a,fun x hx => unique x a hx h⟩
    · exact ⟨seed,fun x hx => (found ⟨x,hx⟩).elim⟩
  obtain ⟨a,ha⟩ := select
  have lower (o : Orbits v) : 2 ≤ deg o + (if o = rep v a then 1 else 0) := by
    induction o using Quotient.inductionOn with
    | _ x =>
      change 2 ≤ deg (rep v x) + (if rep v x = rep v a then 1 else 0)
      by_cases e : rep v x = rep v a
      · rw [ite_eq_left e]
        have pos : 0 < deg (rep v x) := Finite.card_pos_iff.mpr ⟨⟨x,rfl⟩⟩
        omega
      · rw [ite_eq_right e, Nat.add_zero]
        have nx : v x ≠ x := fun h => e (congrArg (rep v) (ha x h))
        let f : Bool → {y : D // rep v y = rep v x}
          | false => ⟨x,rfl⟩
          | true => ⟨v x,Quotient.sound (Perm.SameCycle.refl v x).apply_left⟩
        have inj : Function.Injective f := by
          intro b c h
          cases b <;> cases c
          · rfl
          · exact (nx (congrArg Subtype.val h).symm).elim
          · exact (nx (congrArg Subtype.val h)).elim
          · rfl
        simpa [deg] using Nat.card_le_card_of_injective f inj
  have total := Finset.sum_le_sum (s := (Finset.univ : Finset (Orbits v))) (fun o _ => lower o)
  simpa [Finset.sum_add_distrib, degrees, ← Nat.card_eq_fintype_card, Nat.mul_comm] using total
end Degree

variable {rows : List (Word × Word)}
  {outer : BoundarySchedule (combine rows)}
  {q : Perm (Pos rows)} {tr : List (Pos rows × Pos rows)}
  (g : PlanarCore rows outer q tr)



/-- An isolated planar one-row component has at least two fixed vertex corners. -/
theorem one_row_forces_two_fixed (i : Nat)
    (stems : ∀ j : Fin rows.length, rows[j].1 ≠ [])
    (iso : ∀ x : g.Gap, gapOwner g x = i ↔ gapOwner g (g.gapMate x) = i)
    (seed : g.Gap) (on : gapOwner g seed = i) :
    ∃ x y : g.Gap, gapOwner g x = i ∧ gapOwner g y = i ∧ x ≠ y ∧
      g.GapVertexPerm x = x ∧ g.GapVertexPerm y = y := by
  classical
  let D := Subtype (oneRowGap g i)
  let p := oneRowRotation g i
  let bands := oneRowBands g i
  let v := faces p bands
  let z : D := ⟨seed.val,seed.property,on⟩
  let view := oneRowToGap g i
  have isolated (x : g.Gap) : oneRowGap g i x.val ↔ oneRowGap g i (g.gapMate x).val := by
    exact ⟨fun h => ⟨(g.gapMate x).property,(iso x).mp h.2⟩,
      fun h => ⟨x.property,(iso x).mpr h.2⟩⟩
  have vertex (x : D) : view (v x) = g.GapVertexPerm (view x) := by
    apply Subtype.ext
    change (p (bandPerm bands x)).val = _
    rw [one_row_rotation_agrees g stems]
    have e : view (bandPerm bands x) = g.gapMate (view x) :=
      Subtype.ext (one_row_mate_agrees g i isolated x)
    change (g.rotationOnGaps (view (bandPerm bands x))).val = _
    rw [e]
    rfl
  let _ : Fintype D := Fintype.ofFinite D
  have nd : (used bands).Nodup :=
    restrictBands_distinct (oneRowGap g i) g.gapBands g.gapBands_distinct
  have covers (x : D) : x ∈ used bands := by
    by_contra hu
    have fix := unused_band bands x hu
    have old := one_row_mate_agrees g i isolated x
    change (bandPerm bands x).val = _ at old
    rw [fix] at old
    exact g.gap_free (view x) (Subtype.ext old.symm)
  have all : (used bands).toFinset = Finset.univ := by
    ext d; simp [covers d]
  have darts : Nat.card D = 2 * bands.length := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← all, List.toFinset_card_of_nodup nd]
    exact band_endpoint_count bands
  have euler : Nat.card (Orbits v) = bands.length + 1 := one_row_planar_counts g i stems seed on
  by_contra! none
  have unique (x y : D) (hx : v x = x) (hy : v y = y) : x = y := by
    have fx : g.GapVertexPerm (view x) = view x := (vertex x).symm.trans (congrArg view hx)
    have fy : g.GapVertexPerm (view y) = view y := (vertex y).symm.trans (congrArg view hy)
    by_contra ne
    exact none (view x) (view y) x.property.2 y.property.2
      (fun e => ne (Subtype.ext (congrArg (fun z : g.Gap => z.val) e))) fx fy
  have bound := twice_orbits_le_of_fixed_unique v z unique
  change 2 * Nat.card (Orbits v) ≤ Nat.card D + 1 at bound
  rw [euler,darts] at bound
  omega

open Lean in
run_cmd do
  unless (← Lean.collectAxioms ``one_row_forces_two_fixed).all
    (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
    throwError "Unexpected axiom in planar one-row count"
#print axioms one_row_forces_two_fixed
end
end AK3.SubVPicture.RingGeneralSix
