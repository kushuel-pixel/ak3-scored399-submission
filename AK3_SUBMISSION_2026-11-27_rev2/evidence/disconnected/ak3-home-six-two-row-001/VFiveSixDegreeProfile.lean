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


/-- Positive degrees with average two and at most one degree-one vertex.
All degrees are two, or there is one degree-one and one degree-three vertex. -/
theorem degree_two_profile {A : Type} [Fintype A] (d : A → Nat)
    (pos : ∀ a, 0 < d a)
    (total : ∑ a, d a = 2 * Fintype.card A)
    (lowUnique : ∀ a b, d a = 1 → d b = 1 → a = b) :
    (∀ a, d a = 2) ∨
      ∃ a b, d a = 1 ∧ d b = 3 ∧ ∀ z, z ≠ a → z ≠ b → d z = 2 := by
  classical
  let L : Finset A := Finset.univ.filter (fun x => d x = 1)
  let e (a : A) := d a - 2
  have calcD (a : A) : d a + (if d a = 1 then 1 else 0) = 2 + e a := by
    have h := pos a
    by_cases q : d a = 1 <;> simp only [q, ite_true, ite_false, e] <;> omega
  have identity : (∑ a : A, (d a + (if d a = 1 then 1 else 0))) =
      ∑ a : A, (2 + e a) := Finset.sum_congr rfl (fun a _ => calcD a)
  have tally : (∑ a : A, if d a = 1 then 1 else 0) = L.card := by
    rw [← Finset.sum_filter]; simp [L]
  have cardL : L.card ≤ 1 := Finset.card_le_one.mpr (by
    intro a ha b hb
    exact lowUnique a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2)
  have excess : (∑ a, e a) = L.card := by
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,total,tally] at identity
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at identity
    omega
  have bound (a : A) : d a ≤ 3 := by
    have le := Finset.single_le_sum (f := e) (fun a _ => Nat.zero_le (e a)) (Finset.mem_univ a)
    rw [excess] at le
    change d a - 2 ≤ L.card at le
    omega
  by_cases one : ∃ a, d a = 1
  · obtain ⟨a,ha⟩ := one
    have ina : a ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ a,ha⟩
    have cap : L.card = 1 := by
      have hp := Finset.card_pos.mpr ⟨a,ina⟩
      omega
    have some : ∃ b, d b = 3 := by
      by_contra! none
      have zero (z : A) : e z = 0 := by
        have h := bound z
        have hn := none z
        change d z - 2 = 0
        omega
      simp [zero,cap] at excess
    obtain ⟨b,hb⟩ := some
    right
    refine ⟨a,b,ha,hb,?_⟩
    intro z za zb
    have notone : d z ≠ 1 := fun h => za (lowUnique z a h ha)
    have notthree : d z ≠ 3 := by
      intro hz
      have le := Finset.sum_le_sum_of_subset_of_nonneg
        (s := ({z,b} : Finset A)) (t := Finset.univ) (f := e)
        (Finset.subset_univ _) (fun y _ _ => Nat.zero_le (e y))
      rw [excess,cap] at le
      simp [Finset.sum_insert,zb,e,hz,hb] at le
    have p := pos z
    have u := bound z
    omega
  · left
    have empty : L = ∅ := by
      ext a; simp [L]; exact fun h => one ⟨a,h⟩
    intro a
    have le := Finset.single_le_sum (f := e) (fun a _ => Nat.zero_le (e a)) (Finset.mem_univ a)
    rw [excess,empty,Finset.card_empty] at le
    change d a - 2 ≤ 0 at le
    have p := pos a
    have n : d a ≠ 1 := fun h => one ⟨a,h⟩
    omega

def vertexDegree {D : Type} [Finite D] (v : Perm D) (o : Orbits v) : Nat :=
  Nat.card {x : D // rep v x = o}

theorem permutation_degree_two_profile {D : Type} [Finite D] (v : Perm D)
    (balanced : Nat.card D = 2 * Nat.card (Orbits v))
    (unique : ∀ x y : D, v x = x → v y = y → x = y) :
    (∀ a, vertexDegree v a = 2) ∨
      ∃ a b, vertexDegree v a = 1 ∧ vertexDegree v b = 3 ∧
        ∀ z, z ≠ a → z ≠ b → vertexDegree v z = 2 := by
  classical
  let _ : Fintype (Orbits v) := Fintype.ofFinite _
  let d := vertexDegree v
  have total : (∑ o : Orbits v, d o) = 2 * Fintype.card (Orbits v) := by
    rw [← Nat.card_eq_fintype_card, ← balanced, ← Nat.card_congr (Equiv.sigmaFiberEquiv (rep v)),
      Nat.card_sigma]
    rfl
  have pos (o : Orbits v) : 0 < d o := by
    induction o using Quotient.inductionOn with
    | _ x => exact Finite.card_pos_iff.mpr ⟨⟨x,rfl⟩⟩
  have lowUnique (a b : Orbits v) (ha : d a = 1) (hb : d b = 1) : a = b := by
    induction a using Quotient.inductionOn with
    | _ x =>
      induction b using Quotient.inductionOn with
      | _ y =>
        have fixed (u : D) (small : d (rep v u) = 1) : v u = u := by
          let X := {p : D // rep v p = rep v u}
          let _ : Fintype X := Fintype.ofFinite _
          have hn : Fintype.card X ≤ 1 := by
            rw [← Nat.card_eq_fintype_card]
            exact small.le
          let inst : Subsingleton X := Fintype.card_le_one_iff_subsingleton.mp hn
          exact congrArg Subtype.val (inst.elim
            ⟨v u,Quotient.sound (Perm.SameCycle.refl v u).apply_left⟩ ⟨u,rfl⟩)
        exact congrArg (rep v) (unique x y (fixed x ha) (fixed y hb))
  exact degree_two_profile d pos total lowUnique

#print axioms permutation_degree_two_profile
end
end AK3.SubVPicture.RingGeneralSix
