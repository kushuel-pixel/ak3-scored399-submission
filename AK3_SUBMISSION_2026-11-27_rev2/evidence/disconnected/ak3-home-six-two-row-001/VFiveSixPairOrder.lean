import VFiveSixDegreeProfile

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


theorem degree_two_forces_double_return {D : Type} [Finite D] (v : Perm D) (x : D)
    (degree : vertexDegree v (rep v x) = 2) : v (v x) = x := by
  classical
  by_contra h
  have f : v x ≠ x := fun e => h (by rw [e,e])
  have g : v (v x) ≠ v x := fun e => f (v.injective e)
  let Z := {y : D // rep v y = rep v x}
  let pick : Fin 3 → Z := ![⟨x,rfl⟩,
    ⟨v x,Quotient.sound (Perm.SameCycle.refl v x).apply_left⟩,
    ⟨v (v x),Quotient.sound (Perm.SameCycle.refl v x).apply_left.apply_left⟩]
  have inj : Function.Injective pick := by
    intro a b eq
    have z := congrArg (fun w : Z => w.val) eq
    fin_cases a <;> fin_cases b <;>
      first | rfl | exact (f z).elim | exact (f z.symm).elim |
        exact (g z).elim | exact (g z.symm).elim |
        exact (h z).elim | exact (h z.symm).elim
  have cap := Nat.card_le_card_of_injective pick inj
  change Nat.card (Fin 3) ≤ vertexDegree v (rep v x) at cap
  rw [degree] at cap
  simp at cap

theorem return_two_reverses_step {D : Type} (r m : Perm D)
    (inv : Function.Involutive m) (double : ∀ x, (r*m) ((r*m) x) = x) (z : D) :
    m (r z) = r.symm (m z) := by
  apply r.injective
  simpa only [Perm.mul_apply,inv z,apply_symm_apply] using double (m z)

/-- If the vertex permutation returns after two steps, the edge pairing
reverses the order of the two boundary cycles. -/
theorem return_two_reverses_rows {D : Type} [Finite D] (r m : Perm D)
    (inv : Function.Involutive m) (double : ∀ x, (r*m) ((r*m) x) = x) (x y : D)
    (same : r.SameCycle x y) : r.SameCycle (m x) (m y) := by
  have project (z : D) :
      rep r (m (r z)) = rep r (m z) := by
    rw [return_two_reverses_step r m inv double]
    apply Quotient.sound
    have step : r.SameCycle (r.symm (m z)) (r (r.symm (m z))) :=
      (Perm.SameCycle.refl r _).apply_right
    rwa [apply_symm_apply] at step
  exact Quotient.exact (same_from_step (p := r) (f := fun z => rep r (m z)) (fun z => (project z).symm) same)

open Lean in
run_cmd do
  for n in [``degree_two_forces_double_return,``return_two_reverses_rows] do
    unless (← Lean.collectAxioms n).all
      (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "Unexpected axiom in two-row order"
#print axioms degree_two_forces_double_return
#print axioms return_two_reverses_step
#print axioms return_two_reverses_rows
end
end AK3.SubVPicture.RingGeneralSix
