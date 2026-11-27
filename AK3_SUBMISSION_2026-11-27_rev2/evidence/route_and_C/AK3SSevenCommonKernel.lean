import AK3SSevenKills

namespace AK3.SSeven
open Verify.AtomicSemantics FreeGroup MulOpposite

/-- The common quotient of the original free group, not a quotient of
the seven-sheet comparison words. -/
def RBNorm : Subgroup Verify.F :=
  Subgroup.normalClosure ({mk rWord,mk bWord} : Set Verify.F)

instance rbnormal : RBNorm.Normal := by
  unfold RBNorm
  infer_instance
abbrev Common := Verify.F ⧸ RBNorm
def commonMap : Verify.F →* Common := QuotientGroup.mk' RBNorm

variable {G : Type} [Group G] (y u : G)
variable (Y : y^5=1) (U : u^5=1) (R : ∀ i, evaluate y u (relator i)=1)

include Y U R in
theorem kill_normalRB : RBNorm≤(action y u).ker := by
  apply Subgroup.normalClosure_le_normal
  intro j hj
  change j∈({mk rWord,mk bWord} : Set Verify.F) at hj
  have H : j=mk rWord ∨ j=mk bWord := (Set.mem_insert_iff.mp hj).imp id Set.mem_singleton_iff.mp
  rcases H with rfl|rfl
  · exact MonoidHom.mem_ker.mpr (action_kills_r y u Y U)
  · exact MonoidHom.mem_ker.mpr (action_kills_b y u Y U R)

include Y U R in
def commonAction : Common →* (Equiv.Perm (Sheet×G))ᵐᵒᵖ :=
  QuotientGroup.lift RBNorm (action y u) (kill_normalRB y u Y U R)

open Lean in
run_cmd do
  for n in [``action_kills_r,``action_kills_b,``kill_normalRB,``commonAction] do
    unless (← Lean.collectAxioms n).all (fun a=>[``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError m!"Unexpected axioms in {n}"
end AK3.SSeven
