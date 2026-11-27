import TerminalAssembly

open Lean
open AK3.SSeven
open AK3.SSeven.FreeCap.RawChart

example : yQ ≠ 1 := yQ_ne_one_by_curvature

example : ∀ c : Common,
    c * commonMap (FreeGroup.mk aWord) * c⁻¹ ≠ commonMap (FreeGroup.mk fWord) :=
  common_nonconjugate_by_curvature

run_cmd do
  for n in [``yQ_ne_one_by_curvature, ``common_nonconjugate_by_curvature] do
    let ax ← Lean.collectAxioms n
    unless ax.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "Unexpected axioms in {n}: {ax}"
#print Common
#print commonMap
set_option pp.fullNames true in
#check yQ_ne_one_by_curvature
set_option pp.fullNames true in
#check common_nonconjugate_by_curvature
#print axioms common_nonconjugate_by_curvature
