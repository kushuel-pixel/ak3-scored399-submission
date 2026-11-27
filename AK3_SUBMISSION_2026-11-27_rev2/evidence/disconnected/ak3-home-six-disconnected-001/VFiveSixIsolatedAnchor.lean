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
set_option maxHeartbeats 3200000
noncomputable section
variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr) (plus : Fin 2)

local notation "drop" => deletedAnchors plus
local notation "D" => RemainingDart g (drop)

/-- The raw budget is enough for the six-arc cap once the selected
compression is shown to retain every boundary and mark every monogon. -/
theorem isolated_budget_implies_six_arc_cap
    (iso : ∀ y : g.Gap, remainingGap g (drop) y.val ↔
      remainingGap g (drop) (g.gapMate y).val)
    (marks : rawVertex t s ds g plus iso → Prop)
    (budget : Nat.card (Subtype marks) + 2 ≤
      2 * Nat.card (Quotient (comp (remainingRotation g (drop)) (remainingBands g (drop)))))
    (hits : ∀ d, ∃ a : KeptDart (retainByOrbit t s ds g plus iso marks),
      (remainingDartPerms g (drop) iso).forward.SameCycle a.val d)
    (monogon : ∀ a : D, (remainingDartPerms g (drop) iso).vertex a = a →
      markByOrbit t s ds g plus iso marks a) :
    Nat.card (Orbits (finiteFirstReturns (retainByOrbit t s ds g plus iso marks)).compressed.opposite) ≤ 6 := by
  let R := retainByOrbit t s ds g plus iso marks
  let T := (finiteFirstReturns R).compressed
  have small := compressed_marks_le_raw t s ds g plus iso marks
  have components := Nat.card_congr (remaining_compressed_components g (drop) iso R hits)
  change Nat.card (Quotient (dartComponentSetoid T)) =
    Nat.card (Quotient (comp (remainingRotation g (drop)) (remainingBands g (drop)))) at components
  have distinct : (drop).1 ≠ (drop).2 := by
    intro eq
    have h := congrArg Fin.val eq
    have := plus.isLt
    change plus.val = 2 at h
    omega
  have stems := literalSix_padded t s ds
  have mainOnly := auxiliary_no_gap g stems (literalSix_aux t s ds)
  have mainHits := main_has_gaps g stems (literalSix_main t s ds)
  have four := remaining_rotation_four g stems mainOnly mainHits (drop) distinct
  have zero := remaining_literal_euler g stems mainOnly mainHits (drop) distinct
  let E := compressedExceptional g (drop) iso R (markByOrbit t s ds g plus iso marks)
    (markByOrbit_step t s ds g plus iso marks)
  have bound : Nat.card (Subtype E) ≤ Nat.card (Subtype marks) := small
  have joins : Nat.card (Subtype E) + 2 ≤
      2 * Nat.card (Quotient (dartComponentSetoid T)) := by omega
  exact remaining_compressed_arc_cap g (drop) iso (markByOrbit t s ds g plus iso marks)
    (markByOrbit_step t s ds g plus iso marks) monogon four zero hits joins

/-- The positive/negative anchor two-row component is impossible for every one
of the twelve retained signed types. Both edge bounds refer to the
same selected compression in either branch of the shared-region count. -/
theorem six_isolated_anchor_pair_excluded
    (H : t ∈ coefficientTriples)
    (seed : g.Gap) (positive : gapOwner g seed = plus.val)
    (negative : gapOwner g (g.gapMate seed) = 2)
    (iso : ∀ y : g.Gap, remainingGap g (drop) y.val ↔
      remainingGap g (drop) (g.gapMate y).val) :
    False := by
  let P := remainingDartPerms g (drop) iso
  let V := rawVertex t s ds g plus iso
  have close (mark : V → Prop)
      (budget : Nat.card (Subtype mark) + 2 ≤
        2 * Nat.card (Quotient (comp (remainingRotation g (drop)) (remainingBands g (drop)))))
      (mono : ∀ z : D, P.vertex z = z → mark (rep _ z))
      (pair : ∀ z : D, P.vertex (P.vertex z) = z → P.vertex z ≠ z → ¬ mark (rep _ z) →
        survivingWeight t s ds g plus z = -survivingWeight t s ds g plus (P.vertex z)) :
      False := by
    let R := retainByOrbit t s ds g plus iso mark
    have neutral (z : D) (off : ¬ R.keep z) :
        survivingWeight t s ds g plus z = -survivingWeight t s ds g plus (P.vertex z) :=
      pair z (R.skip_two z off) (R.skip_ne z off) (fun h => off (Or.inl h))
    have hits := generic_four_rows_hit t s ds g plus H iso R neutral
    have min := generic_compressed_needs_seven t s ds g plus H iso R neutral
    have max := isolated_budget_implies_six_arc_cap t s ds g plus iso mark budget hits mono
    exact (Nat.not_lt_of_ge max) min
  have vertex_pair (z : D) (twice : P.vertex (P.vertex z) = z) :
      g.GapVertexPerm (asGap g (drop) z) = asGap g (drop) (P.vertex z) ∧
      g.GapVertexPerm (asGap g (drop) (P.vertex z)) = asGap g (drop) z := by
    refine ⟨(full_step t s ds g plus iso z).symm,?_⟩
    have h := (full_step t s ds g plus iso (P.vertex z)).symm
    rw [twice] at h
    exact h
  have gap_distinct (z : D) (ne : P.vertex z ≠ z) :
      asGap g (drop) z ≠ asGap g (drop) (P.vertex z) := by
    intro eq
    exact ne (Subtype.ext (congrArg (fun x : g.Gap => x.val) eq.symm))
  rcases ring_raw_budget_cases t s ds g plus iso seed positive negative with a | ⟨b,_,small⟩
  · apply close (rawGapShared t s ds g plus iso) a
    · exact full_gap_monogon_marked t s ds g plus H iso
    · intro z twice ne off
      have step := vertex_pair z twice
      exact two_weights_of_single_gap t s ds g (asGap g (drop) z)
        (asGap g (drop) (P.vertex z)) step.1 step.2 (gap_distinct z ne) off
  · apply close (sharedFiber (survivingReadRegion t s ds g plus iso)) b
    · exact surviving_monogon_marked t s ds g plus H iso small
    · intro z twice ne off
      have step := vertex_pair z twice
      exact two_weights_of_single_survivor t s ds g plus iso small z
        (P.vertex z) step.1 step.2 (gap_distinct z ne) off

open Lean in
run_cmd do
  unless (← Lean.collectAxioms ``six_isolated_anchor_pair_excluded).all
    (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
    throwError "Unexpected axiom in isolated anchor exclusion"
#print axioms six_isolated_anchor_pair_excluded
end
end AK3.SubVPicture.RingGeneralSix
