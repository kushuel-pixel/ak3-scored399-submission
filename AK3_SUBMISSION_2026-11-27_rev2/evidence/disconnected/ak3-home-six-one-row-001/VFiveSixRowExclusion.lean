import VFiveSixRowFixed

namespace AK3.SubVPicture.RingGeneralSix
open Equiv AK3.SSeven AK3.SSeven.Relative AK3.SSeven.FreeCap
open AK3.SSeven.FreeCap.CapSchedule AK3.SSeven.FreeCap.SewnCount
open AK3.SSeven.FreeCap.BandOverlay AK3.SSeven.FreeCap.BandDeletion
open AK3.SSeven.FreeCap.SlotPrune AK3.SSeven.FreeCap.Switch
open AK3.SSeven.Endpoint.Weighted AK3.SSeven.Endpoint.Weighted.VFiveBoundary
open AK3.CoefficientDiagram AK3.SSeven.Curvature AK3.SubVPicture.Literal
open AK3.SubVPicture.RingPrefix (atCorner)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32000
noncomputable section


def singletonSide (m : Nat) : Bool :=
  (List.finRange 6).any fun i => ([false,true] : List Bool).any fun b =>
    (List.finRange 6).all fun j =>
      decide ((m.testBit j.val = b) ↔ j = i)

def rowFixedFailures (t : FaceTriple) : List (Nat × Fin 2 × ZMod 5) :=
  (chargedContactInputs t).filter (fun entry => singletonSide entry.1)

theorem one_row_failure_count :
    (certifiedTriples.map fun t => (rowFixedFailures t).length).sum = 6 := by
  decide +kernel

def noSingletonContactInputs (t : FaceTriple) : List (Nat × Fin 2 × ZMod 5) :=
  (chargedContactInputs t).filter (fun entry => !singletonSide entry.1)

theorem no_singleton_contact_count :
    (certifiedTriples.map fun t => (noSingletonContactInputs t).length).sum = 91 := by
  decide +kernel

variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)






/-- In a diagram with a crossing, neither side can be a single row. -/
theorem crossing_forbids_singleton_side (H : t ∈ coefficientTriples)
    (two : Nat.card (SixGapComponent g) = 2)
    (r : Subtype g.joinedHitsGap) (hr : sixCrossComponentRegion g r)
    (c : SixGapComponent g) :
    singletonSide (componentMask t s ds g c).val = false := by
  classical
  by_contra! wrong
  have yes : singletonSide (componentMask t s ds g c).val = true := by
    cases h : singletonSide (componentMask t s ds g c).val <;> simp_all
  obtain ⟨i,_,hi⟩ := List.any_eq_true.mp yes
  obtain ⟨b,_,hb⟩ := List.any_eq_true.mp hi
  have pattern (j : Fin 6) : ((componentMask t s ds g c).val.testBit j.val = b) ↔ j = i :=
    of_decide_eq_true (List.all_eq_true.mp hb j (by simp))
  have atRow (x : g.Gap) :
      (componentMask t s ds g c).val.testBit (gapOwner g x) = b ↔ gapOwner g x = i.val := by
    let j := cornerRow t s ds g x
    exact (pattern j).trans Fin.ext_iff
  have closed (x : g.Gap) : gapOwner g x = i.val ↔ gapOwner g (g.gapMate x) = i.val := by
    have move : sixGapComponent g x = sixGapComponent g (g.gapMate x) := Quot.sound (Or.inr rfl)
    have bits :
        (componentMask t s ds g c).val.testBit (gapOwner g x) =
          (componentMask t s ds g c).val.testBit (gapOwner g (g.gapMate x)) :=
      Bool.eq_iff_iff.mpr ((componentMask_gap t s ds g c x).trans
        ((by rw [move] : sixGapComponent g x = c ↔ sixGapComponent g (g.gapMate x) = c).trans
          (componentMask_gap t s ds g c (g.gapMate x)).symm))
    rw [← atRow x,← atRow (g.gapMate x),bits]
  obtain ⟨x,y,ox,oy,ne,fx,fy⟩ :=
    one_row_forces_two_fixed g i.val (literalSix_padded t s ds) closed
      (rowGap t s ds g i) (rowGap_owner t s ds g i)
  exact ne (fixed_gaps_unique_in_component t s ds g H two r hr x y fx fy
    (same_row_same_component t s ds g x y (ox.trans oy.symm)))

/-- Candidate table entries with an isolated row on either side are excluded. -/
theorem actual_crossing_avoids_one_row_failures (H : t ∈ coefficientTriples)
    (two : Nat.card (SixGapComponent g) = 2)
    (r : Subtype g.joinedHitsGap) (hr : sixCrossComponentRegion g r)
    (c : SixGapComponent g) (f : Fin 2) (k : ZMod 5) :
    ((componentMask t s ds g c).val, f, k) ∉ rowFixedFailures t := by
  intro mem
  have check := (List.mem_filter.mp mem).2
  rw [crossing_forbids_singleton_side t s ds g H two r hr c] at check
  exact Bool.noConfusion check

/-- Bridge from arbitrary actual diagrams to the reduced charged catalogue. -/
theorem two_component_reduced_charged_contact (H : t ∈ coefficientTriples)
    (two : Nat.card (SixGapComponent g) = 2) :
    let c := sixGapComponent g (rowGap t s ds g 2)
    let m := (componentMask t s ds g c).val
    exceptionalNegative t m ∨
    ∃ (r : Subtype g.joinedHitsGap) (x : g.Gap),
      sixCrossComponentRegion g r ∧ g.joined x.val = r.val ∧
      sixGapComponent g x = c ∧
      (m, g.factor x.val, orbitResidue t s ds g x) ∈ noSingletonContactInputs t := by
  dsimp only
  rcases two_component_charged_contact t s ds g H two with neutral | ⟨r,x,hr,xr,xc,mem⟩
  · exact Or.inl neutral
  right
  refine ⟨r,x,hr,xr,xc,List.mem_filter.mpr ⟨mem,?_⟩⟩
  rw [crossing_forbids_singleton_side t s ds g H two r hr]; rfl

open Lean in
run_cmd do
  for n in [``actual_crossing_avoids_one_row_failures, ``one_row_failure_count,
      ``no_singleton_contact_count, ``two_component_reduced_charged_contact] do
    unless (← Lean.collectAxioms n).all
      (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "Unexpected axiom in one-row exclusion: {n}"
#print axioms actual_crossing_avoids_one_row_failures
#print axioms one_row_failure_count
#print axioms no_singleton_contact_count
#print axioms two_component_reduced_charged_contact
end
end AK3.SubVPicture.RingGeneralSix
