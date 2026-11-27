import VFiveSixDigonReverseActual

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


def fingerprintRejects (t : FaceTriple) (l : List (Nat × List (Nat × Nat))) : Bool :=
  l.all fun e => e.2.all fun (a,b) =>
    if ha : a < 6 then
      if hb : b < 6 then reverseRejected (sixTapeAt t ⟨a,ha⟩) (sixTapeAt t ⟨b,hb⟩)
      else false
    else false

theorem verified_fingerprints_reject :
    ((certifiedTriples.zip (certifiedTriples.map lengthFingerprint)).all
      (fun p => fingerprintRejects p.1 p.2)) = true := by
  rw [digon_length_survivors]
  decide +kernel

private theorem mem_zip_map_self {A B : Type} (xs : List A) (f : A → B)
    (a : A) (mem : a ∈ xs) : (a,f a) ∈ xs.zip (xs.map f) := by
  induction xs with
  | nil => simp at mem
  | cons x xs ih =>
    rcases List.mem_cons.mp mem with rfl|tail
    · simp
    · exact List.mem_cons_of_mem _ (ih tail)

variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)







/-- With exactly two components, any two components other than c agree. -/
private theorem outside_equal (two : Nat.card (SixGapComponent g) = 2)
    (c x y : SixGapComponent g) (hx : x ≠ c) (hy : y ≠ c) : x = y := by
  classical
  by_contra xy
  let _ : Fintype (SixGapComponent g) := Fintype.ofFinite _
  have n : ({x,y,c} : Finset (SixGapComponent g)).card = 3 := by simp [xy,hx,hy]
  have cap := Finset.card_le_univ ({x,y,c} : Finset (SixGapComponent g))
  rw [n, ← Nat.card_eq_fintype_card, two] at cap
  omega

theorem actual_digon_pair_in_length_fingerprint (H : t ∈ coefficientTriples)
    (two : Nat.card (SixGapComponent g) = 2)
    (short neg : SixGapComponent g) (a b : Fin 6) (order : a.val < b.val)
    (desc : ∀ x : g.Gap, sixGapComponent g x = short ↔ gapOwner g x = a.val ∨ gapOwner g x = b.val)
    (all : ∀ z, vertexDegree (faces (pairRowRotation g (a.val,b.val))
      (pairRowBands g (a.val,b.val))) z = 2)
    (f : Fin 2) (k : ZMod 5)
    (entry : ((componentMask t s ds g neg).val, f, k) ∈ chargedPairSides t) :
    ∃ l, ((componentMask t s ds g neg).val, l) ∈ lengthFingerprint t ∧ (a.val,b.val) ∈ l := by
  classical
  let m := (componentMask t s ds g neg).val
  have ne : a ≠ b := fun e => (Nat.ne_of_lt order) (congrArg Fin.val e)
  have len := actual_digon_pair_lengths t s ds g H short a b ne desc all
  let truth : Bool := decide (short = neg)
  have classify (j : Fin 6) : (m.testBit j.val = truth) ↔ j = a ∨ j = b := by
    let x := rowGap t s ds g j
    have d : sixGapComponent g x = short ↔ j = a ∨ j = b := by
      rw [desc x,rowGap_owner t s ds g j]
      exact or_congr Fin.ext_iff.symm Fin.ext_iff.symm
    by_cases same : short = neg
    · have ht : truth = true := decide_eq_true same
      rw [ht]
      exact (componentMask_spec t s ds g neg j).trans (same ▸ d)
    · have ht : truth = false := decide_eq_false same
      rw [ht]
      have bits : m.testBit j.val = false ↔ sixGapComponent g x ≠ neg := by
        change m.testBit j.val = false ↔ sixGapComponent g (rowGap t s ds g j) ≠ neg
        have e := (componentMask_spec t s ds g neg j).not
        change (¬m.testBit j.val = true) ↔ _ at e
        cases h : m.testBit j.val <;> simp_all
      apply bits.trans
      refine Iff.trans ⟨fun off => outside_equal t s ds g two neg _ _ off same,
        fun e bad => same (e.symm.trans bad)⟩ d
  have mark : isPairMask m a b = true := by
    have inside : ([false,true] : List Bool).any (fun side =>
      (List.finRange 6).all fun j =>
        decide ((m.testBit j.val = side) ↔ j = a ∨ j = b)) = true := by
      apply List.any_eq_true.mpr
      refine ⟨truth,by cases truth <;> simp, ?_⟩
      exact List.all_eq_true.mpr (fun j _ => decide_eq_true (classify j))
    change (decide (a.val < b.val) && ([false,true] : List Bool).any (fun side =>
      (List.finRange 6).all fun j =>
        decide ((m.testBit j.val = side) ↔ j = a ∨ j = b))) = true
    rw [inside, decide_eq_true order]
    rfl
  have pairMem : (a,b) ∈ maskPairs m := by
    apply List.mem_flatMap.mpr
    refine ⟨a,by simp,List.mem_map.mpr ⟨b,List.mem_filter.mpr ⟨by simp,mark⟩,rfl⟩⟩
  have good : (a,b) ∈ matchedLengths t m := List.mem_filter.mpr ⟨pairMem,decide_eq_true len⟩
  let p := (m,f,k)
  have selected : p ∈ matchedLengthCases t := by
    apply List.mem_filter.mpr
    refine ⟨entry,?_⟩
    cases eq : matchedLengths t m with
    | nil => simp [eq] at good
    | cons hd tl => simp
  refine ⟨_,List.mem_map.mpr ⟨p,selected,rfl⟩,?_⟩
  exact List.mem_map.mpr ⟨(a,b),good,rfl⟩


/-- All 68 charged 2+4 allocations are closed in the all-degree-two
mode. This applies to either orientation of the two-row side. -/
theorem charged_two_row_all_degree_two_excluded (H : t ∈ coefficientTriples)
    (two : Nat.card (SixGapComponent g) = 2)
    (r : Subtype g.joinedHitsGap) (hr : sixCrossComponentRegion g r)
    (short neg : SixGapComponent g) (a b : Fin 6) (order : a.val < b.val)
    (desc : ∀ x : g.Gap, sixGapComponent g x = short ↔ gapOwner g x = a.val ∨ gapOwner g x = b.val)
    (all : ∀ z, vertexDegree (faces (pairRowRotation g (a.val,b.val))
      (pairRowBands g (a.val,b.val))) z = 2)
    (f : Fin 2) (k : ZMod 5)
    (entry : ((componentMask t s ds g neg).val, f, k) ∈ chargedPairSides t) : False := by
  have listed : t ∈ certifiedTriples := roster_binding.symm ▸ H
  have each := List.all_eq_true.mp verified_fingerprints_reject (t,lengthFingerprint t)
    (mem_zip_map_self certifiedTriples lengthFingerprint t listed)
  obtain ⟨l,chosen,pair⟩ :=
    actual_digon_pair_in_length_fingerprint t s ds g H two short neg a b order desc all f k entry
  have row := List.all_eq_true.mp each _ chosen
  have yes := List.all_eq_true.mp row _ pair
  change (if ha : a.val < 6 then if hb : b.val < 6 then
    reverseRejected (sixTapeAt t ⟨a.val,ha⟩) (sixTapeAt t ⟨b.val,hb⟩)
    else false else false) = true at yes
  simp only [dite_eq_left a.isLt,dite_eq_left b.isLt] at yes
  exact actual_digon_reverse_rejected t s ds g H two r hr short a b
    (fun eq => (Nat.ne_of_lt order) (congrArg Fin.val eq)) desc all yes

open Lean in
run_cmd do
  for n in [``verified_fingerprints_reject,``charged_two_row_all_degree_two_excluded] do
    unless (← Lean.collectAxioms n).all
      (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "Unexpected axiom in full charged digon closure"
#print axioms verified_fingerprints_reject
#print axioms charged_two_row_all_degree_two_excluded
end
end AK3.SubVPicture.RingGeneralSix
