import VFiveSixDigonLengths

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


def isPairMask (m : Nat) (a b : Fin 6) : Bool :=
  a.val < b.val && ([false,true] : List Bool).any (fun side =>
    (List.finRange 6).all fun j =>
      decide ((m.testBit j.val = side) ↔ j = a ∨ j = b))

def maskPairs (m : Nat) : List (Fin 6 × Fin 6) :=
  (List.finRange 6).flatMap fun a => ((List.finRange 6).filter (isPairMask m a)).map (a, ·)

def matchedLengths (t : FaceTriple) (m : Nat) : List (Fin 6 × Fin 6) :=
  (maskPairs m).filter fun ab => decide ((sixTapeAt t ab.1).length = (sixTapeAt t ab.2).length)


def matchedLengthCases (t : FaceTriple) : List (Nat × Fin 2 × ZMod 5) :=
  (chargedPairSides t).filter fun e => !(matchedLengths t e.1).isEmpty

def lengthFingerprint (t : FaceTriple) : List (Nat × List (Nat × Nat)) :=
  (matchedLengthCases t).map fun e =>
    (e.1, (matchedLengths t e.1).map (fun ab => (ab.1.val,ab.2.val)))

private theorem length_row_0 : lengthFingerprint ((0,false),(1,false),(4,true)) = [] := by decide +kernel
private theorem length_row_1 : lengthFingerprint ((0,false),(2,false),(5,false)) = [] := by decide +kernel
private theorem length_row_2 : lengthFingerprint ((0,false),(2,true),(3,false)) = [] := by decide +kernel
private theorem length_row_3 : lengthFingerprint ((0,true),(1,false),(1,false)) = [] := by decide +kernel
private theorem length_row_4 : lengthFingerprint ((1,true),(1,true),(5,true)) = [] := by decide +kernel
private theorem length_row_5 : lengthFingerprint ((1,true),(3,false),(6,false)) = [] := by decide +kernel
private theorem length_row_6 : lengthFingerprint ((1,true),(4,false),(4,false)) = [(15,[(4,5)])] := by decide +kernel
private theorem length_row_7 : lengthFingerprint ((2,false),(3,true),(4,false)) = [] := by decide +kernel
private theorem length_row_8 : lengthFingerprint ((2,false),(4,true),(6,false)) = [] := by decide +kernel
private theorem length_row_9 : lengthFingerprint ((2,false),(5,false),(6,true)) = [(23,[(3,5)])] := by decide +kernel
private theorem length_row_10 : lengthFingerprint ((2,true),(3,true),(5,false)) = [] := by decide +kernel
private theorem length_row_11 : lengthFingerprint ((2,true),(4,false),(5,true)) = [] := by decide +kernel

theorem digon_length_survivors :
    certifiedTriples.map lengthFingerprint =
      [[], [], [], [], [], [], [(15,[(4,5)])], [], [], [(23,[(3,5)])], [], []] := by
  change [lengthFingerprint ((0,false),(1,false),(4,true)),
     lengthFingerprint ((0,false),(2,false),(5,false)),
     lengthFingerprint ((0,false),(2,true),(3,false)),
     lengthFingerprint ((0,true),(1,false),(1,false)),
     lengthFingerprint ((1,true),(1,true),(5,true)),
     lengthFingerprint ((1,true),(3,false),(6,false)),
     lengthFingerprint ((1,true),(4,false),(4,false)),
     lengthFingerprint ((2,false),(3,true),(4,false)),
     lengthFingerprint ((2,false),(4,true),(6,false)),
     lengthFingerprint ((2,false),(5,false),(6,true)),
     lengthFingerprint ((2,true),(3,true),(5,false)),
     lengthFingerprint ((2,true),(4,false),(5,true))] = _
  rw [length_row_0, length_row_1, length_row_2, length_row_3, length_row_4, length_row_5, length_row_6, length_row_7, length_row_8, length_row_9, length_row_10, length_row_11]

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

/-- The real 2-row side must survive the actual length table, whether
it contains the negative anchor or is the complementary side. -/
theorem actual_digon_pair_passes_length_table (H : t ∈ coefficientTriples)
    (two : Nat.card (SixGapComponent g) = 2)
    (short neg : SixGapComponent g) (a b : Fin 6) (order : a.val < b.val)
    (desc : ∀ x : g.Gap, sixGapComponent g x = short ↔ gapOwner g x = a.val ∨ gapOwner g x = b.val)
    (all : ∀ z, vertexDegree (faces (pairRowRotation g (a.val,b.val))
      (pairRowBands g (a.val,b.val))) z = 2)
    (f : Fin 2) (k : ZMod 5)
    (entry : ((componentMask t s ds g neg).val, f, k) ∈ chargedPairSides t) :
    ((componentMask t s ds g neg).val, f, k) ∈ matchedLengthCases t := by
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
  apply List.mem_filter.mpr
  refine ⟨entry,?_⟩
  cases eq : matchedLengths t m with
  | nil => simp [eq] at good
  | cons hd tl => simp

open Lean in
run_cmd do
  for n in [``actual_digon_pair_passes_length_table,``digon_length_survivors] do
    unless (← Lean.collectAxioms n).all
      (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "Unexpected axiom in matched length test"
#print axioms actual_digon_pair_passes_length_table
#print axioms digon_length_survivors
end
end AK3.SubVPicture.RingGeneralSix
