import VFiveSixDigonMismatch

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


/-- The counter-rotating tag recurrence reads every possible first tag
at one fixed reverse phase. -/
theorem counterrotation_phase (L : Nat) (positive : 0 < L) (A B : Nat → Nat)
    (aBound : ∀ n, A n < L) (bBound : ∀ n, B n < L)
    (aStep : ∀ n, A (n+1)+1 ≡ A n [MOD L])
    (bStep : ∀ n, B n+1 ≡ B (n+1) [MOD L]) :
    ∃ phase < L, ∀ j < L, ∃ n, A n = j ∧ B n = (phase+L-j) % L := by
  let phase := (A 0+B 0) % L
  have sum (n : Nat) : A n+B n ≡ phase [MOD L] := by
    induction n with
    | zero => exact (Nat.mod_modEq _ _).symm
    | succ n ih =>
      have forward : A (n+1)+B (n+1) ≡ A n+B n [MOD L] := by
        have e := (Nat.ModEq.refl (A (n+1))).add (bStep n).symm
        have f := (aStep n).add (Nat.ModEq.refl (B n))
        exact e.trans (by simpa only [Nat.add_assoc,Nat.add_comm 1 (B n)] using f)
      exact forward.trans ih
  have offset (n : Nat) : A n+n ≡ A 0 [MOD L] := by
    induction n with
    | zero => simp [Nat.ModEq]
    | succ n ih =>
      have e := (aStep n).add (Nat.ModEq.refl n)
      have step : A (n+1)+(n+1) ≡ A n+n [MOD L] := by
        simpa only [Nat.add_assoc,Nat.add_comm 1 n,Nat.succ_eq_add_one] using e
      exact step.trans ih
  refine ⟨phase,Nat.mod_lt _ positive,fun j hj => ?_⟩
  let n := A 0+L-j
  have nj : j+n = A 0+L := by dsimp [n]; omega
  have addL (x : Nat) : x+L ≡ x [MOD L] := by
    change (x+L)%L = x%L
    exact Nat.add_mod_right _ _
  have eqj : A n ≡ j [MOD L] :=
    Nat.ModEq.add_right_cancel (Nat.ModEq.refl n)
      ((offset n).trans (by rw [nj]; exact (addL _).symm))
  have ex : A n = j := by
    change A n % L = j % L at eqj
    rwa [Nat.mod_eq_of_lt (aBound n),Nat.mod_eq_of_lt hj] at eqj
  refine ⟨n,ex,?_⟩
  have s := sum n
  rw [ex] at s
  have rem : j+(phase+L-j) = phase+L := by omega
  have eqb : B n ≡ phase+L-j [MOD L] :=
    Nat.ModEq.add_left_cancel (Nat.ModEq.refl j)
      (s.trans (by rw [rem]; exact (addL _).symm))
  change B n % L = _ at eqb
  rwa [Nat.mod_eq_of_lt (bBound n)] at eqb

def badAt (u v : Tape) (phase j : Nat) : Bool :=
  ((atCorner u j).2 + (atCorner v ((phase+u.length-j)%u.length)).2) % 5 != 0

def twoBadAt (u v : Tape) (phase : Nat) : Bool :=
  match (List.range u.length).filter (badAt u v phase) with
  | i::j::_ => i != j
  | _ => false

def reverseRejected (u v : Tape) : Bool :=
  (List.range u.length).all fun phase => digonWrongFactor u v phase || twoBadAt u v phase

theorem reject_survivorA :
    reverseRejected (sixTapeAt ((1,true),(4,false),(4,false)) 4)
      (sixTapeAt ((1,true),(4,false),(4,false)) 5) = true := by decide +kernel

theorem reject_survivorB :
    reverseRejected (sixTapeAt ((2,false),(5,false),(6,true)) 3)
      (sixTapeAt ((2,false),(5,false),(6,true)) 5) = true := by decide +kernel

theorem two_bad_witness {u v : Tape} {phase : Nat} (yes : twoBadAt u v phase = true) :
    ∃ j k, j < u.length ∧ k < u.length ∧ j ≠ k ∧
      badAt u v phase j = true ∧ badAt u v phase k = true := by
  unfold twoBadAt at yes
  split at yes
  · rename_i j k rest eq
    have mj : j ∈ (List.range u.length).filter (badAt u v phase) := by rw [eq]; simp
    have mk : k ∈ (List.range u.length).filter (badAt u v phase) := by rw [eq]; simp
    obtain ⟨jrange,jbad⟩ := List.mem_filter.mp mj
    obtain ⟨krange,kbad⟩ := List.mem_filter.mp mk
    refine ⟨j,k,List.mem_range.mp jrange,List.mem_range.mp krange,?_,jbad,kbad⟩
    intro same
    simp [same] at yes
  · contradiction

#print axioms counterrotation_phase
#print axioms reject_survivorA
#print axioms reject_survivorB
#print axioms two_bad_witness
end
end AK3.SubVPicture.RingGeneralSix
