import AK3EFactorFixture
namespace AK3.SSeven
open Verify.AtomicSemantics
open AK3.EFactor (literal)
def fWord : Word := literal "XyyyxYYYY"
def rWord : Word := literal "xxYYYYYXyyyyy"
def eWord : Word := literal "xxYXy"
def aWord : Word := literal "xyyyxYXyyyyyXYYYxxyyyXXyyyxYYYYYxyXXXyyyxYYYYxYYYxYXyyyyyXYYYxxYYYXyyyXXyyyxYYYYYxyXyyyXyyyyXYYYxxxYXyyyyyXYYYxxYYYYYYxyyyXXyyyxYYYYYxyXXXyyyxYYYYxYYYxYXyyyyyXYYYxxYYYXyyyyyyXXyyyxYYYYYxyXXXyyyxYYYYxYYYxYXyyyyyXYYYxxYYYxyyyXXyyyxYYYYYxyXyyyXyyyyXYYYxxxYXyyyyyXYYYxxYYYXXyyyxYYYYYxyXX"
def bWord : Word := literal "xyyyxYXyyyyyXYYYxxyyyXXyyyxYYYYYxyXXXyyyxYYYYxYYYxYXyyyyyXYYYxxYYYXyyyXXyyyxYYYYYxyXyyyXyyyyXYYYxxxYXyyyyyXYYYxxYYYYYYxyyyXXyyyxYYYYYxyXXXyyyxYYYYxYYYxYXyyyyyXYYYxxYYYXyyyyyyXXyyyxYYYYYxyXXXyyyxYYYYxYYYxYXyyyyyXYYYxxYYYxyyyXXyyyxYYYYYxyXyyyXyyyyXYYYxxxYXyyyyyXYYYxxYYYXXyyyxYYYYYxyXyyyxYXyyyyyXYYYxxyyyXXyyyxYYYYYxyXXXyyyxYYYYxYYYxYXyyyyyXYYYxxYYYXyyyXXyyyxYYYYYxyXyyyXyyyyXYYYxxxYXyyyyyXYYYxxYYYYYY"

def AWord : Word := literal "X" ++ aWord ++ literal "x"
def AstarWord : Word := literal "X" ++ FreeGroup.invRev bWord ++ aWord ++ literal "x"
def inputPair : WordState := (aWord,bWord)
def targetPair : WordState := (fWord,eWord)
def backwardMoves : List Move := [.m0,.m0,.m3,.m0,.m1,.m4,.m3,.m2,.m4,.m11,.m12,.m10,.m11,.m12,.m10,.m11,.m12,.m10,.m11,.m12,.m10,.m11,.m12,.m10,.m11,.m12,.m10,.m7,.m8,.m6,.m7,.m8,.m6,.m7,.m8,.m6,.m1,.m4,.m1,.m3,.m11,.m2,.m7,.m1,.m5,.m1,.m13,.m13,.m13,.m10,.m6,.m0,.m3,.m0,.m1,.m4,.m3,.m3,.m0,.m1,.m5,.m1]
def forwardMoves : List Move := [.m1,.m4,.m1,.m0,.m2,.m2,.m5,.m1,.m0,.m2,.m0,.m7,.m11,.m12,.m12,.m12,.m1,.m4,.m1,.m6,.m3,.m10,.m2,.m1,.m5,.m1,.m7,.m9,.m6,.m7,.m9,.m6,.m7,.m9,.m6,.m11,.m13,.m10,.m11,.m13,.m10,.m11,.m13,.m10,.m11,.m13,.m10,.m11,.m13,.m10,.m11,.m13,.m10,.m5,.m3,.m2,.m5,.m1,.m0,.m2,.m0,.m0]
theorem fixed_route_size : backwardMoves.length=62 ∧ forwardMoves.length=62 := by decide +kernel
theorem exact_inverse : AK3.Class31Route.undo backwardMoves=forwardMoves := by decide +kernel
theorem exact_seed : AK3.Class31Route.S=(fWord,rWord) ∧ AK3.Class31Route.Q=targetPair := by decide +kernel
theorem raw_append (a b : List Move) (s : WordState) : wordRun (a++b) s=wordRun b (wordRun a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons k m ih => exact ih _

open Lean in
run_cmd do
  for n in [``exact_inverse,``fixed_route_size,``exact_seed,``raw_append] do
    unless (← Lean.collectAxioms n).all (fun a=>[``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError m!"Unexpected axioms in {n}"
end AK3.SSeven
