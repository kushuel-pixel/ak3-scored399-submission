import Submission.Connections

namespace Verify.Submission.Scored399Peak22
open AtomicSemantics
open AK3Mod5FixedPointAdapter (originalStart)
open Connections (totalLength ak3)
open EntryExtension (Reach)

def scored399 : GroupState := (Y * X * Y * x * y * x, Y^4 * x^3)
def literalS : GroupState := (X*y^3*x*Y^4, x^2*Y^5*X*y^5)
def bridge44 : List Move := [.m7, .m10, .m5, .m6, .m5, .m6, .m8, .m12, .m0, .m2, .m6, .m1, .m4, .m1, .m9, .m7, .m5, .m12, .m12, .m11, .m5, .m12, .m4, .m10, .m12, .m11, .m5, .m12, .m11, .m5, .m12, .m4, .m10, .m12, .m12, .m12, .m6, .m4, .m13, .m13, .m8, .m8, .m8, .m7]

theorem bridge44_length : bridge44.length = 44 := by decide +kernel
theorem bridge44_reaches : groupRun bridge44 scored399 = literalS := by decide +kernel
theorem bridge44_cap22 : ∀ k ∈ List.range (bridge44.length + 1),
    totalLength (groupRun (bridge44.take k) scored399) ≤ 22 := by decide +kernel
theorem bridge44_attains22 : 22 ∈ (List.range (bridge44.length + 1)).map
    (fun k => totalLength (groupRun (bridge44.take k) scored399)) := by decide +kernel

theorem joins_bridge42_after_10 :
    groupRun (bridge44.take 12) scored399 =
      groupRun (Connections.bridge42.take 10) ak3 := by decide +kernel

theorem same_last32 : bridge44.drop 12 = Connections.bridge42.drop 10 := by
  decide +kernel

def ReachesAtCap (h : Nat) : Prop :=
  ∃ ms : List Move, groupRun ms scored399 = literalS ∧
    ∀ k ∈ List.range (ms.length + 1), totalLength (groupRun (ms.take k) scored399) ≤ h

theorem literalS_length : totalLength literalS = 22 := by decide +kernel

theorem cap_at_least_22 {h : Nat} (hr : ReachesAtCap h) : 22 ≤ h := by
  obtain ⟨ms, endpoint, stays⟩ := hr
  have hl := stays ms.length (List.mem_range.mpr (Nat.lt_succ_self ms.length))
  simpa only [List.take_length, endpoint, literalS_length] using hl

theorem reachesAtCap_iff (h : Nat) : ReachesAtCap h ↔ 22 ≤ h :=
  ⟨cap_at_least_22, fun hh =>
    ⟨bridge44, bridge44_reaches, fun k hk => (bridge44_cap22 k hk).trans hh⟩⟩

#print axioms literalS_length
#print axioms cap_at_least_22
#print axioms reachesAtCap_iff

#print axioms joins_bridge42_after_10
#print axioms same_last32
#print axioms bridge44_length
#print axioms bridge44_reaches
#print axioms bridge44_cap22
#print axioms bridge44_attains22
end Verify.Submission.Scored399Peak22
