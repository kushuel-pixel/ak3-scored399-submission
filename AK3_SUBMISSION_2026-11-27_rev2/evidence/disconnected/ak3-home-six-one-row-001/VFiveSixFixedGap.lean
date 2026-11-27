import VFiveSixOneCorner
import VFiveSixContactOrder

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

variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)





/-- A fixed gap-vertex corner cannot belong to a coefficient region
containing only that one gap-vertex orbit. -/
theorem fixed_gap_is_shared (H : t ∈ coefficientTriples) (x : g.Gap)
    (fix : g.GapVertexPerm x = x) :
    sharedFiber g.gapVertexJoined (rep g.GapVertexPerm x) := by
  classical
  by_contra off
  let S := sixNonauxDarts t s ds g
  have eq : S.filter (fun d => g.joined d = g.joined x.val) =
      S.filter (fun d => rep g.chartVertexPerm d = rep g.chartVertexPerm x.val) := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd,h⟩
      exact ⟨hd,Quotient.sound ((nonaux_same_chart_of_single_gap t s ds g x off hd h).symm)⟩
    · rintro ⟨hd,h⟩
      exact ⟨hd,congrArg g.chartVertexJoined h⟩
  have zero := nonaux_joined_residue_zero t s ds g (g.joined x.val)
  change (∑ d ∈ S.filter (fun d => g.joined d = g.joined x.val), (g.signed d : ZMod 5)) = 0 at zero
  rw [eq] at zero
  change orbitResidue t s ds g x = 0 at zero
  rw [fixed_contact_has_one_corner t s ds g H x fix] at zero
  let i := cornerRow t s ds g x
  let j := cornerTag t s ds g x
  have small := (literal_corner_weight t s ds g H x).1
  have bound := (six_tape_facts t H i).exponent ⟨j,small⟩
  have dvd : 5 ∣ (atCorner (sixTapeAt t i) j).2 := (ZMod.natCast_eq_zero_iff _ _).mp zero
  obtain ⟨n,hn⟩ := dvd
  change 0 < (atCorner (sixTapeAt t i) j).2 ∧ (atCorner (sixTapeAt t i) j).2 < 5 at bound
  omega

/-- Distinct fixed points in one component cannot both use the only
crossing, since each side contributes just one gap-vertex orbit. -/
theorem fixed_gaps_unique_in_component (H : t ∈ coefficientTriples)
    (two : Nat.card (SixGapComponent g) = 2)
    (r : Subtype g.joinedHitsGap) (hr : sixCrossComponentRegion g r)
    (x y : g.Gap) (cx : g.GapVertexPerm x = x) (cy : g.GapVertexPerm y = y)
    (same : sixGapComponent g x = sixGapComponent g y) : x = y := by
  obtain ⟨a,b,_,_,diff,exactly⟩ := two_components_crossing_spends_budget g two hr
  have hx := (exactly _).mp (fixed_gap_is_shared t s ds g H x cx)
  have hy := (exactly _).mp (fixed_gap_is_shared t s ds g H y cy)
  have orbit : rep g.GapVertexPerm x = rep g.GapVertexPerm y := by
    rcases hx with hx|hx <;> rcases hy with hy|hy
    · exact hx.trans hy.symm
    · exact (diff ((congrArg (sixGapVertexComponent g) hx).symm.trans
        (same.trans (congrArg (sixGapVertexComponent g) hy)))).elim
    · exact (diff ((congrArg (sixGapVertexComponent g) hy).symm.trans
        (same.symm.trans (congrArg (sixGapVertexComponent g) hx)))).elim
    · exact hx.trans hy.symm
  have cyc : g.GapVertexPerm.SameCycle x y := Quotient.exact orbit
  obtain ⟨n,hn⟩ := cyc.exists_nat_pow_eq
  have step (n : Nat) : (g.GapVertexPerm ^ n) x = x := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',Perm.mul_apply,ih,cx]
  exact (step n).symm.trans hn

open Lean in
run_cmd do
  unless (← Lean.collectAxioms ``fixed_gaps_unique_in_component).all
    (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
    throwError "Unexpected axiom in fixed gap uniqueness"
#print axioms fixed_gap_is_shared
#print axioms fixed_gaps_unique_in_component
end
end AK3.SubVPicture.RingGeneralSix
