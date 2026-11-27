import VFiveSixContactLiteral
import VFiveSixOppositeContact

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


/-- A one-corner contact must read an entry on its side of the six-row
allocation, in the correct factor, with the required value. -/
def oneCornerAllows (t : FaceTriple) (m : Nat) (side : Bool) (f : Fin 2) (k : ZMod 5) : Bool :=
  (List.finRange 6).any fun i =>
    (m.testBit i.val == side) && ((List.range (sixTapeAt t i).length).any fun j =>
      decide ((atCorner (sixTapeAt t i) j).1 = f) &&
      decide (((atCorner (sixTapeAt t i) j).2 : ZMod 5) = k))

def oneCornerFailures (t : FaceTriple) : List (Nat × Fin 2 × ZMod 5) :=
  (chargedContactInputs t).filter fun z =>
    !(oneCornerAllows t z.1 true z.2.1 z.2.2 && oneCornerAllows t z.1 false z.2.1 (-z.2.2))

/-- The values alone cannot eliminate any row allocation, even when
both contacts are restricted to one corner. No existence is asserted. -/
theorem one_corner_failures_empty :
    certifiedTriples.map oneCornerFailures = List.replicate 12 [] := by
  decide +kernel

private theorem true_pair {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by rw [ha,hb]; rfl

variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)





theorem fixed_contact_has_one_corner (H : t ∈ coefficientTriples) (x : g.Gap)
    (fixed : g.GapVertexPerm x = x) :
    orbitResidue t s ds g x =
      ((atCorner (sixTapeAt t (cornerRow t s ds g x)) (cornerTag t s ds g x)).2 : ZMod 5) := by
  classical
  rw [orbitResidue_eq_literal_sum t s ds g H x]
  let a : {y : g.Gap // g.GapVertexPerm.SameCycle x y} :=
    ⟨x, Perm.SameCycle.refl _ _⟩
  rw [Finset.sum_eq_single a]
  · intro b _ ne
    obtain ⟨n,hn⟩ := b.property.exists_nat_pow_eq
    have eq : ∀ n : Nat, (g.GapVertexPerm ^ n) x = x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', Perm.mul_apply, ih, fixed]
    exact (ne (Subtype.ext (hn.symm.trans (eq n)))).elim
  · intro bad
    exact (bad (Finset.mem_univ a)).elim

theorem fixed_contact_passes_one_corner (H : t ∈ coefficientTriples) (x : g.Gap)
    (fixed : g.GapVertexPerm x = x) (c : SixGapComponent g) (side : Bool)
    (on : (componentMask t s ds g c).val.testBit (gapOwner g x) = side) :
    oneCornerAllows t (componentMask t s ds g c).val side
      (g.factor x.val) (orbitResidue t s ds g x) = true := by
  let i := cornerRow t s ds g x
  let j := cornerTag t s ds g x
  obtain ⟨small,factor,_⟩ := literal_corner_weight t s ds g H x
  apply List.any_eq_true.mpr
  refine ⟨i, by simp, ?_⟩
  apply true_pair
  · exact beq_iff_eq.mpr on
  ·
    apply List.any_eq_true.mpr
    refine ⟨j,List.mem_range.mpr small,true_pair (decide_eq_true factor) ?_⟩
    exact decide_eq_true (fixed_contact_has_one_corner t s ds g H x fixed).symm

/-- The row allocation and the opposite coefficients are checked at the
same time when both sides have one corner. -/
theorem two_fixed_contacts_pass (H : t ∈ coefficientTriples)
    (two : Nat.card (SixGapComponent g) = 2)
    (r : Subtype g.joinedHitsGap) (hr : sixCrossComponentRegion g r)
    (x y : g.Gap) (xr : g.joined x.val = r.val) (yr : g.joined y.val = r.val)
    (diff : sixGapComponent g x ≠ sixGapComponent g y)
    (fixx : g.GapVertexPerm x = x) (fixy : g.GapVertexPerm y = y) :
    let m := (componentMask t s ds g (sixGapComponent g x)).val
    oneCornerAllows t m true (g.factor x.val) (orbitResidue t s ds g x) &&
      oneCornerAllows t m false (g.factor x.val) (-orbitResidue t s ds g x) = true := by
  let c := sixGapComponent g x
  have lhs := fixed_contact_passes_one_corner t s ds g H x fixx c true
    ((componentMask_gap t s ds g c x).mpr rfl)
  have off : (componentMask t s ds g c).val.testBit (gapOwner g y) = false := by
    cases eq : (componentMask t s ds g c).val.testBit (gapOwner g y)
    · rfl
    · exact (diff ((componentMask_gap t s ds g c y).mp eq).symm).elim
  have rhs := fixed_contact_passes_one_corner t s ds g H y fixy c false off
  have same : g.factor y.val = g.factor x.val := by
    rw [← six_joined_factor_read g y.val, yr, ← xr, six_joined_factor_read]
  have op := crossing_opposite_coefficients t s ds g two r hr y x yr xr diff.symm
  rw [same,op] at rhs
  exact true_pair lhs rhs

open Lean in
run_cmd do
  unless (← Lean.collectAxioms ``two_fixed_contacts_pass).all
    (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
    throwError "Unexpected axiom in simultaneous one-corner test"
#print axioms one_corner_failures_empty
#print axioms two_fixed_contacts_pass
end
end AK3.SubVPicture.RingGeneralSix
