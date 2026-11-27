import VFiveSixContactTable

namespace AK3.SubVPicture.RingGeneralSix
open Equiv AK3.SSeven AK3.SSeven.Relative AK3.SSeven.FreeCap
open AK3.SSeven.FreeCap.CapSchedule AK3.SSeven.FreeCap.SewnCount
open AK3.SSeven.FreeCap.BandOverlay AK3.SSeven.FreeCap.BandDeletion
open AK3.SSeven.FreeCap.SlotPrune AK3.SSeven.FreeCap.Switch
open AK3.SSeven.Endpoint.Weighted AK3.SSeven.Endpoint.Weighted.VFiveBoundary
open AK3.CoefficientDiagram AK3.SSeven.Curvature AK3.SubVPicture.Literal
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32000
noncomputable section
section RawChart

variable {rows : List (Word × Word)} {outer : BoundarySchedule (combine rows)}
  {q : Perm (Pos rows)} {tr : List (Pos rows × Pos rows)} (g : PlanarCore rows outer q tr)

/-- A chart orbit that meets a cut reaches a first cut on the same
coefficient block as its starting site. -/
private theorem chart_block_reaches_gap (d : g.Dart) (x : g.Gap)
    (hits : g.chartVertexPerm.SameCycle d x.val) :
    ∃ z : g.Gap, g.chartVertexPerm.SameCycle d z.val ∧ g.block d = g.block z.val := by
  classical
  let p := g.chartVertexPerm
  let K := fun y : g.Dart => g.factor (g.gapWalk y) ≠ g.factor y
  have reaches : ∃ n : Nat, K ((p ^ n) d) := by
    obtain ⟨n,h⟩ := hits.exists_nat_pow_eq
    exact ⟨n, h.symm ▸ x.property⟩
  let n := Nat.find reaches
  let z : g.Gap := ⟨(p ^ n) d, Nat.find_spec reaches⟩
  refine ⟨z, (Perm.SameCycle.refl p d).pow_right, ?_⟩
  have steady (y : g.Dart) (off : ¬ K y) : g.block (p y) = g.block y := by
    have same : (g.read y).1 = (g.read (g.turn y)).1 :=
      (not_not.mp (mt (g.changes_iff y).mpr off)).symm
    have out : y ∉ used g.gapBands :=
      fun h => off ((g.changes_iff y).mpr ((g.gapBands_cover y).mp h))
    change g.block (g.turn (bandPerm g.gapBands y)) = g.block y
    rw [unused_band _ _ out]
    exact g.block_along y same
  have progress (j : Nat) (le : j ≤ n) : g.block ((p ^ j) d) = g.block d := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Perm.mul_apply]
      have off : ¬ K ((p ^ j) d) := Nat.find_min reaches (by omega)
      exact (steady _ off).trans (ih (by omega))
  exact (progress n le_rfl).symm

/-- Darts on one monochromatic block stay on the same full chart orbit. -/
private theorem block_same_chart {a b : g.Dart} (same : g.block a = g.block b) :
    rep g.chartVertexPerm a = rep g.chartVertexPerm b := by
  let label : g.BoundaryBlock → Orbits g.chartVertexPerm := Quot.lift (rep g.chartVertexPerm) (by
    intro d e link
    cases link with
    | step h =>
      have off : ¬ (g.factor (g.gapWalk d) ≠ g.factor d) :=
        fun cut => ((g.changes_iff d).mp cut) h.symm
      have out : d ∉ used g.gapBands :=
        fun use => off ((g.changes_iff d).mpr ((g.gapBands_cover d).mp use))
      have turn : g.chartVertexPerm d = g.turn d := by
        change g.turn (bandPerm g.gapBands d) = g.turn d
        rw [unused_band _ _ out]
      apply Quotient.sound
      rw [← turn]
      exact (Perm.SameCycle.refl g.chartVertexPerm d).apply_right)
  exact congrArg label same

end RawChart

variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)



/-- A contact vertex uses one monochromatic block for every gap in its orbit.
This calculation does not bound or assume the degree of the vertex. -/
theorem orbitResidue_eq_corner_sum (x : g.Gap) :
    orbitResidue t s ds g x =
      ∑ y : {y : g.Gap // g.GapVertexPerm.SameCycle x y},
        g.blockWeight (Finset.univ.biUnion (trailingDiscSet g)) (g.block y.val.val) := by
  classical
  let O := {y : g.Gap // g.GapVertexPerm.SameCycle x y}
  let aux := Finset.univ.biUnion (trailingDiscSet g)
  let part (y : O) := g.blockDarts (g.block y.val.val) aux
  let sites := (sixNonauxDarts t s ds g).filter
    (fun d => rep g.chartVertexPerm d = rep g.chartVertexPerm x.val)
  have cover : sites = Finset.univ.biUnion part := by
    ext d
    constructor
    · intro hd
      obtain ⟨onMain, same⟩ := Finset.mem_filter.mp hd
      have off := (Finset.mem_filter.mp onMain).2
      have cyc : g.chartVertexPerm.SameCycle d x.val := Quotient.exact same
      obtain ⟨z,reaches,block⟩ := chart_block_reaches_gap g d x cyc
      have project := project_same g.chartVertexPerm
        (fun d => g.factor (g.gapWalk d) ≠ g.factor d) x z
      rw [g.chartVertex_prune_eq] at project
      let w : O := ⟨z, project.mpr (cyc.symm.trans reaches)⟩
      exact Finset.mem_biUnion.mpr
        ⟨w, Finset.mem_univ w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, block, off⟩⟩
    · intro hd
      obtain ⟨y,_,hy⟩ := Finset.mem_biUnion.mp hd
      obtain ⟨block,off⟩ := (Finset.mem_filter.mp hy).2
      have atVertex := congrArg g.gapVertexToChart (Quotient.sound y.property)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,off⟩,
          (block_same_chart g block).trans atVertex.symm⟩
  have disjoint : Set.PairwiseDisjoint (↑(Finset.univ : Finset O) : Set O) part := by
    intro y _ z _ different
    apply Finset.disjoint_left.mpr
    intro d hy hz
    have eq := (Finset.mem_filter.mp hy).2.1.symm.trans (Finset.mem_filter.mp hz).2.1
    exact different (Subtype.ext (g.gap_block_injective eq))
  change (∑ d ∈ sites, (g.signed d : ZMod 5)) = _
  rw [cover, Finset.sum_biUnion disjoint]
  rfl

open Lean in
run_cmd do
  unless (← Lean.collectAxioms ``orbitResidue_eq_corner_sum).all
    (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
    throwError "Unexpected axiom in block sum"
#print axioms orbitResidue_eq_corner_sum
end
end AK3.SubVPicture.RingGeneralSix
