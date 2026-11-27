import VFiveSixOrbitBlocks
import VFiveSixTapeCatalogue

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

theorem six_tape_facts (t : FaceTriple) (H : t ∈ coefficientTriples) (i : Fin 6) :
    LiteralTapeFacts (sixTapeAt t i) := by
  fin_cases i
  · exact tape_anchor
  · exact tape_anchor
  · change LiteralTapeFacts vMinus
    constructor <;> decide +kernel
  · exact survivorTapeFacts t H 1
  · exact survivorTapeFacts t H 2
  · exact survivorTapeFacts t H 3

variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)




def cornerRow (x : g.Gap) : Fin 6 :=
  ⟨gapOwner g x, auxiliary_no_gap g (literalSix_padded t s ds) (literalSix_aux t s ds) x⟩

def cornerTag (x : g.Gap) : Nat :=
  gapTapeTag g (sixTapeAt t (cornerRow t s ds g x)) x

private theorem main_kept (i : Fin 6) (z : g.Dart)
    (own : g.rowOwner z = mainIndex t s ds i) :
    z ∉ Finset.univ.biUnion (trailingDiscSet g) := by
  intro h
  obtain ⟨d,_,hd⟩ := Finset.mem_biUnion.mp h
  obtain ⟨k,_,e⟩ := List.mem_map.mp (Finset.mem_filter.mp hd).2
  have indices := congrArg Prod.fst e
  change (literalSix t s).length + d.val = (coord _ z.val).1 at indices
  rw [g.owner_coord,own] at indices
  change 6+d.val = i.val at indices
  have := i.isLt
  omega

theorem literal_corner_weight (H : t ∈ coefficientTriples) (x : g.Gap) :
    let w := sixTapeAt t (cornerRow t s ds g x)
    let j := cornerTag t s ds g x
    j < w.length ∧ (atCorner w j).1 = g.factor x.val ∧
    g.blockWeight (Finset.univ.biUnion (trailingDiscSet g)) (g.block x.val) =
      ((atCorner w j).2 : ZMod 5) := by
  let i := cornerRow t s ds g x
  let o := mainIndex t s ds i
  let w := sixTapeAt t i
  have own : g.rowOwner x.val = o := Fin.ext rfl
  have cert := six_tape_facts t H i
  have expands := sixTapeAt_expanded t s ds i
  exact ⟨gapTapeTag_lt g w cert o expands x own,
    gapTapeTag_factor g w cert o expands x own,
    gapTapeTag_weight g w cert o expands (literalSix_padded t s ds)
      x own _ (main_kept t s ds g i)⟩

/-- Direct reduction from the actual vertex to a sum of entries of the six
fixed tapes, regardless of the stems, the auxiliary discs, or vertex degree. -/
theorem orbitResidue_eq_literal_sum (H : t ∈ coefficientTriples) (x : g.Gap) :
    orbitResidue t s ds g x =
      ∑ y : {y : g.Gap // g.GapVertexPerm.SameCycle x y},
        ((atCorner (sixTapeAt t (cornerRow t s ds g y.val))
          (cornerTag t s ds g y.val)).2 : ZMod 5) := by
  rw [orbitResidue_eq_corner_sum t s ds g x]
  apply Finset.sum_congr rfl
  intro y _
  exact (literal_corner_weight t s ds g H y.val).2.2

open Lean in
run_cmd do
  for n in [``six_tape_facts,``literal_corner_weight,``orbitResidue_eq_literal_sum] do
    unless (← Lean.collectAxioms n).all
      (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "Unexpected axiom in literal corner reading"
#print axioms orbitResidue_eq_literal_sum
end
end AK3.SubVPicture.RingGeneralSix
