import VFiveSixContactLiteral

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





/-- Walking around a contact vertex first crosses the gap band and then
moves to the preceding literal corner on the row of the opposite gap. -/
theorem contact_successor_literal (H : t ∈ coefficientTriples) (x : g.Gap) :
    let y := g.GapVertexPerm x
    let z := g.gapMate x
    cornerRow t s ds g y = cornerRow t s ds g z ∧
      cornerTag t s ds g y + 1 ≡ cornerTag t s ds g z
        [MOD (sixTapeAt t (cornerRow t s ds g z)).length] := by
  let z := g.gapMate x
  let y := g.rotationOnGaps z
  let i := cornerRow t s ds g z
  have owner : cornerRow t s ds g y = i := by
    apply Fin.ext
    exact ((gapCycle_iff_owner g (literalSix_padded t s ds) z y).mp
      ((Perm.SameCycle.refl g.rotationOnGaps z).apply_right)).symm
  change cornerRow t s ds g y = i ∧
    cornerTag t s ds g y + 1 ≡ cornerTag t s ds g z [MOD (sixTapeAt t i).length]
  refine ⟨owner,?_⟩
  unfold cornerTag
  rw [owner]
  exact (rotation_moves_tag g (sixTapeAt t i) (six_tape_facts t H i)
    (mainIndex t s ds i) (sixTapeAt_expanded t s ds i)
    (literalSix_padded t s ds) z (Fin.ext rfl)).1

/-- In the one-corner case the two paired gaps must be on the same
row, and their tags are consecutive, not independent. -/
theorem fixed_contact_requires_adjacent_mate (H : t ∈ coefficientTriples) (x : g.Gap)
    (fixed : g.GapVertexPerm x = x) :
    cornerRow t s ds g x = cornerRow t s ds g (g.gapMate x) ∧
      cornerTag t s ds g x + 1 ≡ cornerTag t s ds g (g.gapMate x)
        [MOD (sixTapeAt t (cornerRow t s ds g (g.gapMate x))).length] := by
  have h := contact_successor_literal t s ds g H x
  dsimp only at h
  rwa [fixed] at h

open Lean in
run_cmd do
  unless (← Lean.collectAxioms ``fixed_contact_requires_adjacent_mate).all
    (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
    throwError "Unexpected axiom in ordered contact reading"
#print axioms contact_successor_literal
#print axioms fixed_contact_requires_adjacent_mate
end
end AK3.SubVPicture.RingGeneralSix
