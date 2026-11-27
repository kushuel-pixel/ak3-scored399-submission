import VFiveSixTwoCensus
import VFiveSixTwoContact

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
variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)

local notation "C" => SixGapComponent g
local notation "component" => sixGapComponent g

/-- Except for the three neutral signed allocations, every actual two-component
diagram must have a unique crossing joining exactly two gap-vertex orbits. -/
theorem two_component_neutral_or_one_contact (H : t ∈ coefficientTriples)
    (two : Nat.card C = 2) :
    exceptionalNegative t (componentMask t s ds g
      (sixGapComponent g (rowGap t s ds g 2))).val ∨
    ∃! r : Subtype g.joinedHitsGap, sixCrossComponentRegion g r ∧
      ∃ x y : Orbits g.GapVertexPerm,
        sixGapVertexComponent g x ≠ sixGapVertexComponent g y ∧
        ∀ z, g.gapVertexJoined z = r ↔ z = x ∨ z = y := by
  classical
  by_cases present : Nonempty (Subtype (sixCrossComponentRegion g))
  · obtain ⟨⟨r,hr⟩⟩ := present
    have unique := six_mixed_region_subsingleton t s ds g two
    right
    exact ⟨r, ⟨hr,two_components_crossing_has_two_orbits g two hr⟩,
      fun p hp => congrArg Subtype.val (unique.elim ⟨p,hp.1⟩ ⟨r,hr⟩)⟩
  · left
    apply negative_component_only_exceptional_if_closed t s ds g H (by omega)
    intro f x y _ same
    by_cases eq : component x = component y
    · rw [eq]
    · obtain ⟨p,_,hp⟩ := mixed_of_gap_pair t s ds g x y same eq
      exact (present ⟨⟨p,hp⟩⟩).elim

open Lean in
run_cmd do
  unless (← Lean.collectAxioms ``two_component_neutral_or_one_contact).all
    (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
    throwError "Unexpected axiom in two-component reduction"

#print axioms two_component_neutral_or_one_contact
end
end AK3.SubVPicture.RingGeneralSix
