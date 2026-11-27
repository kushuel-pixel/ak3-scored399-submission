import VFiveSixContactOrbit

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

/-- (mask, crossing factor, signed coefficient on negative-anchor side). -/
def chargedContactInputs (t : FaceTriple) : List (Nat × Fin 2 × ZMod 5) :=
  ([0,1] : List (Fin 2)).flatMap fun closed =>
    let f := if closed = 0 then 1 else 0
    ((negativeFactorMasks t closed).map fun m =>
      (m, f, coordinate (selectedCharge (chartCharges t) m) f)).filter
        (fun z => decide (z.2.2 ≠ 0))

theorem charged_contact_count :
    (certifiedTriples.map fun t => (chargedContactInputs t).length).sum = 97 := by
  decide +kernel

private theorem zero_mask_is_exceptional (t : FaceTriple) (H : t ∈ coefficientTriples)
    (m : Fin 64) (f : Fin 2) (h : m.val ∈ negativeFactorMasks t f)
    (zero : coordinate (selectedCharge (chartCharges t) m.val) (if f = 0 then 1 else 0) = 0) :
    exceptionalNegative t m.val := by
  rw [← roster_binding] at H
  simp only [certifiedTriples,List.mem_cons,List.not_mem_nil,or_false] at H
  rcases H with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    unfold exceptionalNegative <;> revert m f <;> decide +kernel

variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)



/-- Every nonneutral actual split has a contact entry; its nonzero
coordinate forces both the location factor and the local coefficient. -/
theorem two_component_charged_contact (H : t ∈ coefficientTriples)
    (two : Nat.card (SixGapComponent g) = 2) :
    let c := sixGapComponent g (rowGap t s ds g 2)
    let m := (componentMask t s ds g c).val
    exceptionalNegative t m ∨
    ∃ (r : Subtype g.joinedHitsGap) (x : g.Gap),
      sixCrossComponentRegion g r ∧ g.joined x.val = r.val ∧
      sixGapComponent g x = c ∧ (m, g.factor x.val, orbitResidue t s ds g x) ∈ chargedContactInputs t := by
  classical
  let c := sixGapComponent g (rowGap t s ds g 2)
  let m := (componentMask t s ds g c).val
  change exceptionalNegative t m ∨ _
  rcases two_component_neutral_or_one_contact t s ds g H two with exceptional | ⟨r,⟨hr,_⟩,_⟩
  · exact Or.inl exceptional
  by_cases exc : exceptionalNegative t m
  · exact Or.inl exc
  obtain ⟨closed,mem⟩ := two_component_negative_mask_in_census t s ds g H two
  let f : Fin 2 := if closed = 0 then 1 else 0
  have nz : coordinate (selectedCharge (chartCharges t) m) f ≠ 0 :=
    fun z => exc (zero_mask_is_exceptional t H (componentMask t s ds g c) closed mem z)
  have forced : sixJoinedFactor g r.val = f := by
    by_contra off
    exact nz (by rw [chart_mask_coordinate t s ds g H c f,
      component_charge_localized t s ds g two c r hr f, ite_eq_right off])
  have pair := hr
  obtain ⟨a,b,ha,hb,diff⟩ := pair
  have member : sixGapVertexComponent g a = c ∨ sixGapVertexComponent g b = c := by
    by_contra! off
    let _ : Fintype (SixGapComponent g) := Fintype.ofFinite _
    have size : ({sixGapVertexComponent g a, sixGapVertexComponent g b, c} :
        Finset (SixGapComponent g)).card = 3 := by simp [diff,off.1,off.2]
    have cap := Finset.card_le_univ ({sixGapVertexComponent g a, sixGapVertexComponent g b, c} :
        Finset (SixGapComponent g))
    rw [size, ← Nat.card_eq_fintype_card, two] at cap
    omega
  obtain ⟨p,hp,pc⟩ : ∃ p : Orbits g.GapVertexPerm,
      g.gapVertexJoined p = r ∧ sixGapVertexComponent g p = c := by
    rcases member with e|e
    · exact ⟨a,ha,e⟩
    · exact ⟨b,hb,e⟩
  obtain ⟨x,hx⟩ : ∃ x : g.Gap, rep g.GapVertexPerm x = p := Quot.exists_rep _
  have atR : g.joined x.val = r.val := congrArg Subtype.val ((congrArg g.gapVertexJoined hx).trans hp)
  have xc : sixGapComponent g x = c := (congrArg (sixGapVertexComponent g) hx).trans pc
  have xf : g.factor x.val = f := (six_joined_factor_read g x.val).symm.trans
    ((congrArg (sixJoinedFactor g) atR).trans forced)
  have localEq := crossing_orbit_reads_row_mask t s ds g H two r hr x atR
  rw [xc,xf] at localEq
  change coordinate (selectedCharge (chartCharges t) m) f = orbitResidue t s ds g x at localEq
  right
  refine ⟨r,x,hr,atR,xc,?_⟩
  rw [xf,← localEq]
  apply List.mem_flatMap.mpr
  refine ⟨closed, ?_, ?_⟩
  · fin_cases closed <;> decide
  · apply List.mem_filter.mpr
    exact ⟨List.mem_map.mpr ⟨m,mem,rfl⟩, decide_eq_true nz⟩

open Lean in
run_cmd do
  for n in [``charged_contact_count,``two_component_charged_contact] do
    unless (← Lean.collectAxioms n).all
      (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "Unexpected axiom for contact table: {n}"

#print axioms charged_contact_count
#print axioms two_component_charged_contact
end
end AK3.SubVPicture.RingGeneralSix
