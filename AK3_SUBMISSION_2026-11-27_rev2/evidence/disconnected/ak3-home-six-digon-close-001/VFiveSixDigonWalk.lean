import VFiveSixDigonLengths
import VFiveSixDefectUnique

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

variable (t : FaceTriple) (s : SixStems) (ds : List TorsionDisc)
  {outer : BoundarySchedule (combine (literalSix t s ++ discRows ds))}
  {q : Perm (Pos (literalSix t s ++ discRows ds))}
  {tr : List (Pos (literalSix t s ++ discRows ds) × Pos (literalSix t s ++ discRows ds))}
  (g : PlanarCore (literalSix t s ++ discRows ds) outer q tr)






private theorem digon_pair_seed (c : SixGapComponent g) (a b : Fin 6) (ne : a ≠ b)
    (desc : ∀ x : g.Gap, sixGapComponent g x = c ↔
      gapOwner g x = a.val ∨ gapOwner g x = b.val) :
    ∃ x : g.Gap, gapOwner g x = a.val ∧ gapOwner g (g.gapMate x) = b.val := by
  classical
  by_contra! no
  let A := rowGap t s ds g a
  let B := rowGap t s ds g b
  have ha : gapOwner g A = a.val := rowGap_owner t s ds g a
  have hb : gapOwner g B = b.val := rowGap_owner t s ds g b
  have stable (x : g.Gap) (p : gapOwner g x = a.val) :
      gapOwner g (g.gapMate x) = a.val := by
    have e : sixGapComponent g x = sixGapComponent g (g.gapMate x) := Quot.sound (Or.inr rfl)
    exact ((desc _).mp (e.symm.trans ((desc x).mpr (Or.inl p)))).resolve_right (no x p)
  let label : SixGapComponent g → Bool := Quot.lift (fun x : g.Gap => decide (gapOwner g x = a.val)) (by
    intro x y h
    have agrees : gapOwner g x = a.val ↔ gapOwner g y = a.val := by
      rcases h with h | rfl
      · rw [(gapCycle_iff_owner g (literalSix_padded t s ds) _ _).mp h]
      · exact ⟨stable x,fun h => g.gap_invol x ▸ stable (g.gapMate x) h⟩
    by_cases h : gapOwner g x = a.val
    · simp [h,agrees.mp h]
    · simp [h,mt agrees.mpr h])
  have eq : sixGapComponent g A = sixGapComponent g B :=
    ((desc A).mpr (Or.inl ha)).trans ((desc B).mpr (Or.inr hb)).symm
  have e := congrArg label eq
  change decide (gapOwner g A = a.val) = decide (gapOwner g B = a.val) at e
  have d : b.val ≠ a.val := fun h => ne (Fin.ext h.symm)
  simp [ha,hb,d] at e


/-- On either row of a genuine all-degree-two component, the unrestricted
vertex walk returns after exactly two steps. -/
theorem digon_raw_double (c : SixGapComponent g) (a b : Fin 6)
    (desc : ∀ x : g.Gap, sixGapComponent g x = c ↔ gapOwner g x = a.val ∨ gapOwner g x = b.val)
    (all : ∀ z, vertexDegree (faces (pairRowRotation g (a.val,b.val))
      (pairRowBands g (a.val,b.val))) z = 2)
    (x : g.Gap) (mem : sixGapComponent g x = c) :
    g.GapVertexPerm (g.GapVertexPerm x) = x := by
  let i := (a.val,b.val)
  let D := Subtype (pairRowGap g i)
  let v := faces (pairRowRotation g i) (pairRowBands g i)
  let view := pairRowToGap g i
  have side (z : g.Gap) : pairRowGap g i z.val ↔ sixGapComponent g z = c :=
    ⟨fun h => (desc z).mpr h.2,fun h => ⟨z.property,(desc z).mp h⟩⟩
  have iso (z : g.Gap) : pairRowGap g i z.val ↔ pairRowGap g i (g.gapMate z).val := by
    have e : sixGapComponent g z = sixGapComponent g (g.gapMate z) := Quot.sound (Or.inr rfl)
    rw [side z,side (g.gapMate z),e]
  let z : D := ⟨x.val,(side x).mpr mem⟩
  have d : v (v z) = z := degree_two_forces_double_return v z (all _)
  have read := pair_row_vertex_agrees g i (literalSix_padded t s ds) iso
  have h := congrArg view d
  change view (v (v z)) = view z at h
  change g.GapVertexPerm (g.GapVertexPerm (view z)) = view z
  exact ((read (v z)).trans (congrArg g.GapVertexPerm (read z))).symm.trans h

theorem row_rotation_keeps_row (x : g.Gap) :
    cornerRow t s ds g (g.rotationOnGaps x) = cornerRow t s ds g x := by
  apply Fin.ext
  exact ((gapCycle_iff_owner g (literalSix_padded t s ds) x _).mp
    (Perm.SameCycle.refl g.rotationOnGaps x).apply_right).symm

theorem row_rotation_tag (H : t ∈ coefficientTriples) (a : Fin 6) (x : g.Gap)
    (own : cornerRow t s ds g x = a) :
    cornerTag t s ds g (g.rotationOnGaps x) + 1 ≡ cornerTag t s ds g x
      [MOD (sixTapeAt t a).length] := by
  have ownRaw : g.rowOwner x.val = mainIndex t s ds a := Fin.ext (congrArg (fun i : Fin 6 => i.val) own)
  unfold cornerTag
  rw [row_rotation_keeps_row t s ds g x,own]
  exact (rotation_moves_tag g (sixTapeAt t a) (six_tape_facts t H a)
    (mainIndex t s ds a) (sixTapeAt_expanded t s ds a)
    (literalSix_padded t s ds) x ownRaw).1

theorem digon_walk_rows (c : SixGapComponent g) (a b : Fin 6) (ne : a ≠ b)
    (desc : ∀ x : g.Gap, sixGapComponent g x = c ↔ gapOwner g x = a.val ∨ gapOwner g x = b.val)
    (all : ∀ z, vertexDegree (faces (pairRowRotation g (a.val,b.val))
      (pairRowBands g (a.val,b.val))) z = 2) :
    ∃ seed : g.Gap, ∀ n : Nat,
      let x := (g.rotationOnGaps ^ n) seed
      cornerRow t s ds g x = a ∧ cornerRow t s ds g (g.GapVertexPerm x) = b ∧
      g.rotationOnGaps (g.GapVertexPerm (g.rotationOnGaps x)) = g.GapVertexPerm x ∧
      g.GapVertexPerm (g.GapVertexPerm x) = x := by
  obtain ⟨seed,ha,hb⟩ := digon_pair_seed t s ds g c a b ne desc
  let p := g.rotationOnGaps
  let m := g.gapMate
  let v := g.GapVertexPerm
  have vx (x : g.Gap) (own : cornerRow t s ds g x = a) :
      p (v (p x)) = v x := by
    have h : sixGapComponent g x = c := (desc x).mpr (Or.inl (congrArg Fin.val own))
    have eq : sixGapComponent g x = sixGapComponent g (m x) := Quot.sound (Or.inr rfl)
    have d := digon_raw_double t s ds g c a b desc all (m x) (eq.symm.trans h)
    have mr : m (p x) = p.symm (m x) := by
      apply p.injective
      change (p*m) ((p*m) (m x)) = m x at d
      have inv : m (m x) = x := g.gap_invol x
      simpa only [Perm.mul_apply,inv,apply_symm_apply] using d
    change p (p (m (p x))) = p (m x)
    rw [mr,p.apply_symm_apply]
  have owners (n : Nat) : cornerRow t s ds g ((p ^ n) seed) = a ∧
      cornerRow t s ds g (v ((p ^ n) seed)) = b := by
    induction n with
    | zero =>
      simp only [pow_zero,Perm.one_apply]
      exact ⟨Fin.ext ha,(row_rotation_keeps_row t s ds g (m seed)).trans (Fin.ext hb)⟩
    | succ n ih =>
      rw [pow_succ',Perm.mul_apply]
      refine ⟨(row_rotation_keeps_row t s ds g _).trans ih.1, ?_⟩
      rw [← row_rotation_keeps_row t s ds g (v (p ((p ^ n) seed))),vx _ ih.1]
      exact ih.2
  refine ⟨seed,fun n => ?_⟩
  let x := (p ^ n) seed
  have o := owners n
  exact ⟨o.1,o.2,vx x o.1,digon_raw_double t s ds g c a b desc all x
    ((desc x).mpr (Or.inl (congrArg Fin.val o.1)))⟩

#print axioms digon_walk_rows
end
end AK3.SubVPicture.RingGeneralSix
