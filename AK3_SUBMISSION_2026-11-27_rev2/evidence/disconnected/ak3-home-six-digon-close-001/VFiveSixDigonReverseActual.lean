import VFiveSixDigonWalk
import VFiveSixReversePhase
import VFiveSixDigonLengthTable

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







/-- If the literal reverse test rejects every compatible phase, an actual
two-row all-degree-two component cannot carry the unique crossing. -/
theorem actual_digon_reverse_rejected (H : t ∈ coefficientTriples)
    (two : Nat.card (SixGapComponent g) = 2)
    (r : Subtype g.joinedHitsGap) (hr : sixCrossComponentRegion g r)
    (c : SixGapComponent g) (a b : Fin 6) (ne : a ≠ b)
    (desc : ∀ x : g.Gap, sixGapComponent g x = c ↔ gapOwner g x = a.val ∨ gapOwner g x = b.val)
    (all : ∀ z, vertexDegree (faces (pairRowRotation g (a.val,b.val))
      (pairRowBands g (a.val,b.val))) z = 2)
    (reject : reverseRejected (sixTapeAt t a) (sixTapeAt t b) = true) : False := by
  let u := sixTapeAt t a
  let w := sixTapeAt t b
  let L := u.length
  let p := g.rotationOnGaps
  let v := g.GapVertexPerm
  obtain ⟨seed,walk⟩ := digon_walk_rows t s ds g c a b ne desc all
  let X (n : Nat) := (p^n) seed
  let A (n : Nat) := cornerTag t s ds g (X n)
  let B (n : Nat) := cornerTag t s ds g (v (X n))
  have read (n : Nat) : cornerRow t s ds g (X n) = a ∧
      cornerRow t s ds g (v (X n)) = b ∧
      p (v (p (X n))) = v (X n) ∧ v (v (X n)) = X n := walk n
  have len : L = w.length := actual_digon_pair_lengths t s ds g H c a b ne desc all
  have aBounds (n : Nat) : A n < L := by
    have h := (literal_corner_weight t s ds g H (X n)).1
    rwa [(read n).1] at h
  have bBounds (n : Nat) : B n < L := by
    have h := (literal_corner_weight t s ds g H (v (X n))).1
    rwa [(read n).2.1, ← len] at h
  have aStep (n : Nat) : A (n+1)+1 ≡ A n [MOD L] := by
    change cornerTag t s ds g ((p^(n+1)) seed) + 1 ≡ A n [MOD L]
    rw [pow_succ',Perm.mul_apply]
    exact row_rotation_tag t s ds g H a (X n) (read n).1
  have bStep (n : Nat) : B n+1 ≡ B (n+1) [MOD L] := by
    have h := row_rotation_tag t s ds g H b (v (X (n+1))) (read (n+1)).2.1
    have step : p (v (X (n+1))) = v (X n) := by
      change p (v ((p^(n+1)) seed)) = v (X n)
      rw [pow_succ',Perm.mul_apply]
      exact (read n).2.2.1
    rwa [step, ← len] at h
  obtain ⟨phase,hphase,cover⟩ :=
    counterrotation_phase L (Nat.zero_lt_of_lt (aBounds 0)) A B aBounds bBounds aStep bStep
  have factorAt (n : Nat) :
      (atCorner u (A n)).1 = (atCorner w (B n)).1 := by
    have fx := (literal_corner_weight t s ds g H (X n)).2.1
    have fy := (literal_corner_weight t s ds g H (v (X n))).2.1
    rw [(read n).1] at fx
    rw [(read n).2.1] at fy
    exact fx.trans ((g.gap_vertex_preserves_factor (X n)).symm.trans fy.symm)
  have correct : digonWrongFactor u w phase = false := by
    cases eq : digonWrongFactor u w phase
    · rfl
    · exfalso
      obtain ⟨j,jr,bad⟩ := List.any_eq_true.mp eq
      obtain ⟨n,an,bn⟩ := cover j (List.mem_range.mp jr)
      have good := factorAt n
      rw [an,bn] at good
      change ((atCorner u j).1 != (atCorner w ((phase+L-j)%L)).1) = true at bad
      simp [good] at bad
  change (List.range L).all (fun phase => digonWrongFactor u w phase || twoBadAt u w phase) = true at reject
  have test := List.all_eq_true.mp reject phase (List.mem_range.mpr hphase)
  have passed : twoBadAt u w phase = true := by simpa only [correct,Bool.false_or] using test
  obtain ⟨j,k,hj,hk,diff,jbad,kbad⟩ := two_bad_witness passed
  obtain ⟨n,an,bn⟩ := cover j hj
  obtain ⟨m,am,bm⟩ := cover k hk
  have residue (i : Nat) :
      orbitResidue t s ds g (X i) =
        ((atCorner u (A i)).2 : ZMod 5) + ((atCorner w (B i)).2 : ZMod 5) := by
    have off : v (X i) ≠ X i := fun e => ne
      ((read i).1.symm.trans ((congrArg (cornerRow t s ds g) e).symm.trans (read i).2.1))
    rw [digon_residue_two_corners t s ds g H (X i) (read i).2.2.2 off,
      (read i).1, (read i).2.1]
  have defect (i q : Nat) (aRead : A i = q) (bRead : B i = (phase+L-q)%L)
      (bad : badAt u w phase q = true) : orbitResidue t s ds g (X i) ≠ 0 := by
    intro zero
    rw [residue i,aRead,bRead,← Nat.cast_add] at zero
    have dvd := (ZMod.natCast_eq_zero_iff _ _).mp zero
    change (((atCorner u q).2 + (atCorner w ((phase+L-q)%L)).2) % 5 != 0) = true at bad
    rw [Nat.mod_eq_zero_of_dvd dvd] at bad
    contradiction
  have xc (i : Nat) : sixGapComponent g (X i) = c :=
    (desc (X i)).mpr (Or.inl (congrArg Fin.val (read i).1))
  have eq := nonzero_orbits_unique_in_component t s ds g two r hr (X n) (X m)
    (defect n j an bn jbad) (defect m k am bm kbad) ((xc n).trans (xc m).symm)
  obtain ⟨q,hq⟩ : v.SameCycle (X n) (X m) := Quotient.exact eq
  rcases Perm.zpow_apply_eq_of_apply_apply_eq_self (read n).2.2.2 q with same | across
  · have e : X m = X n := hq.symm.trans same
    exact diff (an.symm.trans ((congrArg (cornerTag t s ds g) e).symm.trans am))
  · have e : X m = v (X n) := hq.symm.trans across
    exact ne ((read m).1.symm.trans ((congrArg (cornerRow t s ds g) e).trans (read n).2.1))

open Lean in
run_cmd do
  unless (← Lean.collectAxioms ``actual_digon_reverse_rejected).all
    (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
    throwError "Unexpected axiom in actual digon rejection"
#print axioms actual_digon_reverse_rejected
end
end AK3.SubVPicture.RingGeneralSix
