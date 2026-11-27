import GeometricFaces
import GeometricPhase

namespace AK3.SSeven.FreeCap.RawChart
open Equiv SewnCount Scaffold Surgery BandOverlay BandDeletion Seam CapSchedule ScaffoldBands SlotPrune Switch ComponentCensus
open LiveBoundary
open SeamBoundary (retained)
open Curvature hiding tape
open scoped Classical BigOperators
set_option maxHeartbeats 1800000
variable {ds : List Cell} {p : Perm (Augmented ds)}
  {es : BandList ds} {live : FaceId ds → Prop}

theorem vertex_factor_on_coordinate (s : Live ds p es live) (k : Solid p es)
    (e : Orbits (chosenVertex s k)) (M : MarkedRelativeMap (chosenDarts s k) (keepChosen s k e))
    (v : RetainedVertex s k e) (i : Fin (vertexWidth s k e v)) :
    M.vertex_factor (geometricVertexPosition s k e ⟨v,i⟩).val =
      M.vertex_factor (vertexBase s k e v) := by
  have g := geometric_vertex_tag s k e v i
  have h : vertexClass s k (geometricVertexPosition s k e ⟨v,i⟩).val =
      vertexClass s k (vertexBase s k e v) :=
    (congrArg Subtype.val g).trans (vertexBase_prop s k e v).1.symm
  exact same_from_step (p:=chosenVertex s k) (f:=M.vertex_factor)
    (fun a=>(M.factor_same a).symm) (Quotient.exact h)

theorem kept_vertex_mem (s : Live ds p es live) (k : Solid p es)
    (e : Orbits (chosenVertex s k)) [Fintype (Orbits (chosenVertex s k))]
    (o : Orbits (chosenVertex s k)) :
    o∈keptVertexSet s k e ↔ ∃ d, vertexClass s k d=o ∧ (keepChosen s k e).keep d := by
  unfold keptVertexSet
  rw [Finset.mem_filter]
  simp

/-- No additional diagram or topological premise: the argument uses
the actual chosen component obtained from the literal surgery chain. -/
theorem chosen_curvature_contradiction (s : Live ds p es live) (red : NoLiteralDipole es live)
    (k : Solid p es) (b : Rim p es) (a : ChosenDart p es live k)
    (ab : rimAt p es a.val.val=b) (nz : cornerSum live b≠0)
    (other : ∀ j : Rim p es, fTag p (retained ds es) j=k → j≠b → cornerSum live j=0)
    (zz : pieceGap p (retained ds es) k=0) : False := by
  let e := vertexClass s k a
  let S := chosenDarts s k
  let R := keepChosen s k e
  have zero := (exceptional_seed_phase s k b a ab nz other).2
  let M := markedChosen s k e zero red
  let _ := Fintype.ofFinite (ChosenDart p es live k)
  let _ := Fintype.ofFinite (KeptDart R)
  let _ := Fintype.ofFinite (Orbits (chosenVertex s k))
  let V := RetainedVertex s k e
  let F := FaceClass s k
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite F
  let NV := Fintype.card V
  let NF := Fintype.card F
  let K := keptVertexSet s k e
  let E := Nat.card (CellEdges p (retained ds es) k)-(Finset.univ \ K).card
  let ve : Fin NV ≃ V := (Fintype.equivFin V).symm
  let fe : Fin NF ≃ F := (Fintype.equivFin F).symm
  let eV : V := ⟨e,⟨a,rfl,keep_exception s k a⟩⟩
  let ex := ve.symm eV
  let degree (v : Fin NV) := vertexWidth s k e (ve v)
  let factor (v : Fin NV) := M.vertex_factor (vertexBase s k e (ve v))
  let fs (f : Fin NF) := chosenFaceSheet s k (fe f)
  let vp : (Σ v : Fin NV, Fin (degree v)) ≃ KeptDart R :=
    (Equiv.sigmaCongr ve (fun v => Equiv.refl (Fin (degree v)))).trans
      (geometricVertexPosition s k e)
  let fp : (Σ f : Fin NF, Fin (Curvature.tape (fs f)).masses.size) ≃ ChosenDart p es live k :=
    (Equiv.sigmaCongr fe (fun f => finCongr (literal_face_alignment (fs f)).1)).trans
      (geometricFacePosition s k)
  have avoid (v : Fin NV) (ne : v≠ex) : (ve v).val≠e := by
    intro same
    apply ne
    apply ve.injective
    exact (Subtype.ext same : ve v=eV).trans (ve.apply_symm_apply eV).symm
  have counts := exact_compressed_counts s k a zz
  have edgeCount : Fintype.card (KeptDart R)=2*E := by
    rw [←Nat.card_eq_fintype_card]
    exact counts.1
  have vc : NV=K.card := by
    have eq : V ≃ (↑K : Type) :=
      { toFun := fun v => ⟨v.val,(kept_vertex_mem s k e v.val).mpr v.property⟩
        invFun := fun v => ⟨v.val,(kept_vertex_mem s k e v.val).mp v.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Fintype.card_congr eq).trans (Fintype.card_coe K)
  have fc : Nat.card (Orbits (compressedChosen s k e).forward)=NF :=
    (Nat.card_congr (chosenCompressedFaces s k a)).trans Nat.card_eq_fintype_card
  have euler : (NV:Int)-E+NF=2 := by
    rw [vc,←fc]
    exact counts.2
  have nf : 0<NF := by
    let : Nonempty F := ⟨chosenFaceTag s k a⟩
    exact Fintype.card_pos
  let data : MarkedSphereData M NV E NF :=
    { connected := chosen_connected s k
      kept := ⟨a,keep_exception s k a⟩
      exception := ex
      faceSheet := fs
      degree := degree
      factor := factor
      facePosition := fp
      vertexPosition := vp
      face_read_sheet := fun f j => geometric_face_sheet s k (fe f) (finCongr
        (literal_face_alignment (fs f)).1 j)
      face_read_index := fun f j => geometric_face_index s k (fe f) (finCongr
        (literal_face_alignment (fs f)).1 j)
      vertex_cyclic := fun v j => geometric_vertex_step s k e (ve v) j
      vertex_factor := fun v j => vertex_factor_on_coordinate s k e M (ve v) j
      ordinary_degree := fun v ne => geometric_ordinary_degree s k e zero (ve v) (avoid v ne)
      ordinary_phase := fun v ne => geometric_ordinary_phase s k e zero (ve v) (avoid v ne)
      edge_count := edgeCount
      euler := euler
      faces_present := nf }
  exact no_marked_relative_sphere data

theorem yQ_ne_one_by_curvature : yQ≠1 := by
  intro h
  obtain ⟨ds,p,es,live,k,b,s,red,tag,nz,other,zz,j,lj,sj,jb⟩ := reduced_literal_component h
  let a : ChosenDart p es live k := ⟨⟨j,lj,sj⟩,(congrArg (fTag p (retained ds es)) jb).trans tag⟩
  exact chosen_curvature_contradiction s red k b a jb nz other zz

theorem common_nonconjugate_by_curvature :
    ∀ c : Common, c*commonMap (FreeGroup.mk aWord)*c⁻¹≠commonMap (FreeGroup.mk fWord) :=
  common_nonconjugate_of_yQ yQ_ne_one_by_curvature

#print axioms chosen_curvature_contradiction
#print axioms yQ_ne_one_by_curvature
#print axioms common_nonconjugate_by_curvature
end AK3.SSeven.FreeCap.RawChart
