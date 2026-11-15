import HodgeLean.Foundations.Program.SchoenTowerPullbackTopology
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Compactness.SigmaCompact

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace HodgeLean.Foundations.Program

theorem s2v_secondCountable_of_compact_surjection {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [SecondCountableTopology X] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hsurj : Function.Surjective f) :
    SecondCountableTopology Y := by
  classical
  let B := countableBasis X
  have hb : IsTopologicalBasis B := isBasis_countableBasis X
  letI : Countable B := (countable_countableBasis X).to_subtype
  let U (s : Finset B) : Set X := ⋃ b ∈ s, b.val
  let V (s : Finset B) : Set Y := (f '' (U s)ᶜ)ᶜ
  have hU (s : Finset B) : IsOpen (U s) :=
    isOpen_iUnion fun b => isOpen_iUnion fun _ => hb.isOpen b.property
  have hV (s : Finset B) : IsOpen (V s) :=
    (hf.isClosedMap _ (hU s).isClosed_compl).isOpen_compl
  have hbV : IsTopologicalBasis (Set.range V) := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨s, rfl⟩
      exact hV s
    · intro y O hy hO
      let K : Set X := {x | f x = y}
      have hK : IsCompact K := (isClosed_eq hf continuous_const).isCompact
      have hex (x : K) : ∃ b : B, x.val ∈ b.val ∧ b.val ⊆ f ⁻¹' O := by
        obtain ⟨b, hbB, hxb, hbsub⟩ := hb.mem_nhds_iff.mp
          ((hO.preimage hf).mem_nhds (show f x.val ∈ O from x.property.symm ▸ hy))
        exact ⟨⟨b, hbB⟩, hxb, hbsub⟩
      choose b hxb hbsub using hex
      obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => (b x).val)
        (fun x => hb.isOpen (b x).property)
        (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxb ⟨x, hx⟩⟩)
      let t : Finset B := s.image b
      have hcover : K ⊆ U t := by
        intro x hx
        obtain ⟨z, hzs, hxz⟩ := Set.mem_iUnion₂.mp (hs hx)
        exact Set.mem_iUnion₂.mpr ⟨b z, Finset.mem_image_of_mem b hzs, hxz⟩
      have hsub : U t ⊆ f ⁻¹' O := by
        intro x hx
        obtain ⟨z, hzt, hxz⟩ := Set.mem_iUnion₂.mp hx
        obtain ⟨w, hws, rfl⟩ := Finset.mem_image.mp hzt
        exact hbsub w hxz
      refine ⟨V t, ⟨t, rfl⟩, ?_, ?_⟩
      · rintro ⟨x, hx, hxy⟩
        exact hx (hcover hxy)
      · intro z hz
        obtain ⟨x, rfl⟩ := hsurj z
        have hx : x ∈ U t := by
          by_contra hx
          exact hz ⟨x, hx, rfl⟩
        exact hsub hx
  exact hbV.secondCountableTopology (Set.countable_range V)

theorem s2v_projectiveSpace_points_secondCountable (n : ℕ) :
    SecondCountableTopology (ComplexPoint
      (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :=
  s2v_secondCountable_of_compact_surjection
    (ComplexProjectiveSpace.projectivizationToComplexPoint (n := n) ∘
      ComplexProjectiveSpace.sphereToProjectivization (n := n))
    (ComplexProjectiveSpace.continuous_projectivizationToComplexPoint.comp
      ComplexProjectiveSpace.continuous_sphereToProjectivization)
    (ComplexProjectiveSpace.surjective_projectivizationToComplexPoint.comp
      ComplexProjectiveSpace.surjective_sphereToProjectivization)

theorem s2v_projective_points_secondCountable (X : Over (Spec ↧ℂ))
    [h : IsProjective X.hom] : SecondCountableTopology (ComplexPoint X) := by
  obtain ⟨P⟩ := h.nonempty_presentation
  letI := s2v_projectiveSpace_points_secondCountable P.ambientDimension
  exact (ProjectiveSpace.Presentation.analyticImmersion_isClosedEmbedding P).isEmbedding.secondCountableTopology

theorem s2v_projective_openParacompactSpace (X : Over (Spec ↧ℂ))
    [IsProjective X.hom] (U : Opens (ComplexPoint X)) : ParacompactSpace U := by
  letI := s2v_projective_points_secondCountable X
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  infer_instance

theorem s2v_pullback_points_secondCountable {W B E : Over (Spec ↧ℂ)}
    [IsSeparated B.hom] [SecondCountableTopology (ComplexPoint W)]
    [SecondCountableTopology (ComplexPoint E)]
    (β : W ⟶ B) (j : E ⟶ B) : SecondCountableTopology (ComplexPoint (pullback β j)) := by
  letI : SecondCountableTopology (ComplexPoint (W ⊗ E)) :=
    (HodgeLean.Foundations.complexPointProdHomeomorph W E).isEmbedding.secondCountableTopology
  letI := s2v_pullback_toProduct_closedImmersion β j
  exact (ComplexPoint.isEmbedding_map_of_closedImmersion
    (CartesianMonoidalCategory.lift (pullback.fst β j) (pullback.snd β j))).secondCountableTopology

theorem s2v_projective_preimage_openParacompactSpace {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) (j : E ⟶ B) (U : Opens (ComplexPoint (s2b_preimage β j))) :
    ParacompactSpace U := by
  letI := s2v_projective_points_secondCountable W
  letI := s2v_projective_points_secondCountable E
  letI : CompactSpace (ComplexPoint (s2b_preimage β j)) := s2v_pullback_points_compact β j
  letI : T2Space (ComplexPoint (s2b_preimage β j)) := s2v_pullback_points_t2 β j
  letI : SecondCountableTopology (ComplexPoint (s2b_preimage β j)) :=
    s2v_pullback_points_secondCountable β j
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  infer_instance

end HodgeLean.Foundations.Program
