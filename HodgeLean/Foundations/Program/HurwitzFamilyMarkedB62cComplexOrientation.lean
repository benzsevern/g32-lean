import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.CenteredComplexOrientation
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cExcision

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory Topology AlgebraicTopology.Singular
variable (R : Type) [CommRing R] (d : ℕ)

theorem b6m_complexMatrix_preserves_localClass
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.det ≠ 0) :
    relativeHomologyMap R (2 * d) (complexMatrixPuncturedPairMap d A hA)
        (standardComplexLocalClass R d) = standardComplexLocalClass R d := by
  let H := (Matrix.nonempty_complexIsotopyToOne A hA).some
  have h := (complexMatrixPuncturedPairHomotopy d hA H).relativeHomologyMap_apply_eq
    (R := R) (2 * d) (standardComplexLocalClass R d)
  simpa using h.symm

theorem b6m_localHomotopy_relativeHomologyMap_eq
    {Y : TopPair} (n : ℕ) (F G : puncturedPair ℂ d ⟶ Y)
    (U : Set (Fin d → ℂ)) (hU : IsOpen U) (h0U : 0 ∈ U)
    (H : TopPair.Homotopy
      (neighborhoodPointComplementPairMap U 0 ≫ F)
      (neighborhoodPointComplementPairMap U 0 ≫ G)) :
    relativeHomologyMap R n F = relativeHomologyMap R n G := by
  ext a
  obtain ⟨b, rfl⟩ := (b6m_closed_support_excision_bijective R hU isClosed_singleton
    (Set.singleton_subset_iff.mpr h0U) n).2 a
  have h := H.relativeHomologyMap_apply_eq (R := R) n b
  have he : b6m_subspacePairMap (TopCat.of (Fin d → ℂ)) U {0}ᶜ =
      neighborhoodPointComplementPairMap U 0 := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext z <;> rfl
  rw [he]
  rw [relativeHomologyMap_comp, relativeHomologyMap_comp] at h
  exact h

theorem b6m_local_complexDifferentiable_invariance
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.det ≠ 0)
    (U : Set (Fin d → ℂ)) (hU : IsOpen U) (h0U : 0 ∈ U)
    (f : (Fin d → ℂ) → (Fin d → ℂ)) (hf : ContinuousOn f U)
    (hf0 : f 0 = 0)
    (hf' : HasFDerivAt f
      (A.mulVecLin.toContinuousLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0) :
    ∃ (V : Set (Fin d → ℂ)) (hVU : V ⊆ U)
        (hf_ne : ∀ z, z ∈ V → z ≠ 0 → f z ≠ 0),
      IsOpen V ∧ 0 ∈ V ∧
      ∀ c : RelativeHomology R (neighborhoodPointComplementPair V 0) (2 * d),
        relativeHomologyMap R (2 * d) (neighborhoodPointComplementPairMap V 0) c =
            standardComplexLocalClass R d →
          relativeHomologyMap R (2 * d)
              (complexNeighborhoodPuncturedPairMapOf d V f (hf.mono hVU) hf_ne) c =
            standardComplexLocalClass R d := by
  let f' : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    A.mulVecLin.toContinuousLinearMap
  have hf'_apply (z : Fin d → ℂ) : f' z = A.mulVec z := rfl
  have hf'_inj : Function.Injective f' := fun x y hxy ↦
    A.mulVec_injective_of_det_ne_zero hA (by simpa only [← hf'_apply] using hxy)
  obtain ⟨W, hW, h0W, hline⟩ :=
    exists_open_straightLine_ne_zero d f f' hf0 hf' hf'_inj
  let V := U ∩ W
  have hV : IsOpen V := hU.inter hW
  have h0V : 0 ∈ V := ⟨h0U, h0W⟩
  have hlineV : ∀ (t : unitInterval) (z : Fin d → ℂ), z ∈ V → z ≠ 0 →
      A.mulVec z + (((t : ℝ) : ℂ) • (f z - A.mulVec z)) ≠ 0 := by
    intro t z hz hz0
    simpa only [hf'_apply] using hline t z hz.2 hz0
  have hfV : ContinuousOn f V := hf.mono Set.inter_subset_left
  have hf_neV : ∀ z, z ∈ V → z ≠ 0 → f z ≠ 0 := by
    intro z hz hz0
    simpa using hlineV (1 : unitInterval) z hz hz0
  refine ⟨V, Set.inter_subset_left, hf_neV, hV, h0V, ?_⟩
  intro c hc
  let H := complexStraightLineLocalPairHomotopy d A hA V f hfV hf_neV hlineV
  have hhom := H.relativeHomologyMap_apply_eq (R := R) (2 * d) c
  calc
    relativeHomologyMap R (2 * d)
        (complexNeighborhoodPuncturedPairMapOf d V f hfV hf_neV) c =
        relativeHomologyMap R (2 * d)
          (neighborhoodPointComplementPairMap V 0 ≫
            complexMatrixPuncturedPairMap d A hA) c := hhom.symm
    _ = relativeHomologyMap R (2 * d) (complexMatrixPuncturedPairMap d A hA)
        (relativeHomologyMap R (2 * d) (neighborhoodPointComplementPairMap V 0) c) := by
          rw [relativeHomologyMap_comp]
          rfl
    _ = relativeHomologyMap R (2 * d) (complexMatrixPuncturedPairMap d A hA)
        (standardComplexLocalClass R d) := by rw [hc]
    _ = standardComplexLocalClass R d :=
      b6m_complexMatrix_preserves_localClass R d A hA

theorem b6m_complexDifferentiable_preserves_localClass
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.det ≠ 0)
    (f : (Fin d → ℂ) → (Fin d → ℂ)) (hf : Continuous f)
    (hf0 : f 0 = 0) (hf_ne : ∀ z, z ≠ 0 → f z ≠ 0)
    (hf' : HasFDerivAt f
      (A.mulVecLin.toContinuousLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0) :
    relativeHomologyMap R (2 * d) (complexPuncturedPairMapOf d f hf hf_ne)
        (standardComplexLocalClass R d) =
      standardComplexLocalClass R d := by
  let f' : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    A.mulVecLin.toContinuousLinearMap
  have hf'_apply (z : Fin d → ℂ) : f' z = A.mulVec z := rfl
  have hf'_inj : Function.Injective f' := fun x y hxy ↦
    A.mulVec_injective_of_det_ne_zero hA (by simpa only [← hf'_apply] using hxy)
  obtain ⟨U, hU, h0U, hline⟩ :=
    exists_open_straightLine_ne_zero d f f' hf0 hf' hf'_inj
  have hline' : ∀ (t : unitInterval) (z : Fin d → ℂ), z ∈ U → z ≠ 0 →
      A.mulVec z + (((t : ℝ) : ℂ) • (f z - A.mulVec z)) ≠ 0 := by
    simpa only [hf'_apply] using hline
  let H := complexStraightLineNeighborhoodPairHomotopy d A hA f hf hf_ne U hline'
  have hmaps := b6m_localHomotopy_relativeHomologyMap_eq R d (2 * d)
    (complexMatrixPuncturedPairMap d A hA)
    (complexPuncturedPairMapOf d f hf hf_ne) U hU h0U H
  rw [← hmaps]
  exact b6m_complexMatrix_preserves_localClass R d A hA

theorem b6m_centeredEmbedding_relativeHomologyMap_eq
    (F : (Fin d → ℂ) → (Fin d → ℂ)) (hF : Continuous F) (hFi : Function.Injective F)
    (v : Fin d → ℂ) (n : ℕ) :
    relativeHomologyMap R n (centeredComplexEmbeddingPair d F hF hFi v) =
      relativeHomologyMap R n (centeredComplexEmbeddingPair d F hF hFi 0) :=
  ((centeredComplexEmbeddingPairHomotopy d F hF hFi v).congr_relativeHomologyMap n).symm

theorem b6m_centeredUnivBall_preserves_localClass
    (c : Fin d → ℂ) (r : ℝ) (hr : 0 < r) (v : Fin d → ℂ) :
    relativeHomologyMap R (2 * d)
      (centeredComplexEmbeddingPair d (OpenPartialHomeomorph.univBall c r)
        (continuous_complexUnivBall d c r) (injective_complexUnivBall d c r) v)
      (standardComplexLocalClass R d) = standardComplexLocalClass R d := by
  rw [b6m_centeredEmbedding_relativeHomologyMap_eq R]
  let L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    (r : ℂ) • ContinuousLinearMap.id ℂ (Fin d → ℂ)
  have hL : Function.Injective L := by
    intro w z hwz
    change (r : ℂ) • w = (r : ℂ) • z at hwz
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    exact (smul_right_injective _ hr') hwz
  let A := complexMatrixOfContinuousLinearMap d L
  have hA : A.det ≠ 0 := complexMatrixOfContinuousLinearMap_det_ne_zero d L hL
  have hAL : (A.mulVecLin.toContinuousLinearMap :
      (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) = L :=
    ContinuousLinearMap.ext (complexMatrixOfContinuousLinearMap_mulVec d L)
  apply b6m_complexDifferentiable_preserves_localClass R d A hA
  case hf0 => simp
  rw [hAL]
  simpa only [add_zero] using
    (hasFDerivAt_univBall_complex d c r hr).sub_const
      ((OpenPartialHomeomorph.univBall c r) 0)

theorem b6m_point_excision_bijective {M : Type} [TopologicalSpace M] [T1Space M]
    (U : Set M) (x : M) (hU : IsOpen U) (hx : x ∈ U) (n : ℕ) :
    Function.Bijective (relativeHomologyMap R n (neighborhoodPointComplementPairMap U x)) := by
  have he : b6m_subspacePairMap (TopCat.of M) U {x}ᶜ =
      neighborhoodPointComplementPairMap U x := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext z <;> rfl
  rw [← he]
  exact b6m_closed_support_excision_bijective R hU isClosed_singleton
    (Set.singleton_subset_iff.mpr hx) n

end HodgeLean.Foundations.Program
