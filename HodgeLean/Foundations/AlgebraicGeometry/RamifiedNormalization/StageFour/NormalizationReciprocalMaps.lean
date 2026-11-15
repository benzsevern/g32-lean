import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.LiteralNormalizedChartOpen
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ReciprocalProjectiveGluing
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffineParameterGluing

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Two original-field normalization charts retain simultaneous actual selector and projective parameter morphisms. -/
theorem normalization_reciprocal_maps
    {A B L : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] [Field L]
    (X : Over (Spec ↧ℂ))
    (η : Spec ↧L ⟶ X.left) [IsDominant η] [QuasiCompact η] [QuasiSeparated η]
    [LocallyOfFiniteType (s2b_normalizationOver X η).hom]
    (jA : Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶ X)
    (jB : Over.mk (ComplexPoint.affineSpecStructureMap B) ⟶ X)
    [IsOpenImmersion jA.left] [IsOpenImmersion jB.left]
    (hcover : ∀ x : X.left, (∃ a, jA.left a = x) ∨ ∃ b, jB.left b = x)
    (f : A →+* L) (g : B →+* L)
    (hf : Spec.map (CommRingCat.ofHom f) ≫ jA.left = η)
    (hg : Spec.map (CommRingCat.ofHom g) ≫ jB.left = η)
    (q t : normalizedChart f) (q' s : normalizedChart g)
    (hqq : (q : L) = (q' : L)) (hts : (t : L) * (s : L) = 1) :
    letI := ((StageTwo.integralCoeff f).comp (algebraMap ℂ A)).toAlgebra
    letI := ((StageTwo.integralCoeff g).comp (algebraMap ℂ B)).toAlgebra
    ∃ (JA : Over.mk (ComplexPoint.affineSpecStructureMap (normalizedChart f)) ⟶
        s2b_normalizationOver X η)
      (JB : Over.mk (ComplexPoint.affineSpecStructureMap (normalizedChart g)) ⟶
        s2b_normalizationOver X η)
      (Q : s2b_normalizationOver X η ⟶
        Over.mk (ComplexPoint.affineSpecStructureMap (Polynomial ℂ)))
      (T : s2b_normalizationOver X η ⟶ projectiveLine),
      IsOpenImmersion JA.left ∧ IsOpenImmersion JB.left ∧
      (JA.left ≫ η.fromNormalization =
        Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff f)) ≫ jA.left) ∧
      (JB.left ≫ η.fromNormalization =
        Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff g)) ≫ jB.left) ∧
      Set.range JA.left = η.fromNormalization ⁻¹' Set.range jA.left ∧
      Set.range JB.left = η.fromNormalization ⁻¹' Set.range jB.left ∧
      (∀ x : (s2b_normalizationOver X η).left,
        (∃ a, JA.left a = x) ∨ ∃ b, JB.left b = x) ∧
      JA ≫ Q = affineLineParameter q ∧ JB ≫ Q = affineLineParameter q' ∧
      JA ≫ T = projectiveLineChart 1 t ∧ JB ≫ T = projectiveLineChart 0 s ∧
      Spec.map (CommRingCat.ofHom (normalizedChart f).subtype) ≫ JA.left = η.toNormalization ∧
      Spec.map (CommRingCat.ofHom (normalizedChart g).subtype) ≫ JB.left = η.toNormalization := by
  letI := ((StageTwo.integralCoeff f).comp (algebraMap ℂ A)).toAlgebra
  letI := ((StageTwo.integralCoeff g).comp (algebraMap ℂ B)).toAlgebra
  obtain ⟨JA, hJA, hbA, hrA, hpA⟩ := literal_normalized_chart_open X η jA f hf
  obtain ⟨JB, hJB, hbB, hrB, hpB⟩ := literal_normalized_chart_open X η jB g hg
  haveI : IsOpenImmersion JA.left := hJA
  haveI : IsOpenImmersion JB.left := hJB
  have hcov : ∀ x : (s2b_normalizationOver X η).left,
      (∃ a, JA.left a = x) ∨ ∃ b, JB.left b = x := by
    intro x
    rcases hcover (η.fromNormalization x) with h | h
    · left
      change x ∈ Set.range JA.left
      rw [hrA]
      exact h
    · right
      change x ∈ Set.range JB.left
      rw [hrB]
      exact h
  haveI : IsIntegral (s2b_normalizationOver X η).left := by
    change IsIntegral η.normalization
    infer_instance
  haveI : IsDominant η.toNormalization := inferInstance
  haveI : QuasiCompact η.toNormalization := inferInstance
  obtain ⟨Q, hQ, _⟩ := equal_field_affine_parameter_gluing
    (s2b_normalizationOver X η) η.toNormalization JA JB hcov
    (normalizedChart f).subtype (normalizedChart g).subtype hpA hpB q q' hqq
  obtain ⟨T, hT, _⟩ := reciprocal_projective_chart_gluing
    (s2b_normalizationOver X η) η.toNormalization JA JB hcov
    (normalizedChart f).subtype (normalizedChart g).subtype hpA hpB t s hts
  exact ⟨JA, JB, Q, T, hJA, hJB, hbA, hbB, hrA, hrB, hcov, hQ.1, hQ.2, hT.1, hT.2, hpA, hpB⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
