import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Etale integral-closure charts of the actual normalization -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Etaleness of the actual affine integral-closure algebras gives etaleness
of the relative normalization projection. -/
theorem s2e_c1_normalization_etale_of_affine_integralClosures
    {T B : Scheme} (f : T ⟶ B) [QuasiCompact f] [QuasiSeparated f]
    (h : ∀ U : B.affineOpens,
      letI := (f.app U.1).hom.toAlgebra
      Algebra.Etale Γ(B, U.1) (integralClosure Γ(B, U.1) Γ(T, f ⁻¹ᵁ U.1))) :
    Etale f.fromNormalization := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale) f.normalizationOpenCover
  intro U
  rw [f.ι_fromNormalization]
  letI := (f.app U.1).hom.toAlgebra
  haveI : Etale (Spec.map (f.normalizationDiagramMap.app (.op U.1))) := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    exact RingHom.etale_algebraMap.mpr (h U)
  infer_instance

/-- Over an affine base, etaleness of its single global integral-closure
algebra suffices for the actual normalization projection. -/
theorem s2e_c1_affine_normalization_etale_of_integralClosure
    {T B : Scheme} [IsAffine B] (f : T ⟶ B) [QuasiCompact f] [QuasiSeparated f]
    (h : letI := (f.app ⊤).hom.toAlgebra
      Algebra.Etale Γ(B, ⊤) (integralClosure Γ(B, ⊤) Γ(T, f ⁻¹ᵁ ⊤))) :
    Etale f.fromNormalization := by
  let U : B.affineOpens := ⟨⊤, isAffineOpen_top B⟩
  let j := f.normalizationOpenCover.f U
  haveI : IsIso j := isIso_of_isOpenImmersion_of_opensRange_eq_top j (by
    rw [← f.fromNormalization_preimage U]
    simp only [U, Scheme.Hom.preimage_top])
  haveI : Etale (j ≫ f.fromNormalization) := by
    dsimp only [j]
    rw [f.ι_fromNormalization]
    letI := (f.app ⊤).hom.toAlgebra
    haveI : Etale (Spec.map (f.normalizationDiagramMap.app (.op U.1))) := by
      apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      exact RingHom.etale_algebraMap.mpr h
    infer_instance
  have heq : f.fromNormalization = inv j ≫ (j ≫ f.fromNormalization) := by
    simp only [IsIso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

end HodgeLean.Foundations.Program
