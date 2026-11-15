import HodgeLean.Foundations.Program.SchoenCycleS3LinearProj
import HodgeLean.Foundations.Program.SchoenPolynomialProjectiveSpace
import HodgeLean.Foundations.Program.SchoenProjMapBase

/-! # Projective linear isomorphisms over the coefficient field -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- Polynomial linear substitution fixes the degree-zero coefficient ring pointwise. -/
theorem s2e_gradedLinearSubstitution_zero {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ))
    (a : homogeneousSubmodule (Fin n) ℂ 0) :
    s2e_gradedLinearSubstitution e (a : MvPolynomial (Fin n) ℂ) = a := by
  have ha : C ((ProjectiveSpace.degreeZeroEquiv (Fin n) ℂ) a) =
      (a : MvPolynomial (Fin n) ℂ) :=
    congrArg Subtype.val ((ProjectiveSpace.degreeZeroEquiv (Fin n) ℂ).symm_apply_apply a)
  rw [← ha]
  change s2e_linearSubstitution e.toLinearMap (C _) = _
  simp only [s2e_linearSubstitution, aeval_C, MvPolynomial.algebraMap_eq]

/-- The polynomial projective automorphism preserves the specified coefficient structure map. -/
theorem s2e_linearProjIso_toSpecZero {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    (s2e_linearProjIso e).hom ≫ Proj.toSpecZero (homogeneousSubmodule (Fin n) ℂ) =
      Proj.toSpecZero (homogeneousSubmodule (Fin n) ℂ) := by
  have h := s2_projMap_toSpecZero _ _ (s2e_gradedLinearSubstitution e)
    (s2e_gradedLinearSubstitution_irrelevant e) (RingHom.id _)
    (fun a => (s2e_gradedLinearSubstitution_zero e a).symm)
  simpa only [s2e_linearProjIso, CommRingCat.ofHom_id, Spec.map_id,
    Category.comp_id] using h

/-- Transfer the polynomial coordinate automorphism to the actual projective space. -/
def s2e_linearProjectiveSpaceIso {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    ProjectiveSpace (Fin n) (Spec ↧ℂ) ≅ ProjectiveSpace (Fin n) (Spec ↧ℂ) :=
  (s2_polynomialProjectiveSpaceIso ℂ (Fin n)).symm ≪≫ s2e_linearProjIso e ≪≫
    s2_polynomialProjectiveSpaceIso ℂ (Fin n)

/-- The transferred automorphism retains the complex structure morphism. -/
theorem s2e_linearProjectiveSpaceIso_toBase {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    (s2e_linearProjectiveSpaceIso e).hom ≫ ProjectiveSpace.toBase (Fin n) (Spec ↧ℂ) =
      ProjectiveSpace.toBase (Fin n) (Spec ↧ℂ) := by
  simp only [s2e_linearProjectiveSpaceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    s2_polynomialProjectiveSpaceIso_toBase]
  rw [← Category.assoc (s2e_linearProjIso e).hom, s2e_linearProjIso_toSpecZero]
  rw [← s2_polynomialProjectiveSpaceIso_toBase, Iso.inv_hom_id_assoc]

/-- A coordinate basis change gives an isomorphism of projective spaces over the complex base. -/
def s2e_linearProjectiveOverIso {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    Over.mk (ProjectiveSpace.toBase (Fin n) (Spec ↧ℂ)) ≅
      Over.mk (ProjectiveSpace.toBase (Fin n) (Spec ↧ℂ)) :=
  Over.isoMk (s2e_linearProjectiveSpaceIso e) (s2e_linearProjectiveSpaceIso_toBase e)

end HodgeLean.Foundations.Program
