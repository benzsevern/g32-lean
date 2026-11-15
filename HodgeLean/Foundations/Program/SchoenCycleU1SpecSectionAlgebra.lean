import HodgeLean.Foundations.Program.SchoenCycleU1SpecSectionEvaluation
import HodgeLean.Foundations.Program.SchoenCycleU1AffineCharts

/-! # Scalar compatibility of actual affine-source evaluations -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Evaluation by an actual affine complex scheme map preserves its specified
complex scalar structure on every image neighbourhood.
Source: Hartshorne, Algebraic Geometry, II.2, morphisms over a base. -/
def s2e_u1_specSectionAlgebraEvaluation
    (A : Type) [CommRing A] [Algebra ℂ A]
    (X : Over (Spec ↧ℂ)) (f : s2e_u1_specOver A ⟶ X)
    (U : X.left.Opens) (hU : ⊤ ≤ f.left ⁻¹ᵁ U) :
    letI := s2e_step1_sectionAlgebra X U
    Γ(X.left, U) →ₐ[ℂ] A := by
  letI := s2e_step1_sectionAlgebra X U
  refine ⟨s2e_u1_specSectionEvaluation X.left f.left U hU, ?_⟩
  intro c
  have he : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ U le_top ≫
      f.left.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom =
        CommRingCat.ofHom (algebraMap ℂ A) := by
    rw [← Category.assoc (X.hom.appLE _ _ _), Scheme.Hom.appLE_comp_appLE]
    have hf := Over.w f
    change f.left ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) at hf
    rw [hf]
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ A))).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom = _
    rw [Scheme.ΓSpecIso_naturality, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  exact congrArg (fun g : CommRingCat.of ℂ ⟶ CommRingCat.of A => g.hom c) he

/-- An actual affine-source scheme map factors through every affine image
neighbourhood by its actual regular-section evaluation map.
Source: Mathlib, `IsAffineOpen.SpecMap_appLE_fromSpec`; Hartshorne, II.2. -/
theorem s2e_u1_specSectionAlgebraEvaluation_factor
    (A : Type) [CommRing A] [Algebra ℂ A]
    (X : Over (Spec ↧ℂ)) (f : s2e_u1_specOver A ⟶ X)
    (U : X.left.Opens) (hUa : IsAffineOpen U) (hU : ⊤ ≤ f.left ⁻¹ᵁ U) :
    letI := s2e_step1_sectionAlgebra X U
    s2e_u1_specOverMap (s2e_u1_specSectionAlgebraEvaluation A X f U hU) ≫
      s2e_u1_fromSpecOver X U hUa = f := by
  letI := s2e_step1_sectionAlgebra X U
  letI : IsAffine (s2e_u1_specOver A).left := by
    change IsAffine (Spec (CommRingCat.of A))
    infer_instance
  apply Over.OverMorphism.ext
  change Spec.map (f.left.appLE U ⊤ hU ≫
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom) ≫ hUa.fromSpec = f.left
  rw [Spec.map_comp, Category.assoc,
    hUa.SpecMap_appLE_fromSpec f.left (isAffineOpen_top _) hU,
    IsAffineOpen.fromSpec_top, ← Scheme.isoSpec_Spec_hom,
    ← Category.assoc]
  change ((Spec (CommRingCat.of A)).isoSpec.hom ≫
    (Spec (CommRingCat.of A)).isoSpec.inv) ≫ f.left = f.left
  rw [Iso.hom_inv_id, Category.id_comp]

/-- Actual regular-section evaluation commutes with change of the affine
coefficient algebra, including residue and dual-number algebra maps.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_u1_specSectionAlgebraEvaluation_baseChange
    (A C : Type) [CommRing A] [CommRing C] [Algebra ℂ A] [Algebra ℂ C]
    (φ : A →ₐ[ℂ] C) (X : Over (Spec ↧ℂ)) (f : s2e_u1_specOver A ⟶ X)
    (U : X.left.Opens) (hU : ⊤ ≤ f.left ⁻¹ᵁ U)
    (hV : ⊤ ≤ (s2e_u1_specOverMap φ ≫ f).left ⁻¹ᵁ U) :
    letI := s2e_step1_sectionAlgebra X U
    s2e_u1_specSectionAlgebraEvaluation C X (s2e_u1_specOverMap φ ≫ f) U hV =
      φ.comp (s2e_u1_specSectionAlgebraEvaluation A X f U hU) := by
  letI := s2e_step1_sectionAlgebra X U
  apply AlgHom.ext
  intro a
  change s2e_u1_specSectionEvaluation X.left
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f.left) U hV a =
      φ (s2e_u1_specSectionEvaluation X.left f.left U hU a)
  have he := s2e_u1_specSectionEvaluation_comp (Spec (CommRingCat.of A)) X.left
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) f.left U ⊤ hU (by simp) hV
  rw [← he, s2e_u1_specSectionEvaluation_specMap_top]
  rfl

end HodgeLean.Foundations.Program
