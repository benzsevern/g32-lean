import HodgeLean.Foundations.Program.SchoenCycleNativeSectionDifferential
import HodgeLean.Foundations.Program.SchoenCycleSectionEvaluation
import Mathlib.RingTheory.Derivation.Basic
import HodgeLean.Foundations.Program.SchoenCycleEtaleCotangentBasis

/-! # Algebraic derivations from native tangent vectors -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Differentiating actual regular sections in a native tangent direction gives an algebraic derivation at the point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.8. -/
def s2e_nativeSectionTangentDerivation
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U)
    (δ : Fin d → ℂ) :
    letI := s2e_step1_sectionAlgebra X U
    let φ := s2e_step1_pointEvaluation X U p (s2e_step1_point_preimage X p U hp)
    letI : Algebra Γ(X.left, U) ℂ := φ.toRingHom.toAlgebra
    Derivation ℂ Γ(X.left, U) ℂ := by
  letI := s2e_step1_sectionAlgebra X U
  let φ := s2e_step1_pointEvaluation X U p (s2e_step1_point_preimage X p U hp)
  letI : Algebra Γ(X.left, U) ℂ := φ.toRingHom.toAlgebra
  let v := fun z : Fin d → ℂ => (ComplexPoint.localChart X d p).symm
    (ComplexPoint.localChart X d p p + z)
  let D : Γ(X.left, U) →ₗ[ℂ] ℂ := {
    toFun := fun s => fderiv ℂ (fun z => Point.evaluate U s (v z)) 0 δ
    map_add' := by
      intro s t
      exact congrArg (fun F : (Fin d → ℂ) →L[ℂ] ℂ => F δ)
        (s2e_native_section_differential_add X d p U hp s t)
    map_smul' := by
      intro c s
      have hsmul : (fun z => Point.evaluate U (c • s) (v z)) =
          c • (fun z => Point.evaluate U s (v z)) := by
        funext z
        exact s2e_regular_evaluation_smul X U (v z) c s
      rw [hsmul, fderiv_const_smul
        (s2e_native_section_analytic X d p U hp s).differentiableAt c]
      rfl }
  refine Derivation.mk' D ?_
  intro s t
  change fderiv ℂ (fun z => Point.evaluate U (s * t) (v z)) 0 δ =
    φ s * fderiv ℂ (fun z => Point.evaluate U t (v z)) 0 δ +
    φ t * fderiv ℂ (fun z => Point.evaluate U s (v z)) 0 δ
  have hs : φ s = Point.evaluate U s p :=
    (s2e_regular_evaluation_eq_pointEvaluation X U p hp
      (s2e_step1_point_preimage X p U hp) s).symm
  have ht : φ t = Point.evaluate U t p :=
    (s2e_regular_evaluation_eq_pointEvaluation X U p hp
      (s2e_step1_point_preimage X p U hp) t).symm
  rw [hs, ht]
  exact congrArg (fun F : (Fin d → ℂ) →L[ℂ] ℂ => F δ)
    (s2e_native_section_differential_mul X d p U hp s t)

example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U)
    (δ : Fin d → ℂ) (s : Γ(X.left, U)) :
    s2e_nativeSectionTangentDerivation X d p U hp δ s =
      fderiv ℂ (fun z : Fin d → ℂ => Point.evaluate U s
        ((ComplexPoint.localChart X d p).symm
          (ComplexPoint.localChart X d p p + z))) 0 δ := rfl

/-- Native tangent vectors identify bijectively with algebraic tangent derivations on the chosen actual etale neighbourhood.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_native_affine_tangent_derivation_bijective
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) :
    let D := ComplexPoint.localEtaleCoordinates X d p
    letI := s2e_step1_sectionAlgebra X D.neighborhood
    let ε := s2e_step1_pointEvaluation X D.neighborhood p
      (s2e_step1_point_preimage X p D.neighborhood D.mem)
    letI : Algebra Γ(X.left, D.neighborhood) ℂ := ε.toRingHom.toAlgebra
    Function.Bijective (fun δ : Fin d → ℂ =>
      s2e_nativeSectionTangentDerivation X d p D.neighborhood D.mem δ) := by
  let D := ComplexPoint.localEtaleCoordinates X d p
  letI := s2e_step1_sectionAlgebra X D.neighborhood
  let ε := s2e_step1_pointEvaluation X D.neighborhood p
    (s2e_step1_point_preimage X p D.neighborhood D.mem)
  letI : Algebra Γ(X.left, D.neighborhood) ℂ := ε.toRingHom.toAlgebra
  letI : IsScalarTower ℂ Γ(X.left, D.neighborhood) ℂ :=
    IsScalarTower.of_algebraMap_eq fun c => (ε.commutes c).symm
  have hv (δ : Fin d → ℂ) (i : Fin d) :
      s2e_nativeSectionTangentDerivation X d p D.neighborhood D.mem δ
        (D.coordinateAlgHom (MvPolynomial.X i)) = δ i := by
    change fderiv ℂ (fun z : Fin d → ℂ =>
      Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X i))
        ((ComplexPoint.localChart X d p).symm
          (ComplexPoint.localChart X d p p + z))) 0 δ = δ i
    exact congrArg (fun F : (Fin d → ℂ) →L[ℂ] ℂ => F δ)
      (s2e_native_etale_coordinate_differential X d p i)
  constructor
  · intro δ η he
    funext i
    have hi := congrArg (fun F : Derivation ℂ Γ(X.left, D.neighborhood) ℂ =>
      F (D.coordinateAlgHom (MvPolynomial.X i))) he
    exact (hv δ i).symm.trans (hi.trans (hv η i))
  · intro E
    let δ : Fin d → ℂ := fun i => E (D.coordinateAlgHom (MvPolynomial.X i))
    refine ⟨δ, ?_⟩
    apply s2e_etale_coordinate_derivation_ext _ D.coordinateAlgHom D.etale ℂ
    intro i
    exact hv δ i

end HodgeLean.Foundations.Program
