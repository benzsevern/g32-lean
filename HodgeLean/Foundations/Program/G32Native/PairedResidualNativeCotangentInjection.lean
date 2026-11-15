import HodgeLean.Foundations.Program.G32Native.PairedResidualTangentLift
import HodgeLean.Foundations.Program.G32Native.PairedResidualEvaluationPullback
import HodgeLean.Foundations.Program.G32Native.PairedResidualDifferentialInjection
/-! # Actual affine cotangent injection from native tangent surjectivity -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- A native submersion induces an injection of the actual cotangent fibres
of the original affine section pullback at the specified complex point.
Source: Hartshorne, Algebraic Geometry, II.8. -/
theorem residual_native_cotangent_fibre_injective
    (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (f : X ⟶ Y) (p : ComplexPoint X)
    (W : X.left.affineOpens) (hpW : p.underlying ∈ W.1)
    (hWV : W.1 ≤ f.left ⁻¹ᵁ (localEtaleCoordinates Y e (Point.map f p)).neighborhood)
    (ht : Function.Surjective (fderiv ℂ (fun z : Fin d → ℂ =>
      localChart Y e (Point.map f p)
        (Point.map f ((localChart X d p).symm (localChart X d p p + z)))) 0)) :
    let DY := localEtaleCoordinates Y e (Point.map f p)
    letI := s2e_step1_sectionAlgebra Y DY.neighborhood
    letI := s2e_step1_sectionAlgebra X W.1
    let φ := s2e_morphismSectionAlgHom X Y f DY.neighborhood W.1 hWV
    let εX := s2e_step1_pointEvaluation X W.1 p (s2e_step1_point_preimage X p W.1 hpW)
    let εY := s2e_step1_pointEvaluation Y DY.neighborhood (Point.map f p)
      (s2e_step1_point_preimage Y (Point.map f p) DY.neighborhood DY.mem)
    letI : Algebra Γ(Y.left, DY.neighborhood) Γ(X.left, W.1) := φ.toRingHom.toAlgebra
    letI : Algebra Γ(X.left, W.1) ℂ := εX.toRingHom.toAlgebra
    letI : Algebra Γ(Y.left, DY.neighborhood) ℂ := εY.toRingHom.toAlgebra
    letI : IsScalarTower ℂ Γ(Y.left, DY.neighborhood) Γ(X.left, W.1) :=
      IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    letI : IsScalarTower ℂ Γ(X.left, W.1) ℂ :=
      IsScalarTower.of_algebraMap_eq fun c => (εX.commutes c).symm
    letI : IsScalarTower ℂ Γ(Y.left, DY.neighborhood) ℂ :=
      IsScalarTower.of_algebraMap_eq fun c => (εY.commutes c).symm
    letI : IsScalarTower Γ(Y.left, DY.neighborhood) Γ(X.left, W.1) ℂ :=
      IsScalarTower.of_algebraMap_eq fun a =>
        (DFunLike.congr_fun (congrArg AlgHom.toRingHom
          (residual_section_evaluation_pullback X Y f p DY.neighborhood W.1 hpW DY.mem hWV)) a).symm
    Function.Injective
      (residualDifferentialFibreMap ℂ Γ(Y.left, DY.neighborhood) Γ(X.left, W.1) ℂ) := by
  dsimp only
  let DY := localEtaleCoordinates Y e (Point.map f p)
  letI := s2e_step1_sectionAlgebra Y DY.neighborhood
  letI := s2e_step1_sectionAlgebra X W.1
  let φ := s2e_morphismSectionAlgHom X Y f DY.neighborhood W.1 hWV
  let εX := s2e_step1_pointEvaluation X W.1 p (s2e_step1_point_preimage X p W.1 hpW)
  let εY := s2e_step1_pointEvaluation Y DY.neighborhood (Point.map f p)
      (s2e_step1_point_preimage Y (Point.map f p) DY.neighborhood DY.mem)
  letI : Algebra Γ(Y.left, DY.neighborhood) Γ(X.left, W.1) := φ.toRingHom.toAlgebra
  letI : Algebra Γ(X.left, W.1) ℂ := εX.toRingHom.toAlgebra
  letI : Algebra Γ(Y.left, DY.neighborhood) ℂ := εY.toRingHom.toAlgebra
  letI : IsScalarTower ℂ Γ(Y.left, DY.neighborhood) Γ(X.left, W.1) :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  letI : IsScalarTower ℂ Γ(X.left, W.1) ℂ :=
    IsScalarTower.of_algebraMap_eq fun c => (εX.commutes c).symm
  letI : IsScalarTower ℂ Γ(Y.left, DY.neighborhood) ℂ :=
    IsScalarTower.of_algebraMap_eq fun c => (εY.commutes c).symm
  letI : IsScalarTower Γ(Y.left, DY.neighborhood) Γ(X.left, W.1) ℂ :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (DFunLike.congr_fun (congrArg AlgHom.toRingHom
        (residual_section_evaluation_pullback X Y f p DY.neighborhood W.1 hpW DY.mem hWV)) a).symm
  apply residual_differential_fibre_injective_of_tangent_lift
  exact residual_native_tangent_derivation_lift X Y d e f p W hpW hWV ht

#print axioms residual_native_cotangent_fibre_injective
end HodgeLean.Foundations.Program.G32Native
