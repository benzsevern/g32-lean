import HodgeLean.Foundations.Program.SchoenCycleRelativeTangentVanishing
import HodgeLean.Foundations.Program.SchoenCycleCotangentFibreDerivations

/-! # Relative cotangent fibres at actual complex points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- An injective native tangent map makes the actual relative cotangent fibre vanish on an affine refinement.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_relative_cotangent_fibre_subsingleton
    (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (f : X ⟶ Y) (p : ComplexPoint X)
    (W : X.left.affineOpens) (hpW : p.underlying ∈ W.1)
    (hW : W.1 ≤ (ComplexPoint.localEtaleCoordinates X d p).neighborhood)
    (hWV : W.1 ≤ f.left ⁻¹ᵁ (ComplexPoint.localEtaleCoordinates Y e (Point.map f p)).neighborhood)
    (ht : Function.Injective (fderiv ℂ (fun z : Fin d → ℂ =>
      ComplexPoint.localChart Y e (Point.map f p)
        (Point.map f ((ComplexPoint.localChart X d p).symm
          (ComplexPoint.localChart X d p p + z)))) 0)) :
    let V := (ComplexPoint.localEtaleCoordinates Y e (Point.map f p)).neighborhood
    letI := s2e_step1_sectionAlgebra Y V
    letI := s2e_step1_sectionAlgebra X W.1
    let φ := s2e_morphismSectionAlgHom X Y f V W.1 hWV
    letI : Algebra Γ(Y.left, V) Γ(X.left, W.1) := φ.toRingHom.toAlgebra
    let ε := s2e_step1_pointEvaluation X W.1 p (s2e_step1_point_preimage X p W.1 hpW)
    letI : Algebra Γ(X.left, W.1) ℂ := ε.toRingHom.toAlgebra
    letI : Algebra Γ(Y.left, V) ℂ := (ε.comp φ).toRingHom.toAlgebra
    Subsingleton (ℂ ⊗[Γ(X.left, W.1)] Ω[Γ(X.left, W.1)⁄Γ(Y.left, V)]) := by
  let V := (ComplexPoint.localEtaleCoordinates Y e (Point.map f p)).neighborhood
  letI := s2e_step1_sectionAlgebra Y V
  letI := s2e_step1_sectionAlgebra X W.1
  let φ := s2e_morphismSectionAlgHom X Y f V W.1 hWV
  letI : Algebra Γ(Y.left, V) Γ(X.left, W.1) := φ.toRingHom.toAlgebra
  let ε := s2e_step1_pointEvaluation X W.1 p (s2e_step1_point_preimage X p W.1 hpW)
  letI : Algebra Γ(X.left, W.1) ℂ := ε.toRingHom.toAlgebra
  letI : Algebra Γ(Y.left, V) ℂ := (ε.comp φ).toRingHom.toAlgebra
  letI : IsScalarTower Γ(Y.left, V) Γ(X.left, W.1) ℂ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact s2e_cotangent_fibre_subsingleton_of_derivations Γ(Y.left, V) Γ(X.left, W.1) ℂ
    (s2e_relative_tangent_derivations_subsingleton X Y d e f p W hpW hW hWV ht)

end HodgeLean.Foundations.Program
