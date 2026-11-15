import HodgeLean.Foundations.Program.SchoenCycleRefinedTangentDerivation
import HodgeLean.Foundations.Program.SchoenCycleNativeTangentPullback
import HodgeLean.Foundations.Program.SchoenCycleMorphismSectionAlgebra

/-! # Lifting actual algebraic tangent derivations through a native submersion -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Surjectivity of the native tangent map lifts every target tangent derivation
to the actual source section ring, with the original section pullback.
Source: Hartshorne, Algebraic Geometry, II.8; the analytic chain rule. -/
theorem residual_native_tangent_derivation_lift
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
    let εX := s2e_step1_pointEvaluation X W.1 p (s2e_step1_point_preimage X p W.1 hpW)
    let εY := s2e_step1_pointEvaluation Y DY.neighborhood (Point.map f p)
      (s2e_step1_point_preimage Y (Point.map f p) DY.neighborhood DY.mem)
    letI : Algebra Γ(X.left, W.1) ℂ := εX.toRingHom.toAlgebra
    letI : Algebra Γ(Y.left, DY.neighborhood) ℂ := εY.toRingHom.toAlgebra
    ∀ E : Derivation ℂ Γ(Y.left, DY.neighborhood) ℂ,
      ∃ D : Derivation ℂ Γ(X.left, W.1) ℂ,
        ∀ a, D (s2e_morphismSectionAlgHom X Y f DY.neighborhood W.1 hWV a) = E a := by
  dsimp only
  let DY := localEtaleCoordinates Y e (Point.map f p)
  letI := s2e_step1_sectionAlgebra Y DY.neighborhood
  letI := s2e_step1_sectionAlgebra X W.1
  let εX := s2e_step1_pointEvaluation X W.1 p (s2e_step1_point_preimage X p W.1 hpW)
  let εY := s2e_step1_pointEvaluation Y DY.neighborhood (Point.map f p)
    (s2e_step1_point_preimage Y (Point.map f p) DY.neighborhood DY.mem)
  letI : Algebra Γ(X.left, W.1) ℂ := εX.toRingHom.toAlgebra
  letI : Algebra Γ(Y.left, DY.neighborhood) ℂ := εY.toRingHom.toAlgebra
  intro E
  have hb : Function.Bijective (fun v : Fin e → ℂ =>
      s2e_nativeSectionTangentDerivation Y e (Point.map f p) DY.neighborhood DY.mem v) :=
    s2e_native_affine_tangent_derivation_bijective Y e (Point.map f p)
  obtain ⟨v, hv⟩ := hb.surjective E
  obtain ⟨u, hu⟩ := ht v
  refine ⟨s2e_nativeSectionTangentDerivation X d p W.1 hpW u, ?_⟩
  intro a
  have hr := s2e_native_section_differential_restrict X d p
    (f.left ⁻¹ᵁ DY.neighborhood) W.1 hWV hpW (f.left.app DY.neighborhood a)
  have hf := s2e_native_section_differential_pullback X Y d e f p DY.neighborhood DY.mem a
  have hh := congrArg (fun F : (Fin d → ℂ) →L[ℂ] ℂ => F u) (hr.trans hf)
  change _ = _ at hh
  change fderiv ℂ (fun z : Fin d → ℂ =>
    Point.evaluate W.1 (s2e_morphismSectionAlgHom X Y f DY.neighborhood W.1 hWV a)
      ((localChart X d p).symm (localChart X d p p + z))) 0 u = E a
  refine hh.trans ?_
  rw [ContinuousLinearMap.comp_apply, hu]
  exact congrArg (fun D : Derivation ℂ Γ(Y.left, DY.neighborhood) ℂ => D a) hv

#print axioms residual_native_tangent_derivation_lift
end HodgeLean.Foundations.Program.G32Native
