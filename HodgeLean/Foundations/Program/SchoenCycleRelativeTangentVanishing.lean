import HodgeLean.Foundations.Program.SchoenCycleRefinedTangentDerivation
import HodgeLean.Foundations.Program.SchoenCycleNativeTangentPullback
import HodgeLean.Foundations.Program.SchoenCycleMorphismSectionAlgebra

/-! # Relative tangent vanishing on actual affine neighbourhoods -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- An injective native tangent map annihilates every relative algebraic tangent derivation on an actual affine refinement.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_relative_tangent_derivations_subsingleton
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
    Subsingleton (Derivation Γ(Y.left, V) Γ(X.left, W.1) ℂ) := by
  let DY := ComplexPoint.localEtaleCoordinates Y e (Point.map f p)
  let V := DY.neighborhood
  letI := s2e_step1_sectionAlgebra Y V
  letI := s2e_step1_sectionAlgebra X W.1
  let φ := s2e_morphismSectionAlgHom X Y f V W.1 hWV
  letI : Algebra Γ(Y.left, V) Γ(X.left, W.1) := φ.toRingHom.toAlgebra
  let ε := s2e_step1_pointEvaluation X W.1 p (s2e_step1_point_preimage X p W.1 hpW)
  letI : Algebra Γ(X.left, W.1) ℂ := ε.toRingHom.toAlgebra
  letI : Algebra Γ(Y.left, V) ℂ := (ε.comp φ).toRingHom.toAlgebra
  letI : IsScalarTower ℂ Γ(Y.left, V) Γ(X.left, W.1) :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  letI : IsScalarTower ℂ Γ(X.left, W.1) ℂ :=
    IsScalarTower.of_algebraMap_eq fun c => (ε.commutes c).symm
  letI : IsScalarTower Γ(Y.left, V) Γ(X.left, W.1) ℂ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower ℂ Γ(Y.left, V) ℂ :=
    IsScalarTower.of_algebraMap_eq fun c => ((ε.comp φ).commutes c).symm
  let J := fderiv ℂ (fun z : Fin d → ℂ =>
    ComplexPoint.localChart Y e (Point.map f p)
      (Point.map f ((ComplexPoint.localChart X d p).symm
        (ComplexPoint.localChart X d p p + z)))) 0
  have hcoord (i : Fin e) :
      fderiv ℂ (fun z : Fin d → ℂ =>
        Point.evaluate W.1 (φ (DY.coordinateAlgHom (MvPolynomial.X i)))
          ((ComplexPoint.localChart X d p).symm
            (ComplexPoint.localChart X d p p + z))) 0 =
      (ContinuousLinearMap.proj i : (Fin e → ℂ) →L[ℂ] ℂ).comp J := by
    have hr := s2e_native_section_differential_restrict X d p (f.left ⁻¹ᵁ V) W.1 hWV hpW
      (f.left.app V (DY.coordinateAlgHom (MvPolynomial.X i)))
    have hf := s2e_native_section_differential_pullback X Y d e f p V DY.mem
      (DY.coordinateAlgHom (MvPolynomial.X i))
    have hy := s2e_native_etale_coordinate_differential Y e (Point.map f p) i
    exact hr.trans (hf.trans (congrArg (fun F : (Fin e → ℂ) →L[ℂ] ℂ => F.comp J) hy))
  apply subsingleton_of_forall_eq (0 : Derivation Γ(Y.left, V) Γ(X.left, W.1) ℂ)
  intro E
  obtain ⟨δ, hδ⟩ := (s2e_native_refined_tangent_derivation_bijective X d p W hpW hW).surjective
    (E.restrictScalars ℂ)
  have hJ : J δ = 0 := by
    ext i
    have hd := congrArg (fun F : Derivation ℂ Γ(X.left, W.1) ℂ =>
      F (φ (DY.coordinateAlgHom (MvPolynomial.X i)))) hδ
    have hz : E (φ (DY.coordinateAlgHom (MvPolynomial.X i))) = 0 :=
      E.map_algebraMap (DY.coordinateAlgHom (MvPolynomial.X i))
    have hj := congrArg (fun F : (Fin d → ℂ) →L[ℂ] ℂ => F δ) (hcoord i)
    exact hj.symm.trans (hd.trans hz)
  have hzero : δ = 0 := ht (by rw [map_zero]; exact hJ)
  ext s
  have hs := congrArg (fun F : Derivation ℂ Γ(X.left, W.1) ℂ => F s) hδ
  rw [hzero] at hs
  change fderiv ℂ (fun z : Fin d → ℂ => Point.evaluate W.1 s
    ((ComplexPoint.localChart X d p).symm
      (ComplexPoint.localChart X d p p + z))) 0 (0 : Fin d → ℂ) = E s at hs
  simpa only [map_zero, Derivation.zero_apply] using hs.symm

end HodgeLean.Foundations.Program
