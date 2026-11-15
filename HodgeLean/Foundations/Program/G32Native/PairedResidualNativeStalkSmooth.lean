import HodgeLean.Foundations.Program.G32Native.PairedResidualEvaluatedLocalization
import HodgeLean.Foundations.Program.G32Native.PairedResidualNativeCotangentInjection
import HodgeLean.Foundations.Program.G32Native.PairedResidualStalkEvaluation
import HodgeLean.Foundations.Program.G32Native.PairedResidualRefinedSectionSmooth

/-! # Relative formal smoothness of the actual native source stalk -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- A native submersion makes the actual source stalk formally smooth over
the original target section algebra, using the actual section germ map.
Source: EGA IV, 17.11.1; Hartshorne, Algebraic Geometry, II.8. -/
theorem residual_native_stalk_formallySmooth
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (f : X ⟶ Y) (p : ComplexPoint X)
    (W : X.left.affineOpens) (hpW : p.underlying ∈ W.1)
    (hW : W.1 ≤ (localEtaleCoordinates X d p).neighborhood)
    (hWV : W.1 ≤ f.left ⁻¹ᵁ (localEtaleCoordinates Y e (Point.map f p)).neighborhood)
    (ht : Function.Surjective (fderiv ℂ (fun z : Fin d → ℂ =>
      localChart Y e (Point.map f p)
        (Point.map f ((localChart X d p).symm (localChart X d p p + z)))) 0)) :
    let DY := localEtaleCoordinates Y e (Point.map f p)
    letI := s2e_step1_sectionAlgebra Y DY.neighborhood
    letI := s2e_step1_sectionAlgebra X W.1
    let L := X.left.presheaf.stalk p.underlying
    letI : Algebra ℂ L := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
    let G := s2e_complex_section_germ X W.1 p.underlying hpW
    let φ := s2e_morphismSectionAlgHom X Y f DY.neighborhood W.1 hWV
    letI : Algebra Γ(Y.left, DY.neighborhood) L := (G.comp φ).toAlgebra
    Algebra.FormallySmooth Γ(Y.left, DY.neighborhood) L := by
  dsimp only
  let DY := localEtaleCoordinates Y e (Point.map f p)
  letI := s2e_step1_sectionAlgebra Y DY.neighborhood
  letI := s2e_step1_sectionAlgebra X W.1
  let S := Γ(Y.left, DY.neighborhood)
  let A := Γ(X.left, W.1)
  let L := X.left.presheaf.stalk p.underlying
  letI : Algebra ℂ L := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
  let G := s2e_complex_section_germ X W.1 p.underlying hpW
  let φ := s2e_morphismSectionAlgHom X Y f DY.neighborhood W.1 hWV
  letI : Algebra S A := φ.toAlgebra
  letI : Algebra A L := G.toAlgebra
  letI : Algebra S L := (G.comp φ).toAlgebra
  letI : IsScalarTower ℂ S A := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  letI : IsScalarTower ℂ A L := IsScalarTower.of_algebraMap_eq' G.comp_algebraMap.symm
  letI : IsScalarTower ℂ S L := IsScalarTower.of_algebraMap_eq' (G.comp φ).comp_algebraMap.symm
  letI : IsScalarTower S A L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let P := (W.2.primeIdealOf ⟨p.underlying, hpW⟩).asIdeal
  letI : IsLocalization.AtPrime L P := W.2.isLocalization_stalk ⟨p.underlying, hpW⟩
  letI : Algebra.FormallyEtale A L := Algebra.FormallyEtale.of_isLocalization P.primeCompl
  letI : Algebra.IsStandardSmoothOfRelativeDimension d ℂ A :=
    residual_refined_section_standardSmooth X d p W hW
  letI : Algebra.IsStandardSmoothOfRelativeDimension e ℂ S :=
    residual_refined_section_standardSmooth Y e (Point.map f p)
      ⟨DY.neighborhood, DY.isAffine⟩ le_rfl
  letI : Algebra.IsStandardSmooth ℂ A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  letI : Algebra.IsStandardSmooth ℂ S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth e
  let εL := s2e_complex_point_augmentation X p
  let εA := s2e_step1_pointEvaluation X W.1 p (s2e_step1_point_preimage X p W.1 hpW)
  let εS := s2e_step1_pointEvaluation Y DY.neighborhood (Point.map f p)
    (s2e_step1_point_preimage Y (Point.map f p) DY.neighborhood DY.mem)
  have hA : εL.comp (IsScalarTower.toAlgHom ℂ A L) = εA :=
    residual_stalk_section_evaluation X p W.1 hpW
  have hS : εA.comp (IsScalarTower.toAlgHom ℂ S A) = εS :=
    residual_section_evaluation_pullback X Y f p DY.neighborhood W.1 hpW DY.mem hWV
  apply residual_formallySmooth_localization_with_evaluations ℂ S A L εL εA εS hA hS
  exact residual_native_cotangent_fibre_injective X Y d e f p W hpW hWV ht

#print axioms residual_native_stalk_formallySmooth
end HodgeLean.Foundations.Program.G32Native
