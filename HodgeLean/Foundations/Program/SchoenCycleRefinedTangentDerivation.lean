import HodgeLean.Foundations.Program.SchoenCycleNativeTangentDerivation
import HodgeLean.Foundations.Program.SchoenCycleAffineCoordinateRestriction

/-! # Tangent derivations on refined actual affine neighbourhoods -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Native tangent vectors give all algebraic tangent derivations on every smaller affine neighbourhood of the chosen etale chart.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_native_refined_tangent_derivation_bijective
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (W : X.left.affineOpens) (hpW : p.underlying ∈ W.1)
    (hW : W.1 ≤ (ComplexPoint.localEtaleCoordinates X d p).neighborhood) :
    letI := s2e_step1_sectionAlgebra X W.1
    let ε := s2e_step1_pointEvaluation X W.1 p (s2e_step1_point_preimage X p W.1 hpW)
    letI : Algebra Γ(X.left, W.1) ℂ := ε.toRingHom.toAlgebra
    Function.Bijective (fun δ : Fin d → ℂ =>
      s2e_nativeSectionTangentDerivation X d p W.1 hpW δ) := by
  let D := ComplexPoint.localEtaleCoordinates X d p
  letI := s2e_step1_sectionAlgebra X D.neighborhood
  letI := s2e_step1_sectionAlgebra X W.1
  let ε := s2e_step1_pointEvaluation X W.1 p (s2e_step1_point_preimage X p W.1 hpW)
  letI : Algebra Γ(X.left, W.1) ℂ := ε.toRingHom.toAlgebra
  letI : IsScalarTower ℂ Γ(X.left, W.1) ℂ :=
    IsScalarTower.of_algebraMap_eq fun c => (ε.commutes c).symm
  let ρ := s2e_sectionRestrictionAlgHom X D.neighborhood W.1 hW
  let coord := ρ.comp D.coordinateAlgHom
  have hcoord : coord.toRingHom.Etale :=
    RingHom.Etale.stableUnderComposition _ _ D.etale
      (s2e_affine_section_restriction_etale X ⟨D.neighborhood, D.isAffine⟩ W hW)
  have hv (δ : Fin d → ℂ) (i : Fin d) :
      s2e_nativeSectionTangentDerivation X d p W.1 hpW δ (coord (MvPolynomial.X i)) = δ i := by
    have hr := s2e_native_section_differential_restrict X d p D.neighborhood W.1 hW hpW
      (D.coordinateAlgHom (MvPolynomial.X i))
    have he := hr.trans (s2e_native_etale_coordinate_differential X d p i)
    exact congrArg (fun F : (Fin d → ℂ) →L[ℂ] ℂ => F δ) he
  constructor
  · intro δ η he
    funext i
    have hi := congrArg (fun F : Derivation ℂ Γ(X.left, W.1) ℂ => F (coord (MvPolynomial.X i))) he
    exact (hv δ i).symm.trans (hi.trans (hv η i))
  · intro E
    let δ : Fin d → ℂ := fun i => E (coord (MvPolynomial.X i))
    refine ⟨δ, ?_⟩
    apply s2e_etale_coordinate_derivation_ext _ coord hcoord ℂ
    intro i
    exact hv δ i

end HodgeLean.Foundations.Program
