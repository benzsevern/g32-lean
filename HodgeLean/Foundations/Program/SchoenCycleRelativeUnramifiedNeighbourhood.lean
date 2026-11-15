import HodgeLean.Foundations.Program.SchoenCycleRelativeCotangentFibre
import HodgeLean.Foundations.Program.SchoenCycleFieldFibreSupport

/-! # Relative unramified localizations at actual complex points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Native tangent injectivity gives a regular section nonzero at the point whose actual localization is formally unramified over the target chart.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald, Corollary 2.7. -/
theorem s2e_relative_unramified_localization_neighbourhood
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
    ∃ a : Γ(X.left, W.1), ε a ≠ 0 ∧
      Algebra.FormallyUnramified Γ(Y.left, V) (Localization.Away a) := by
  let DY := ComplexPoint.localEtaleCoordinates Y e (Point.map f p)
  let V := DY.neighborhood
  letI := s2e_step1_sectionAlgebra Y V
  letI := s2e_step1_sectionAlgebra X W.1
  let φ := s2e_morphismSectionAlgHom X Y f V W.1 hWV
  letI : Algebra Γ(Y.left, V) Γ(X.left, W.1) := φ.toRingHom.toAlgebra
  let ε := s2e_step1_pointEvaluation X W.1 p (s2e_step1_point_preimage X p W.1 hpW)
  letI : Algebra Γ(X.left, W.1) ℂ := ε.toRingHom.toAlgebra
  letI : Algebra Γ(Y.left, V) ℂ := (ε.comp φ).toRingHom.toAlgebra
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth (n := d) X.hom
  haveI : LocallyOfFiniteType (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  letI : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  letI : Algebra.FiniteType Γ(Y.left, V) Γ(X.left, W.1) :=
    RingHom.finiteType_algebraMap.mp (f.left.finiteType_appLE DY.isAffine W.2 hWV)
  let q : PrimeSpectrum Γ(X.left, W.1) :=
    ⟨RingHom.ker ε.toRingHom, RingHom.ker_isPrime ε.toRingHom⟩
  letI : q.asIdeal.IsPrime := q.isPrime
  have hq : Algebra.IsUnramifiedAt Γ(Y.left, V) q.asIdeal :=
    s2e_isUnramifiedAt_of_field_cotangent_fibre Γ(Y.left, V) Γ(X.left, W.1) ℂ
      ε.toRingHom q rfl
      (s2e_relative_cotangent_fibre_subsingleton X Y d e f p W hpW hW hWV ht)
  letI : Algebra.IsUnramifiedAt Γ(Y.left, V) q.asIdeal := hq
  obtain ⟨a, ha, hu⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt
    (R := Γ(Y.left, V)) q.asIdeal
  exact ⟨a, ha, hu⟩

end HodgeLean.Foundations.Program
