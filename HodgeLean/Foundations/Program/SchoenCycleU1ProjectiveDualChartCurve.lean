import HodgeLean.Foundations.Program.SchoenCycleU1ProjectivePolynomialCurve
import HodgeLean.Foundations.Program.SchoenCycleU1PolynomialDualParameter
import HodgeLean.Foundations.Program.SchoenCycleU1SpecOver
import Mathlib.RingTheory.DualNumber

/-! # Normalized chart curve representatives of actual projective dual-number points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- Every actual projective dual-number point has a specified normalized
polynomial chart curve representative over the complex base.
Source: Hartshorne, Algebraic Geometry, II.2, II.7 and II.8. -/
theorem s2e_u1_projective_dual_point_chartCurve (n : ℕ)
    (f : s2e_u1_specOver (DualNumber ℂ) ⟶
      Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) :
    ∃ (i : Fin (n + 1))
      (φ : HomogeneousLocalization.Away (UniversalGrading.{0} n)
        (MvPolynomial.X i : UniversalRing.{0} n) →+* DualNumber ℂ),
      s2e_u1_polynomialDualParameter ≫ s2e_u1_projectiveChartCurve i φ = f := by
  classical
  let q := f.left ≫ Limits.pullback.snd (Limits.terminal.from (Spec ↧ℂ))
    (Limits.terminal.from (Proj (UniversalGrading n)))
  have hmem : q (IsLocalRing.closedPoint (DualNumber ℂ)) ∈
      (⊤ : (Proj (UniversalGrading n)).Opens) := trivial
  rw [← iSup_coordinateBasicOpen_eq_top n, Opens.mem_iSup] at hmem
  obtain ⟨i, hi⟩ := hmem
  let e := Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X _ _) zero_lt_one
  have hRange : Set.range q ⊆ Set.range e := by
    change Set.range q ⊆ e.opensRange
    dsimp only [e]
    rw [Proj.opensRange_awayι]
    rintro _ ⟨x, rfl⟩
    have hp := Scheme.preimage_eq_top_of_closedPoint_mem q hi
    have hx : x ∈ q ⁻¹ᵁ Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i) := by
      rw [hp]
      trivial
    exact hx
  let l := IsOpenImmersion.lift e q hRange
  let φ := (Spec.preimage l).hom
  let line := s2e_u1_projectiveChartLine.{0, 0} i φ
  let g0 : Spec (CommRingCat.of (Polynomial ℂ)) ⟶
      ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ) :=
    Limits.pullback.lift (Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)))
      (Spec.map (CommRingCat.ofHom line) ≫ e) (Subsingleton.elim _ _)
  let g := s2e_u1_projectiveChartCurve i φ
  refine ⟨i, φ, ?_⟩
  ext1
  apply Limits.pullback.hom_ext
  · exact (Over.w (s2e_u1_polynomialDualParameter ≫ g)).trans (Over.w f).symm
  · change Spec.map (CommRingCat.ofHom
        (Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ))).toRingHom) ≫
      (g0 ≫ Limits.pullback.snd _ _) = q
    dsimp only [g0]
    rw [Limits.pullback.lift_snd, ← Category.assoc, ← Spec.map_comp]
    have he : CommRingCat.ofHom line ≫ CommRingCat.ofHom
        (Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ))).toRingHom = Spec.preimage l := by
      apply CommRingCat.hom_ext
      exact s2e_u1_projectiveChartLine_dual i φ
    rw [he, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac e q hRange

end HodgeLean.Foundations.Program
