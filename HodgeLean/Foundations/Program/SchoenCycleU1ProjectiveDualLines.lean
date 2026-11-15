import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveChartAlgebra
import HodgeLean.Foundations.Program.SchoenCycleU1SpecOver
import Mathlib.RingTheory.DualNumber

/-! # Polynomial line representatives of actual projective dual-number points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- Every actual dual-number point of complex projective space is the restriction
of an actual polynomial line family, over the specified complex base.
Source: Hartshorne, Algebraic Geometry, II.2, II.7 and II.8, standard charts and tangent vectors. -/
theorem s2e_u1_projective_dual_point_polynomial_curve (n : ℕ)
    (f : s2e_u1_specOver (DualNumber ℂ) ⟶
      Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) :
    ∃ g : s2e_u1_specOver (Polynomial ℂ) ⟶
        Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)),
      s2e_u1_specOverMap (Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ))) ≫ g = f := by
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
  let line := s2e_u1_projectiveChartLine i φ
  let g0 : Spec (CommRingCat.of (Polynomial ℂ)) ⟶
      ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ) :=
    Limits.pullback.lift (Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)))
      (Spec.map (CommRingCat.ofHom line) ≫ e) (Subsingleton.elim _ _)
  let g : s2e_u1_specOver (Polynomial ℂ) ⟶
      Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)) :=
    Over.homMk g0 (by exact Limits.pullback.lift_fst _ _ _)
  refine ⟨g, ?_⟩
  ext1
  apply Limits.pullback.hom_ext
  · exact (Over.w (s2e_u1_specOverMap
      (Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ))) ≫ g)).trans (Over.w f).symm
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
