import HodgeLean.Foundations.Program.SchoenCycleProjectivePoints
import Mathlib.Algebra.DualNumber

/-! # Standard projective chart functions over nonreduced rings -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- Maps from the actual universal projective chart to any commutative ring are
determined by the homogeneous coordinate ratios, including over dual numbers.
Source: Hartshorne, Algebraic Geometry, II.2 and II.7, projective affine charts. -/
theorem s2e_u1_projective_chart_ringHom_ext
    {A : Type} [CommRing A] {n : ℕ} (i : Fin (n + 1))
    (φ ψ : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →+* A)
    (hcoord : ∀ j, φ (chartCoordinate i j) = ψ (chartCoordinate i j)) : φ = ψ := by
  have hbase : φ.comp (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
      (Submonoid.powers (MvPolynomial.X i : UniversalRing n))) =
    ψ.comp (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
      (Submonoid.powers (MvPolynomial.X i : UniversalRing n))) := by
    ext a
    obtain ⟨z, rfl⟩ :=
      (ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) (ULift ℤ)).symm.surjective a
    obtain ⟨z, rfl⟩ := (ULift.ringEquiv (R := ℤ)).symm.surjective z
    exact DFunLike.congr_fun (Subsingleton.elim
      (((φ.comp (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
        (Submonoid.powers (MvPolynomial.X i : UniversalRing n)))).comp
        (ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) (ULift ℤ)).symm.toRingHom).comp
        (ULift.ringEquiv (R := ℤ)).symm.toRingHom)
      (((ψ.comp (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
        (Submonoid.powers (MvPolynomial.X i : UniversalRing n)))).comp
        (ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) (ULift ℤ)).symm.toRingHom).comp
        (ULift.ringEquiv (R := ℤ)).symm.toRingHom)) z
  letI : Algebra (UniversalGrading n 0) A :=
    (φ.comp (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
      (Submonoid.powers (MvPolynomial.X i : UniversalRing n)))).toAlgebra
  let φa : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →ₐ[UniversalGrading n 0] A :=
    { φ with commutes' := fun _ => rfl }
  let ψa : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →ₐ[UniversalGrading n 0] A :=
    { ψ with commutes' := fun r => (DFunLike.congr_fun hbase r).symm }
  change φa.toRingHom = ψa.toRingHom
  apply congrArg AlgHom.toRingHom
  apply AlgHom.ext_of_adjoin_eq_top
    (HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i)
      (Fin (n + 1)) (fun j => MvPolynomial.X j) (adjoin_coordinates_eq_top n)
      (fun _ => (1 : ℕ)) (fun j => MvPolynomial.isHomogeneous_X (ULift ℤ) j))
  rintro z ⟨a, ai, hai, hai_le, rfl⟩
  have hai' : ∑ j, ai j = a := by simpa using hai
  rw [chartGenerator_eq_prod i ai hai']
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  change φ (chartCoordinate i j ^ ai j) = ψ (chartCoordinate i j ^ ai j)
  rw [φ.map_pow, ψ.map_pow, hcoord]

/-- Every ring-valued standard chart point is evaluation at its actual normalized
coordinate ratios, including points valued in complex dual numbers.
Source: Hartshorne, Algebraic Geometry, II.2 and II.7, projective affine charts. -/
theorem s2e_u1_projective_chart_coordinate_recovery
    {A : Type} [CommRing A] [Algebra ℂ A] {n : ℕ} (i : Fin (n + 1))
    (φ : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →+* A) :
    (MvPolynomial.eval₂Hom (algebraMap ℂ A) (fun j => φ (chartCoordinate i j))).comp
      (chartAwayPolynomialHom i) = φ := by
  apply s2e_u1_projective_chart_ringHom_ext i
  intro j
  simp only [RingHom.comp_apply, chartAwayPolynomialHom_chartCoordinate]
  by_cases hji : j = i
  · subst j
    simp [chartCoordinate_self]
  · simp only [if_neg hji, MvPolynomial.eval₂Hom_X']

/-- The polynomial line associated to a dual-number chart point retains its base
coordinates and every first-order coordinate variation.
Source: Hartshorne, Algebraic Geometry, II.8, the affine description of tangent vectors. -/
def s2e_u1_projectiveChartLine {n : ℕ} (i : Fin (n + 1))
    (φ : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →+* DualNumber ℂ) :
    HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →+* Polynomial ℂ :=
  (MvPolynomial.eval₂Hom Polynomial.C (fun j =>
    Polynomial.C (φ (chartCoordinate i j)).fst +
      Polynomial.X * Polynomial.C (φ (chartCoordinate i j)).snd)).comp
        (chartAwayPolynomialHom i)

/-- Substituting the actual dual-number parameter in the polynomial line
recovers the original nonreduced projective chart point.
Source: Hartshorne, Algebraic Geometry, II.8, the affine description of tangent vectors. -/
theorem s2e_u1_projectiveChartLine_dual {n : ℕ} (i : Fin (n + 1))
    (φ : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →+* DualNumber ℂ) :
    (Polynomial.eval₂RingHom (algebraMap ℂ (DualNumber ℂ))
      (TrivSqZeroExt.inr (1 : ℂ))).comp (s2e_u1_projectiveChartLine i φ) = φ := by
  apply s2e_u1_projective_chart_ringHom_ext i
  intro j
  simp only [RingHom.comp_apply, s2e_u1_projectiveChartLine,
    chartAwayPolynomialHom_chartCoordinate]
  by_cases hji : j = i
  · subst j
    simp [chartCoordinate_self]
  · simp only [if_neg hji, MvPolynomial.eval₂Hom_X', map_add, map_mul,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

end HodgeLean.Foundations.Program
