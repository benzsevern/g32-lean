import HodgeLean.Foundations.Program.SchoenCycleProjectivePoints

/-! # Actual standard projective chart rings -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- Maps from the actual integral projective chart ring to any commutative ring are determined by the base and coordinate ratios.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
theorem s2e_projective_chart_ringHom_ext {T : Type*} [CommRing T] {n : ℕ} (i : Fin (n + 1))
    (φ ψ : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →+* T)
    (hbase : ∀ a : UniversalGrading n 0,
      φ (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
        (Submonoid.powers (MvPolynomial.X i : UniversalRing n)) a) =
      ψ (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
        (Submonoid.powers (MvPolynomial.X i : UniversalRing n)) a))
    (hcoord : ∀ j, φ (chartCoordinate i j) = ψ (chartCoordinate i j)) :
    φ = ψ := by
  letI : Algebra (UniversalGrading n 0) T :=
    (φ.comp (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
      (Submonoid.powers (MvPolynomial.X i : UniversalRing n)))).toAlgebra
  let φa : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →ₐ[UniversalGrading n 0] T :=
    { φ with commutes' := fun _ ↦ rfl }
  let ψa : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →ₐ[UniversalGrading n 0] T :=
    { ψ with commutes' := fun r ↦ (hbase r).symm }
  change φa.toRingHom = ψa.toRingHom
  apply congrArg AlgHom.toRingHom
  apply AlgHom.ext_of_adjoin_eq_top
    (HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i)
      (Fin (n + 1)) (fun j ↦ MvPolynomial.X j) (adjoin_coordinates_eq_top n)
      (fun _ ↦ (1 : ℕ)) (fun j ↦ MvPolynomial.isHomogeneous_X (ULift ℤ) j))
  rintro z ⟨a, ai, hai, hai_le, rfl⟩
  have hai' : ∑ j, ai j = a := by simpa using hai
  rw [chartGenerator_eq_prod i ai hai']
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  change φ (chartCoordinate i j ^ ai j) = ψ (chartCoordinate i j ^ ai j)
  rw [φ.map_pow, ψ.map_pow, hcoord]

/-- Normalization of an integral homogeneous coordinate tuple sets the selected coordinate to one.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2. -/
def s2e_integralChartPolynomialHom {n : ℕ} (i : Fin (n + 1)) :
    UniversalRing n →+* UniversalRing n :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun j => if j = i then 1 else MvPolynomial.X j)

example {n : ℕ} (i j : Fin (n + 1)) :
    s2e_integralChartPolynomialHom i (MvPolynomial.X j) =
      if j = i then 1 else MvPolynomial.X j := by
  simp only [s2e_integralChartPolynomialHom, MvPolynomial.eval₂Hom_X']

/-- The actual integral chart localization maps to its normalized polynomial coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
def s2e_integralChartAwayHom {n : ℕ} (i : Fin (n + 1)) :
    HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) →+* UniversalRing n :=
  (Localization.awayLift (s2e_integralChartPolynomialHom i) (MvPolynomial.X i)
    (by simp [s2e_integralChartPolynomialHom])).comp
      (algebraMap
        (HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i))
        (Localization.Away (MvPolynomial.X i)))

/-- The degree-zero integral coefficient ring has a unique map to every commutative ring.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_projective_degreeZero_ringHom_unique {T : Type*} [CommRing T] {n : ℕ}
    (φ ψ : UniversalGrading n 0 →+* T) : φ = ψ := by
  ext a
  obtain ⟨z, rfl⟩ :=
    (ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) (ULift ℤ)).symm.surjective a
  obtain ⟨z, rfl⟩ := (ULift.ringEquiv (R := ℤ)).symm.surjective z
  exact DFunLike.congr_fun (Subsingleton.elim
    ((φ.comp (ProjectiveSpace.degreeZeroEquiv
      (Fin (n + 1)) (ULift ℤ)).symm.toRingHom).comp
        (ULift.ringEquiv (R := ℤ)).symm.toRingHom)
    ((ψ.comp (ProjectiveSpace.degreeZeroEquiv
      (Fin (n + 1)) (ULift ℤ)).symm.toRingHom).comp
        (ULift.ringEquiv (R := ℤ)).symm.toRingHom)) z

/-- The actual chart localization sends each regular ratio to its normalized integral coordinate.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
theorem s2e_integralChartAwayHom_coordinate {n : ℕ} (i j : Fin (n + 1)) :
    s2e_integralChartAwayHom i (chartCoordinate i j) =
      if j = i then 1 else MvPolynomial.X j := by
  simp only [s2e_integralChartAwayHom, RingHom.coe_comp, Function.comp_apply]
  change (Localization.awayLift (s2e_integralChartPolynomialHom i) (MvPolynomial.X i) _)
    (Localization.mk (MvPolynomial.X j) ⟨MvPolynomial.X i ^ 1, ⟨1, rfl⟩⟩) = _
  rw [Localization.awayLift_mk (s2e_integralChartPolynomialHom i) (MvPolynomial.X i)
    (MvPolynomial.X j) 1]
  all_goals simp [s2e_integralChartPolynomialHom]

end HodgeLean.Foundations.Program
