import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveCoordinates

noncomputable section
set_option maxHeartbeats 400000
open AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

theorem s0_projective_chart_hom_ext {R : Type*} [CommRing R] {n : ℕ}
    (i : Fin (n + 1))
    (φ ψ : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →+* R)
    (hbase : ∀ a : UniversalGrading n 0,
      φ (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
        (Submonoid.powers (MvPolynomial.X i : UniversalRing n)) a) =
      ψ (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
        (Submonoid.powers (MvPolynomial.X i : UniversalRing n)) a))
    (hcoord : ∀ j, φ (chartCoordinate i j) = ψ (chartCoordinate i j)) : φ = ψ := by
  letI : Algebra (UniversalGrading n 0) R :=
    (φ.comp (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
      (Submonoid.powers (MvPolynomial.X i : UniversalRing n)))).toAlgebra
  let φa : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →ₐ[UniversalGrading n 0] R :=
    { φ with commutes' := fun _ ↦ rfl }
  let ψa : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →ₐ[UniversalGrading n 0] R :=
    { ψ with commutes' := fun r ↦ (hbase r).symm }
  change φa.toRingHom = ψa.toRingHom
  apply congrArg AlgHom.toRingHom
  apply AlgHom.ext_of_adjoin_eq_top
    (HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i)
      (Fin (n + 1)) (fun j ↦ MvPolynomial.X j) (adjoin_coordinates_eq_top n)
      (fun _ ↦ (1 : ℕ)) (fun j ↦ MvPolynomial.isHomogeneous_X (ULift ℤ) j))
  rintro z ⟨a, ai, hai, _, rfl⟩
  have hai' : ∑ j, ai j = a := by simpa using hai
  rw [chartGenerator_eq_prod i ai hai']
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  change φ (chartCoordinate i j ^ ai j) = ψ (chartCoordinate i j ^ ai j)
  rw [φ.map_pow, ψ.map_pow, hcoord]

#print axioms s0_projective_chart_hom_ext

/-- Evaluate an integral projective affine chart at coordinates with the chart coordinate equal to one.
Source: Hartshorne, Algebraic Geometry, II.2.5, degree-zero homogeneous localization. -/
def s0_projective_chart_eval {R : Type*} [CommRing R] {n : ℕ}
    (i : Fin (n + 1)) (a : ULift.{0} ℤ →+* R) (w : Fin (n + 1) → R) (hw : w i = 1) :
    HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) →+* R :=
  (IsLocalization.Away.lift
    (S := Localization.Away (MvPolynomial.X i : UniversalRing n))
    (MvPolynomial.X i)
    (show IsUnit ((MvPolynomial.eval₂Hom a w) (MvPolynomial.X i)) by
      simpa only [MvPolynomial.eval₂Hom_X', hw] using (isUnit_one : IsUnit (1 : R)))).comp
    (algebraMap (HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i))
      (Localization.Away (MvPolynomial.X i)))

theorem s0_projective_chart_eval_mk {R : Type*} [CommRing R] {n : ℕ}
    (i : Fin (n + 1)) (a : ULift.{0} ℤ →+* R) (w : Fin (n + 1) → R) (hw : w i = 1)
    (d : ℕ) (r : UniversalRing n) (hr : r ∈ UniversalGrading n d) :
    s0_projective_chart_eval i a w hw
      (HomogeneousLocalization.Away.mk (UniversalGrading n)
        (MvPolynomial.isHomogeneous_X _ i) d r (by simpa using hr)) =
      (MvPolynomial.eval₂Hom a w) r := by
  simp only [s0_projective_chart_eval, RingHom.coe_comp, Function.comp_apply]
  change (Localization.awayLift (MvPolynomial.eval₂Hom a w) (MvPolynomial.X i) _)
    (Localization.mk r ⟨MvPolynomial.X i ^ d, ⟨d, rfl⟩⟩) = _
  rw [Localization.awayLift_mk (MvPolynomial.eval₂Hom a w) (MvPolynomial.X i) r 1]
  · simp only [one_pow, mul_one]
  · simp only [MvPolynomial.eval₂Hom_X', hw, mul_one]

#print axioms s0_projective_chart_eval
#print axioms s0_projective_chart_eval_mk

theorem s0_projective_chart_eval_coordinate {R : Type*} [CommRing R] {n : ℕ}
    (i : Fin (n + 1)) (a : ULift.{0} ℤ →+* R) (w : Fin (n + 1) → R) (hw : w i = 1)
    (j : Fin (n + 1)) :
    s0_projective_chart_eval i a w hw (chartCoordinate i j) = w j := by
  unfold chartCoordinate
  rw [s0_projective_chart_eval_mk (hr := MvPolynomial.isHomogeneous_X _ j),
    MvPolynomial.eval₂Hom_X']

#print axioms s0_projective_chart_eval_coordinate

/-- The coefficient-ring map into an integral projective affine chart.
Source: Hartshorne, Algebraic Geometry, II.2.5, degree-zero localization. -/
def s0_projective_chart_base {n : ℕ} (i : Fin (n + 1)) :
    ULift.{0} ℤ →+* HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) :=
  (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
    (Submonoid.powers (MvPolynomial.X i : UniversalRing n))).comp
      (ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) (ULift.{0} ℤ)).symm.toRingHom

theorem s0_projective_chart_eval_base {R : Type*} [CommRing R] {n : ℕ}
    (i : Fin (n + 1)) (a : ULift.{0} ℤ →+* R) (w : Fin (n + 1) → R) (hw : w i = 1)
    (c : ULift.{0} ℤ) :
    s0_projective_chart_eval i a w hw (s0_projective_chart_base i c) = a c := by
  change s0_projective_chart_eval i a w hw
    (HomogeneousLocalization.Away.mk (UniversalGrading n)
      (MvPolynomial.isHomogeneous_X _ i) 0 (MvPolynomial.C c) _) = _
  rw [s0_projective_chart_eval_mk (hr := MvPolynomial.isHomogeneous_C _ c),
    MvPolynomial.eval₂Hom_C]

#print axioms s0_projective_chart_base
#print axioms s0_projective_chart_eval_base

/-- Polynomial coordinates on the chart with the distinguished homogeneous coordinate equal to one.
Source: Hartshorne, Algebraic Geometry, II.2.5, standard projective affine charts. -/
def s0_projective_chart_forward {n : ℕ} (i : Fin (n + 1)) :
    MvPolynomial {j : Fin (n + 1) // j ≠ i} (ULift.{0} ℤ) →+*
      HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) :=
  MvPolynomial.eval₂Hom (s0_projective_chart_base i) (fun j ↦ chartCoordinate i j.val)

/-- Evaluation in the free polynomial coordinates of a standard projective affine chart.
Source: Hartshorne, Algebraic Geometry, II.2.5, standard projective affine charts. -/
def s0_projective_chart_backward {n : ℕ} (i : Fin (n + 1)) :
    HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) →+*
      MvPolynomial {j : Fin (n + 1) // j ≠ i} (ULift.{0} ℤ) :=
  s0_projective_chart_eval i MvPolynomial.C
    (fun j ↦ if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩) (by simp)

#print axioms s0_projective_chart_forward
#print axioms s0_projective_chart_backward

attribute [local irreducible] s0_projective_chart_eval s0_projective_chart_base

set_option maxHeartbeats 200000 in
theorem s0_projective_chart_backward_forward {n : ℕ} (i : Fin (n + 1)) :
    (s0_projective_chart_backward i).comp (s0_projective_chart_forward i) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, s0_projective_chart_forward,
      MvPolynomial.eval₂Hom_C, RingHom.id_apply, s0_projective_chart_backward,
      s0_projective_chart_eval_base]
  · intro j
    simp only [RingHom.comp_apply, s0_projective_chart_forward,
      MvPolynomial.eval₂Hom_X', RingHom.id_apply, s0_projective_chart_backward,
      s0_projective_chart_eval_coordinate, dif_neg j.property]

#print axioms s0_projective_chart_backward_forward

set_option maxHeartbeats 200000 in
theorem s0_projective_chart_forward_backward {n : ℕ} (i : Fin (n + 1)) :
    (s0_projective_chart_forward i).comp (s0_projective_chart_backward i) = RingHom.id _ := by
  apply s0_projective_chart_hom_ext i
  · intro a
    obtain ⟨c, rfl⟩ := (ProjectiveSpace.degreeZeroEquiv
      (Fin (n + 1)) (ULift.{0} ℤ)).symm.surjective a
    have hb : HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
        (Submonoid.powers (MvPolynomial.X i : UniversalRing n))
          ((ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) (ULift.{0} ℤ)).symm c) =
        s0_projective_chart_base i c := by unfold s0_projective_chart_base; rfl
    simp only [RingHom.comp_apply, RingHom.id_apply, hb, s0_projective_chart_backward,
      s0_projective_chart_eval_base, s0_projective_chart_forward, MvPolynomial.eval₂Hom_C]
  · intro j
    simp only [RingHom.comp_apply, RingHom.id_apply, s0_projective_chart_backward,
      s0_projective_chart_eval_coordinate]
    by_cases h : j = i
    · subst j
      simp only [dite_true, map_one, chartCoordinate_self]
    · simp only [dif_neg h, s0_projective_chart_forward, MvPolynomial.eval₂Hom_X']

#print axioms s0_projective_chart_forward_backward

/-- The standard integral projective chart is a polynomial ring in the other coordinates.
Source: Hartshorne, Algebraic Geometry, II.2.5, standard projective affine charts. -/
def s0_projective_chart_ringEquiv {n : ℕ} (i : Fin (n + 1)) :
    MvPolynomial {j : Fin (n + 1) // j ≠ i} (ULift.{0} ℤ) ≃+*
      HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) where
  toFun := s0_projective_chart_forward i
  invFun := s0_projective_chart_backward i
  left_inv := fun p ↦ DFunLike.congr_fun (s0_projective_chart_backward_forward i) p
  right_inv := fun p ↦ DFunLike.congr_fun (s0_projective_chart_forward_backward i) p
  map_mul' := (s0_projective_chart_forward i).map_mul
  map_add' := (s0_projective_chart_forward i).map_add

/-- The polynomial description respects the displayed integral coefficient map.
Source: Hartshorne, Algebraic Geometry, II.2.5, standard projective affine charts. -/
def s0_projective_chart_algEquiv {n : ℕ} (i : Fin (n + 1)) :
    letI := (s0_projective_chart_base i).toAlgebra
    MvPolynomial {j : Fin (n + 1) // j ≠ i} (ULift.{0} ℤ) ≃ₐ[ULift.{0} ℤ]
      HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) :=
  letI := (s0_projective_chart_base i).toAlgebra
  { s0_projective_chart_ringEquiv i with
    commutes' := fun c ↦ MvPolynomial.eval₂Hom_C (s0_projective_chart_base i) _ c }

#print axioms s0_projective_chart_ringEquiv
#print axioms s0_projective_chart_algEquiv

theorem s0_projective_chart_smooth {n : ℕ} (i : Fin (n + 1)) :
    RingHom.Smooth (s0_projective_chart_base i) := by
  letI := (s0_projective_chart_base i).toAlgebra
  change Algebra.Smooth (ULift.{0} ℤ)
    (HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i))
  exact Algebra.Smooth.of_equiv (s0_projective_chart_algEquiv i)

#print axioms s0_projective_chart_smooth

end HodgeLean.Foundations.Program
