import HodgeLean.Foundations.Program.SchoenTowerL1bDifferentialLocalization
import Mathlib.RingTheory.Ideal.Span
import HodgeLean.Foundations.Program.SchoenTowerL1bEtaleDerivations

/-! Etale neighborhoods for specified unit multiples of coordinate generators.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program
open KaehlerDifferential
open scoped BigOperators

/-- Unit changes at vanishing coordinates have a nonzero differential determinant at the specified point. -/
theorem s2v_l1b_unit_generator_determinant_ne_zero
    {R A K ι : Type*} [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Fintype ι] [DecidableEq ι]
    (f : ι → A) (b : Module.Basis ι A Ω[A⁄R]) (hb : ∀ i, b i = D R A (f i))
    (w : ι → Aˣ) (φ : A →+* K)
    (hz : ∀ i, φ (f i) = 0 ∨ w i = 1) :
    φ (b.det (fun i => D R A ((w i : A) * f i))) ≠ 0 := by
  have hentry (i j : ι) :
      φ (b.repr (D R A ((w j : A) * f j)) i) =
        if i = j then φ (w j : A) else 0 := by
    rw [(D R A).leibniz, ← hb j]
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul, map_mul, b.repr_self, Finsupp.single_apply]
    have hzero : φ (f j) * φ (b.repr (D R A (w j : A)) i) = 0 := by
      rcases hz j with hj | hj
      · rw [hj, zero_mul]
      · rw [hj]
        simp only [Units.val_one, (D R A).map_one_eq_zero, map_zero, Finsupp.zero_apply, mul_zero]
    rw [hzero, add_zero]
    by_cases h : i = j
    · simp only [h, ite_true, map_one, mul_one]
    · simp only [h, Ne.symm h, ite_false, map_zero, mul_zero]
  have hmatrix : φ.mapMatrix (b.toMatrix (fun j => D R A ((w j : A) * f j))) =
      Matrix.diagonal (fun j => φ (w j : A)) := by
    ext i j
    change φ (b.toMatrix (fun j => D R A ((w j : A) * f j)) i j) = _
    rw [Module.Basis.toMatrix_apply, hentry,
      Matrix.diagonal_apply]
    split_ifs with h
    · subst j
      rfl
    · rfl
  rw [Module.Basis.det_apply, RingHom.map_det, hmatrix, Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (Units.map φ.toMonoidHom (w i)).ne_zero

/-- Unit changes of coordinate generators have an etale principal neighborhood retaining a point where the changed generators vanish. -/
theorem s2v_l1b_unit_generator_etale_neighborhood
    {R A K ι : Type*} [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra.Smooth R A] [Fintype ι] [DecidableEq ι]
    (f : ι → A) (b : Module.Basis ι A Ω[A⁄R]) (hb : ∀ i, b i = D R A (f i))
    (w : ι → Aˣ) (φ : A →+* K)
    (hz : ∀ i, φ (f i) = 0 ∨ w i = 1) :
    ∃ d : A, φ d ≠ 0 ∧
      (MvPolynomial.aeval (R := R)
        (fun i => algebraMap A (Localization.Away d) ((w i : A) * f i))).toRingHom.Etale := by
  refine ⟨b.det (fun i => D R A ((w i : A) * f i)),
    s2v_l1b_unit_generator_determinant_ne_zero f b hb w φ hz, ?_⟩
  exact s2v_l1b_evaluation_etale_away_differential_determinant (fun i => (w i : A) * f i) b

/-- Equal principal ideals allow the specified generators as exact etale coordinates after a point-preserving localization. -/
theorem s2v_l1b_principal_generator_etale_neighborhood
    {R A K ι : Type*} [CommRing R] [CommRing A] [IsDomain A] [Field K]
    [Algebra R A] [Algebra.Smooth R A] [Fintype ι] [DecidableEq ι]
    (f g : ι → A) (b : Module.Basis ι A Ω[A⁄R]) (hb : ∀ i, b i = D R A (f i))
    (hI : ∀ i, Ideal.span {g i} = Ideal.span {f i}) (φ : A →+* K)
    (hz : ∀ i, φ (f i) = 0 ∨ g i = f i) :
    ∃ d : A, φ d ≠ 0 ∧
      (MvPolynomial.aeval (R := R)
        (fun i => algebraMap A (Localization.Away d) (g i))).toRingHom.Etale := by
  have hunit (i : ι) : ∃ w : Aˣ, (w : A) * f i = g i ∧
      (φ (f i) = 0 ∨ w = 1) := by
    rcases hz i with hi | hi
    · obtain ⟨w, hw⟩ := (Ideal.span_singleton_eq_span_singleton.mp (hI i)).symm
      exact ⟨w, (mul_comm _ _).trans hw, Or.inl hi⟩
    · exact ⟨1, (one_mul _).trans hi.symm, Or.inr rfl⟩
  choose w hw hz' using hunit
  obtain ⟨d, hd, hEt⟩ := s2v_l1b_unit_generator_etale_neighborhood f b hb w φ hz'
  refine ⟨d, hd, ?_⟩
  simpa only [hw] using hEt

/-- The exact replacement generators of an etale coordinate family give another etale family on a neighborhood of their common vanishing point. -/
theorem s2v_l1b_etale_coordinate_generator_replacement
    {R A K ι : Type*} [CommRing R] [CommRing A] [IsDomain A] [Field K]
    [Algebra R A] [Fintype ι] [DecidableEq ι]
    (f g : ι → A) (hEt : (MvPolynomial.aeval (R := R) f).toRingHom.Etale)
    (hI : ∀ i, Ideal.span {g i} = Ideal.span {f i}) (φ : A →+* K)
    (hz : ∀ i, φ (f i) = 0 ∨ g i = f i) :
    ∃ d : A, φ d ≠ 0 ∧
      (MvPolynomial.aeval (R := R)
        (fun i => algebraMap A (Localization.Away d) (g i))).toRingHom.Etale := by
  letI : Algebra (MvPolynomial ι R) A := (MvPolynomial.aeval (R := R) f).toRingHom.toAlgebra
  letI : IsScalarTower R (MvPolynomial ι R) A :=
    .of_algebraMap_eq fun r => by
      simp only [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
  letI : Algebra.Etale (MvPolynomial ι R) A := hEt
  letI : Algebra.Smooth R A := Algebra.Smooth.comp R (MvPolynomial ι R) A
  apply s2v_l1b_principal_generator_etale_neighborhood f g
    (s2v_l1b_etaleDifferentialBasis R A ι) _ hI φ hz
  intro i
  simpa only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, MvPolynomial.aeval_X] using
    s2v_l1b_etaleDifferentialBasis_apply R A ι i

end HodgeLean.Foundations.Program
