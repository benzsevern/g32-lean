import HodgeLean.Foundations.Program.SchoenCycleNativeAnalyticAdic
import HodgeLean.Foundations.Program.SchoenCycleNativeAnalyticStalk
import HodgeLean.Adapters.NormalConeB4aGysinSectionEvaluation

/-! # The actual algebraic-to-analytic adic stalk map -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- The actual local comparison of stalks induces a canonical map on their
maximal-ideal adic rings.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
def s2e_actualAnalytic_adic_stalkMap
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) :
    AdicCompletion (IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying))
        (X.left.presheaf.stalk p.underlying) →+*
      AdicCompletion (IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d))
        (s2e_nativeAnalyticGermRing d) :=
  s2e_adic_ring_map _ _ (s2e_stalk_nativeAnalyticGerm X d p)
    (IsLocalRing.map_maximalIdeal_le _)

#print axioms s2e_actualAnalytic_adic_stalkMap
/-- The actual adic comparison extends the previously constructed map on
original algebraic stalk elements.
Source: Mathlib, AdicCompletion.of and ideal-adic functoriality. -/
theorem s2e_actualAnalytic_adic_stalkMap_of
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (a : X.left.presheaf.stalk p.underlying) :
    s2e_actualAnalytic_adic_stalkMap X d p
      (AdicCompletion.of (IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying))
        (X.left.presheaf.stalk p.underlying) a) =
      AdicCompletion.of (IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d))
        (s2e_nativeAnalyticGermRing d) (s2e_stalk_nativeAnalyticGerm X d p a) := by
  exact s2e_adic_ring_map_of _ _ _ _ a

#print axioms s2e_actualAnalytic_adic_stalkMap_of
/-- The chosen algebraic coordinate section has the expected translated
coordinate germ in the actual centered analytic chart.
Source: HodgeConjecture, ComplexPoint.localChart_apply_of_mem and
LocalEtaleCoordinates.ambientAnalyticCoordinates_apply_eq_evaluate. -/
theorem s2e_actual_coordinateSection_nativeAnalytic
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X)
    (hp : p.underlying ∈ (ComplexPoint.localEtaleCoordinates X d p).ambientCoordinateOpen)
    (i : Fin d) :
    s2e_regularSection_nativeAnalyticGerm X d p
      (ComplexPoint.localEtaleCoordinates X d p).ambientCoordinateOpen hp
      ((ComplexPoint.localEtaleCoordinates X d p).ambientCoordinateSection i) =
        s2e_nativeAnalytic_constant d (ComplexPoint.localChart X d p p i) +
          s2e_nativeAnalytic_coordinate d i := by
  let D := ComplexPoint.localEtaleCoordinates X d p
  let e := ComplexPoint.localChart X d p
  have hep : e p ∈ e.target := e.map_source (ComplexPoint.mem_localChart_source X d p)
  have ht : ∀ᶠ z : Fin d → ℂ in nhds 0, e p + z ∈ e.target := by
    have hcont : ContinuousAt (fun z : Fin d → ℂ => e p + z) 0 :=
      continuous_const.continuousAt.add continuous_id.continuousAt
    exact hcont.tendsto (by simpa only [add_zero] using e.open_target.mem_nhds hep)
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [ht] with z hz
  have hcoord := congrFun (ComplexPoint.localChart_apply_of_mem X d p
    (e.symm (e p + z)) (e.map_target hz)) i
  rw [D.ambientAnalyticCoordinates_apply_eq_evaluate] at hcoord
  exact hcoord.symm.trans (congrFun (e.right_inv hz) i)

#print axioms s2e_actual_coordinateSection_nativeAnalytic
/-- Actual constant sections map to constant native analytic germs.
Source: Hartshorne, Algebraic Geometry, II.2, restriction of base scalars. -/
theorem s2e_actual_constantSection_nativeAnalytic
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U) (c : ℂ) :
    s2e_regularSection_nativeAnalyticGerm X d p U hp
      (HodgeLean.Adapters.a3b4a_gysin_sectionConst X.hom U c) =
        s2e_nativeAnalytic_constant d c := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  have hU := s2e_centered_localChart_tendsto X d p
    ((Point.isOpen_overOpen U).mem_nhds hp)
  filter_upwards [hU] with z hz
  exact HodgeLean.Adapters.a3b4a_gysin_evaluate_sectionConst X.hom U _ hz c

#print axioms s2e_actual_constantSection_nativeAnalytic
/-- Centered polynomials in the chosen actual algebraic coordinate sections
define elements of the actual algebraic stalk.
Source: HodgeConjecture, ComplexPoint.localEtaleCoordinates;
Hartshorne, Algebraic Geometry, II.2. -/
def s2e_actual_centeredPolynomial_stalk
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) : MvPolynomial (Fin d) ℂ →+* X.left.presheaf.stalk p.underlying :=
  let D := ComplexPoint.localEtaleCoordinates X d p
  let U := D.ambientCoordinateOpen
  let hp : p.underlying ∈ U := by
    simpa only [U, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using D.mem
  (X.left.presheaf.germ U p.underlying hp).hom.comp
    (MvPolynomial.eval₂Hom (HodgeLean.Adapters.a3b4a_gysin_sectionConst X.hom U)
      (fun i => D.ambientCoordinateSection i -
        HodgeLean.Adapters.a3b4a_gysin_sectionConst X.hom U (ComplexPoint.localChart X d p p i)))

#print axioms s2e_actual_centeredPolynomial_stalk
/-- The actual centered polynomial lift maps to native polynomial evaluation
under the actual analytic stalk comparison.
Source: HodgeConjecture, ComplexPoint.localChart_apply_of_mem;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_actual_centeredPolynomial_nativeAnalytic
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (q : MvPolynomial (Fin d) ℂ) :
    s2e_stalk_nativeAnalyticGerm X d p (s2e_actual_centeredPolynomial_stalk X d p q) =
      s2e_nativeAnalytic_polynomial d q := by
  simp only [s2e_actual_centeredPolynomial_stalk, RingHom.comp_apply,
    s2e_stalk_nativeAnalyticGerm_germ]
  induction q using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.eval₂Hom_C, s2e_nativeAnalytic_polynomial]
    exact s2e_actual_constantSection_nativeAnalytic X d p _ _ c
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul_X a i ha =>
    simp only [map_mul, ha, MvPolynomial.eval₂Hom_X', map_sub,
      s2e_actual_coordinateSection_nativeAnalytic, s2e_actual_constantSection_nativeAnalytic]
    rw [add_sub_cancel_left]
    congr 1
    exact (MvPolynomial.eval₂Hom_X' _ _ i).symm

#print axioms s2e_actual_centeredPolynomial_nativeAnalytic
/-- The actual algebraic-to-analytic stalk map surjects on every finite
maximal-ideal power quotient.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6. -/
theorem s2e_actualAnalytic_finite_stalkMap_surjective
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (N : ℕ) :
    Function.Surjective (s2e_adic_quotient_ring_map
      (IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying))
      (IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d))
      (s2e_stalk_nativeAnalyticGerm X d p) (IsLocalRing.map_maximalIdeal_le _) N) := by
  intro b
  obtain ⟨q, hq⟩ := s2e_nativeAnalytic_polynomial_quotient_surjective d N b
  refine ⟨Ideal.Quotient.mk _ (s2e_actual_centeredPolynomial_stalk X d p q), ?_⟩
  change Ideal.Quotient.mk _
    (s2e_stalk_nativeAnalyticGerm X d p (s2e_actual_centeredPolynomial_stalk X d p q)) = b
  rw [s2e_actual_centeredPolynomial_nativeAnalytic]
  exact hq

#print axioms s2e_actualAnalytic_finite_stalkMap_surjective
/-- The actual centered polynomial map sends the variable ideal into the
actual algebraic maximal ideal.
Source: Hartshorne, Algebraic Geometry, II.2, local homomorphisms. -/
theorem s2e_actual_centeredPolynomial_map_variableIdeal_le
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) :
    (MvPolynomial.idealOfVars (Fin d) ℂ).map (s2e_actual_centeredPolynomial_stalk X d p) ≤
      IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) := by
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change ¬ IsUnit (s2e_actual_centeredPolynomial_stalk X d p (MvPolynomial.X i))
  intro hu
  have h := hu.map (s2e_stalk_nativeAnalyticGerm X d p)
  rw [s2e_actual_centeredPolynomial_nativeAnalytic] at h
  apply (s2e_nativeAnalyticGerm_isUnit_iff_value_ne_zero d _).mp h
  rw [s2e_nativeAnalytic_polynomial_value, MvPolynomial.constantCoeff_X]

#print axioms s2e_actual_centeredPolynomial_map_variableIdeal_le
/-- The actual algebraic-to-native-analytic adic stalk map is surjective.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_actualAnalytic_adic_stalkMap_surjective
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) : Function.Surjective (s2e_actualAnalytic_adic_stalkMap X d p) := by
  let I := MvPolynomial.idealOfVars (Fin d) ℂ
  let J := IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying)
  let K := IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d)
  let P := s2e_actual_centeredPolynomial_stalk X d p
  let F := s2e_stalk_nativeAnalyticGerm X d p
  have hP : I.map P ≤ J := s2e_actual_centeredPolynomial_map_variableIdeal_le X d p
  have hF : J.map F ≤ K := IsLocalRing.map_maximalIdeal_le _
  have hcomp : F.comp P = s2e_nativeAnalytic_polynomial d := by
    apply RingHom.ext
    intro q
    exact s2e_actual_centeredPolynomial_nativeAnalytic X d p q
  have hgf : I.map (F.comp P) ≤ K := by
    rw [hcomp]
    exact (s2e_nativeAnalytic_map_variableIdeal d).le
  intro b
  obtain ⟨z, rfl⟩ := (s2e_nativeAnalytic_adic_coordinates d).surjective b
  refine ⟨s2e_adic_ring_map I J P hP z, ?_⟩
  have h := s2e_adic_ring_map_comp I J K P hP F hF hgf z
  change s2e_adic_ring_map J K F hF (s2e_adic_ring_map I J P hP z) =
    s2e_adic_ring_map I K (s2e_nativeAnalytic_polynomial d)
      (s2e_nativeAnalytic_map_variableIdeal d).le z
  simpa only [hcomp] using h

#print axioms s2e_actualAnalytic_adic_stalkMap_surjective
end HodgeLean.Foundations.Program
