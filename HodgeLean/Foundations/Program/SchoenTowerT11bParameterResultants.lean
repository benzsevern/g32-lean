import HodgeLean.Foundations.Program.SchoenTowerT11bRadicalResultants

/-! Projection resultants for polynomial families with multiplicities removed.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open UniqueFactorizationMonoid
variable {A : Type*} [CommRing A] [IsDomain A] [CharZero A]
    [UniqueFactorizationMonoid A] [NormalizationMonoid (Polynomial A)]

/-- A nonzero equation of spatial degree zero becomes a unit over the parameter fraction field.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, vertical-factor step. -/
theorem s2v_t11b_parameter_fraction_map_unit_of_degree_zero
    (P : Polynomial A) (hP : P ≠ 0) (hd : P.natDegree = 0) :
    IsUnit (P.map (algebraMap A (FractionRing A))) := by
  let φ := algebraMap A (FractionRing A)
  have hφ := IsFractionRing.injective A (FractionRing A)
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hd
  have hc : P.coeff 0 ≠ 0 := by
    intro h
    apply hP
    exact hC.trans (by rw [h, Polynomial.C_0])
  have hmc : φ (P.coeff 0) ≠ 0 := fun h => hc (hφ (h.trans (map_zero φ).symm))
  have hm : P.map φ = Polynomial.C (φ (P.coeff 0)) := by
    exact (congrArg (Polynomial.map φ) hC).trans (Polynomial.map_C φ)
  rw [hm]
  exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hmc)

/-- Distinct prime factors of a polynomial family become a separable polynomial over the parameter field.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, polynomial factorization step. -/
theorem s2v_t11b_parameter_radical_fraction_separable (P : Polynomial A) :
    ((radical P).map (algebraMap A (FractionRing A))).Separable := by
  classical
  let K := FractionRing A
  let φ : A →+* K := algebraMap A K
  have hirr : ∀ f ∈ primeFactors P, Irreducible f := fun f hf =>
    irreducible_of_normalized_factor f (mem_primeFactors.mp hf)
  have hsep : ∀ f ∈ primeFactors P, (f.map φ).Separable := by
    intro f hf
    by_cases hd : f.natDegree = 0
    · have hu := s2v_t11b_parameter_fraction_map_unit_of_degree_zero f (hirr f hf).ne_zero hd
      exact Polynomial.separable_one.of_dvd hu.dvd
    · have hp := (hirr f hf).isPrimitive hd
      have hi : Irreducible (f.map φ) :=
        (hp.irreducible_iff_irreducible_map_fraction_map (K := K)).mp (hirr f hf)
      exact hi.separable
  have hcop : ∀ f ∈ primeFactors P, ∀ g ∈ primeFactors P,
      f ≠ g → IsCoprime (f.map φ) (g.map φ) := by
    intro f hf g hg hfg
    by_cases hd : f.natDegree = 0
    · have hu := s2v_t11b_parameter_fraction_map_unit_of_degree_zero f (hirr f hf).ne_zero hd
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv'.mp hu
      exact ⟨b, 0, by simpa only [zero_mul, add_zero] using hb⟩
    · have hp := (hirr f hf).isPrimitive hd
      have hi : Irreducible (f.map φ) :=
        (hp.irreducible_iff_irreducible_map_fraction_map (K := K)).mp (hirr f hf)
      apply hi.coprime_iff_not_dvd.mpr
      intro h
      have hdiv : f ∣ g := (hp.dvd_iff_fraction_map_dvd_fraction_map K).mpr h
      have hr : IsRelPrime f g := pairwise_primeFactors_isRelPrime hf hg hfg
      exact ((hirr f hf).isRelPrime_iff_not_dvd.mp hr) hdiv
  change ((radical P).map φ).Separable
  simpa only [radical, Polynomial.map_prod, id_eq] using Polynomial.separable_prod' hcop hsep

/-- Removing repeated factors always gives a nonzero derivative resultant for a polynomial family.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, projection-polynomial step. -/
theorem s2v_t11b_parameter_radical_derivative_resultant (P : Polynomial A) :
    (radical P).resultant (radical P).derivative ≠ 0 := by
  let K := FractionRing A
  let φ : A →+* K := algebraMap A K
  have hφ : Function.Injective φ := IsFractionRing.injective A K
  have hsep := s2v_t11b_parameter_radical_fraction_separable P
  have hres := Polynomial.resultant_ne_zero ((radical P).map φ)
    ((radical P).map φ).derivative ((Polynomial.separable_def _).mp hsep)
  intro hz
  apply hres
  rw [Polynomial.derivative_map,
    s2v_t11b_resultant_map_of_injective (radical P) (radical P).derivative φ hφ, hz, map_zero]

end HodgeLean.Foundations.Program
