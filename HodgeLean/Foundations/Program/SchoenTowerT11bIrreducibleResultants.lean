import HodgeLean.Foundations.Program.SchoenTowerT11bResultantProjection
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Separable

/-! Projection polynomials obtained from irreducible plane equations.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An injective coefficient map preserves the ordinary degree-sized resultant.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, projection-polynomial step. -/
theorem s2v_t11b_resultant_map_of_injective {R S : Type*} [CommRing R] [CommRing S]
    (P Q : Polynomial R) (φ : R →+* S) (hφ : Function.Injective φ) :
    (P.map φ).resultant (Q.map φ) = φ (P.resultant Q) := by
  simpa only [Polynomial.natDegree_map_eq_of_injective hφ] using
    Polynomial.resultant_map_map P Q (P.map φ).natDegree (Q.map φ).natDegree φ

/-- An irreducible equation of positive spatial degree has a nonzero derivative resultant.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, projection-polynomial step. -/
theorem s2v_t11b_irreducible_derivative_resultant
    (P : Polynomial (Polynomial ℝ)) (hP : Irreducible P) (hdegree : P.natDegree ≠ 0) :
    P.resultant P.derivative ≠ 0 := by
  let K := FractionRing (Polynomial ℝ)
  let φ : Polynomial ℝ →+* K := algebraMap (Polynomial ℝ) K
  have hφ : Function.Injective φ := IsFractionRing.injective (Polynomial ℝ) K
  have hirr : Irreducible (P.map φ) :=
    ((hP.isPrimitive hdegree).irreducible_iff_irreducible_map_fraction_map (K := K)).mp hP
  have hcop := (Polynomial.separable_def (P.map φ)).mp hirr.separable
  have hres := Polynomial.resultant_ne_zero (P.map φ) (P.map φ).derivative hcop
  intro hz
  apply hres
  rw [Polynomial.derivative_map, s2v_t11b_resultant_map_of_injective P P.derivative φ hφ,
    hz, map_zero]

/-- A test not divisible by an irreducible plane equation has a nonzero common-root resultant.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, projection-polynomial step. -/
theorem s2v_t11b_irreducible_test_resultant
    (P Q : Polynomial (Polynomial ℝ)) (hP : Irreducible P) (hdegree : P.natDegree ≠ 0)
    (hnd : ¬ P ∣ Q) : P.resultant Q ≠ 0 := by
  let K := FractionRing (Polynomial ℝ)
  let φ : Polynomial ℝ →+* K := algebraMap (Polynomial ℝ) K
  have hφ : Function.Injective φ := IsFractionRing.injective (Polynomial ℝ) K
  have hprim := hP.isPrimitive hdegree
  have hirr : Irreducible (P.map φ) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hP
  have hcop : IsCoprime (P.map φ) (Q.map φ) :=
    hirr.coprime_iff_not_dvd.mpr (fun h => hnd
      ((hprim.dvd_iff_fraction_map_dvd_fraction_map K).mpr h))
  have hres := Polynomial.resultant_ne_zero (P.map φ) (Q.map φ) hcop
  intro hz
  apply hres
  rw [s2v_t11b_resultant_map_of_injective P Q φ hφ, hz, map_zero]

end HodgeLean.Foundations.Program
