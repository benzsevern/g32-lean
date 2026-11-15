import HodgeLean.Foundations.Program.SchoenCycleC1UnitDiscriminantHelpers
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- A specified base rational function that becomes an actual unit in an
integral chart extension comes from a unit of the original normal base ring.
No invariance or separate unit of the base coefficient is supplied. -/
theorem s2e_c1_normal_unit_descent
    {R S K L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L]
    [Algebra R L] [IsScalarTower R S L] [Algebra K L] [IsScalarTower R K L]
    (t : K) (u : Sˣ) (ht : algebraMap K L t = algebraMap S L (u : S)) :
    ∃ v : Rˣ, algebraMap R K (v : R) = t := by
  have ht0 : t ≠ 0 := by
    intro hz
    have hu0 : algebraMap S L (u : S) ≠ 0 :=
      fun h => u.ne_zero (IsFractionRing.injective S L (h.trans (map_zero _).symm))
    apply hu0
    rw [← ht, hz, map_zero]
  have hi : IsIntegral R (algebraMap K L t) := by
    rw [ht]
    exact (Algebra.IsIntegral.isIntegral (u : S)).map (IsScalarTower.toAlgHom R S L)
  have hinv : IsIntegral R (algebraMap K L t⁻¹) := by
    rw [map_inv₀, ht, ← map_units_inv]
    exact (Algebra.IsIntegral.isIntegral ((u⁻¹ : Sˣ) : S)).map (IsScalarTower.toAlgHom R S L)
  have liftIntegral (a : K) (h : IsIntegral R (algebraMap K L a)) : IsIntegral R a := by
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L)
      (RingHom.injective (algebraMap K L))).mp h
  exact s2e_c1_unit_of_integral_inverse t ht0 (liftIntegral t hi) (liftIntegral t⁻¹ hinv)

end HodgeLean.Foundations.Program
