import HodgeLean.Foundations.QuotientDuality.MonomialFractionGeneration
import HodgeLean.Foundations.QuotientDuality.MonomialRootFiniteness
import Mathlib.FieldTheory.Galois.Basic

/-! Galois structure on the fraction field of a finitely generated root component. -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.QuotientDuality

theorem power_root_fractionField_galois
    {R A K F : Type*} [CommRing R] [CommRing A] [IsDomain A]
    [Field K] [CharZero K] [Field F]
    [Algebra R A] [Algebra A F] [IsFractionRing A F]
    [Algebra R K] [Algebra K F] [Algebra R F]
    [IsScalarTower R A F] [IsScalarTower R K F]
    (n m : ℕ) (hm : 0 < m) (ζ : K) (hζ : IsPrimitiveRoot ζ m)
    (W : Fin n → A) (U : A)
    (hgen : Algebra.adjoin R (Set.range W ∪ {U}) = ⊤)
    (hW : ∀ j, ∃ a : K, algebraMap A F (W j) ^ m = algebraMap K F a)
    (hU : ∃ a : K, algebraMap A F U ^ m = algebraMap K F a) :
    IsGalois K F ∧ FiniteDimensional K F := by
  let S := algebraMap A F '' (Set.range W ∪ {U})
  have hS : IntermediateField.adjoin K S = ⊤ := fractionField_adjoin_eq_top _ hgen
  have hfinite : S.Finite :=
    ((Set.finite_range W).union (Set.finite_singleton U)).image _
  have hpow : ∀ x ∈ S, ∃ a : K, x ^ m = algebraMap K F a := by
    rintro x ⟨a, (⟨j, rfl⟩ | rfl), rfl⟩
    · exact hW j
    · exact hU
  letI : Normal K F := normal_of_adjoin_power_roots m hm ζ hζ S hS hpow
  exact ⟨{}, finiteDimensional_of_adjoin_power_roots m hm S hfinite hS hpow⟩

#print axioms power_root_fractionField_galois
end HodgeLean.Foundations.QuotientDuality
