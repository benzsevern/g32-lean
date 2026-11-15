import HodgeLean.Adapters.NormalConeB2Fibre
import HodgeLean.Adapters.NormalConeB2Cycle
import HodgeLean.Adapters.NormalConeB4aGysinParameter
import HodgeLean.Adapters.IntersectionProductScaf
import Mathlib.RingTheory.KrullDimension.Regular

/-! # Lengths of the scheme-theoretic fibre algebra

Evaluation base change retains the length of the parameter quotient. This identifies
its coefficient with the component-length formula for a regular parameter.
-/

noncomputable section
namespace HodgeLean.Adapters
open scoped TensorProduct Pointwise

universe u

/-- The self-length of an evaluation fibre is its length as a parameter quotient. -/
theorem a3b4a_gysin_tensor_fibre_length
    {k A : Type u} [Field k] [CommRing A] [Algebra (Polynomial k) A]
    (s : k) [Algebra (Polynomial k) k]
    (hs : algebraMap (Polynomial k) k = Polynomial.evalRingHom s) :
    Module.length (A ⊗[Polynomial k] k) (A ⊗[Polynomial k] k) =
      Module.length A (A ⧸ Ideal.span
        {algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C s)}) := by
  rw [a3b2_length_eq_of_ringEquiv (a3b2_tensorEvalEquiv A s hs)]
  exact (Module.length_eq_of_surjective (Ideal.Quotient.mk_surjective)).symm

/-- A fibre equation in a flat algebra lies outside each minimal prime. -/
theorem a3b4a_gysin_parameter_not_mem_minimalPrime
    {k A : Type u} [Field k] [CommRing A] [Algebra (Polynomial k) A]
    [Module.Flat (Polynomial k) A] (s : k) (P : Ideal A)
    (hP : P ∈ minimalPrimes A) :
    algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C s) ∉ P := by
  intro h
  apply notMem_nonZeroDivisors_of_mem_mem_minimalPrimes h hP
  rw [mem_nonZeroDivisors_iff_right]
  intro a ha
  exact (a3b4a_gysin_parameter_mul_eq_zero_iff s a).mp (by simpa only [mul_comm] using ha)

/-- In a local flat algebra of dimension at most one, the exact fibre length is
its sum of generic lengths times the reduced-component parameter lengths. -/
theorem a3b4a_gysin_local_fibre_length_sum
    {k A : Type u} [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] [Algebra (Polynomial k) A] [Module.Flat (Polynomial k) A]
    (s : k) [Algebra (Polynomial k) k]
    (hs : algebraMap (Polynomial k) k = Polynomial.evalRingHom s)
    (hrm : algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C s) ∈
      IsLocalRing.maximalIdeal A)
    (Φ : Finset (PrimeSpectrum A))
    (hΦ : ∀ p : PrimeSpectrum A, p ∈ Φ ↔ p.asIdeal ∈ minimalPrimes A) :
    (Module.length (A ⊗[Polynomial k] k) (A ⊗[Polynomial k] k)).toNat =
      ∑ p ∈ Φ, (a3e_locLen p A).toNat *
        (Module.length A (QuotSMulTop
          (algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C s))
          (A ⧸ p.asIdeal))).toNat := by
  let t := algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C s)
  have ht : ∀ p ∈ Φ, t ∉ p.asIdeal := fun p hp =>
    a3b4a_gysin_parameter_not_mem_minimalPrime s p.asIdeal ((hΦ p).mp hp)
  have hm : ∀ p ∈ Φ, p ≠ IsLocalRing.closedPoint A := by
    intro p hp heq
    apply ht p hp
    simpa only [heq, t, IsLocalRing.closedPoint] using hrm
  have hd : ∀ p ∈ Φ, ∀ q : PrimeSpectrum A, p < q →
      q = IsLocalRing.closedPoint A := by
    intro p hp q hpq
    rcases Ring.krullDimLE_one_iff.mp (inferInstance : Ring.KrullDimLE 1 A)
      q.asIdeal q.isPrime with hq | hq
    · exact False.elim (not_le_of_gt hpq ((PrimeSpectrum.isMin_iff.mpr hq) hpq.le))
    · exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hq)
  have hsupport : Module.support A A ⊆
      insert (IsLocalRing.closedPoint A) (Φ : Set (PrimeSpectrum A)) := by
    intro p hp
    rcases Ring.krullDimLE_one_iff.mp (inferInstance : Ring.KrullDimLE 1 A)
      p.asIdeal p.isPrime with hmin | hmax
    · exact Set.mem_insert_of_mem _ ((hΦ p).mpr hmin)
    · exact Or.inl (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax))
  have hregular : IsSMulRegular A t := a3b4a_gysin_parameter_mul_injective s
  have hquot : (t • (⊤ : Submodule A A)) = (Ideal.span {t} : Ideal A) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [a3b4a_gysin_tensor_fibre_length s hs]
  have hlen := (Submodule.quotEquivOfEq (t • (⊤ : Submodule A A))
    (Ideal.span {t}) hquot).length_eq
  rw [← hlen]
  exact IntersectionProductScaf_parameter_length t Φ hm hd ht A hsupport hregular

/-- An Artinian fibre supplies the dimension bound and a finite set of components
for the exact local length formula. -/
theorem a3b4a_gysin_artinian_fibre_length_sum
    {k A : Type u} [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra (Polynomial k) A] [Module.Flat (Polynomial k) A]
    (s : k) [Algebra (Polynomial k) k]
    (hs : algebraMap (Polynomial k) k = Polynomial.evalRingHom s)
    [IsArtinianRing (A ⊗[Polynomial k] k)]
    (hrm : algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C s) ∈
      IsLocalRing.maximalIdeal A) :
    ∃ Φ : Finset (PrimeSpectrum A),
      (∀ p : PrimeSpectrum A, p ∈ Φ ↔ p.asIdeal ∈ minimalPrimes A) ∧
      (Module.length (A ⊗[Polynomial k] k) (A ⊗[Polynomial k] k)).toNat =
        ∑ p ∈ Φ, (a3e_locLen p A).toNat *
          (Module.length A (QuotSMulTop
            (algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C s))
            (A ⧸ p.asIdeal))).toNat := by
  classical
  have hreg : IsSMulRegular A
      (algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C s)) :=
    a3b4a_gysin_parameter_mul_injective s
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hreg hrm
  rw [← ringKrullDim_eq_of_ringEquiv (a3b2_tensorEvalEquiv A s hs)] at hdim
  let : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by
    rw [← hdim]
    have hz : ringKrullDim (A ⊗[Polynomial k] k) ≤ 0 :=
      Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 0 (A ⊗[Polynomial k] k))
    simpa only [Nat.cast_one, zero_add, add_zero, add_comm] using add_le_add_right hz 1)
  let Φ := (PrimeSpectrum.finite_setOfPred_isMin A).toFinset
  have hΦ : ∀ p : PrimeSpectrum A, p ∈ Φ ↔ p.asIdeal ∈ minimalPrimes A := by
    intro p
    simp only [Φ, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, PrimeSpectrum.isMin_iff]
  exact ⟨Φ, hΦ, a3b4a_gysin_local_fibre_length_sum s hs hrm Φ hΦ⟩

end HodgeLean.Adapters
