import HodgeLean.Foundations.Program.SchoenCycleCotangentGeneration
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Descending adic maximal-ideal generators -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Generation of the adic maximal ideal by original elements descends to the
original Noetherian local ring.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10;
faithful flatness of the local adic algebra. -/
theorem s2e_maximalIdeal_generators_of_adic_generators
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {ι : Type*} (d : ι → R)
    (hgen : IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) =
      Ideal.span (Set.range (fun i => algebraMap R
        (AdicCompletion (IsLocalRing.maximalIdeal R) R) (d i)))) :
    IsLocalRing.maximalIdeal R = Ideal.span (Set.range d) := by
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  letI : Module.FaithfullyFlat R A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply Ideal.map_injective_of_faithfullyFlat (B := A)
  rw [← AdicCompletion.maximalIdeal_eq_map, Ideal.map_span, ← Set.range_comp]
  exact hgen

#print axioms s2e_maximalIdeal_generators_of_adic_generators
/-- Original elements approximating adic maximal-ideal generators modulo its
square generate the original local maximal ideal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 2 and 10;
Nakayama's lemma and faithful flatness. -/
theorem s2e_maximalIdeal_generators_of_adic_approximation
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {ι : Type*} (c : ι → AdicCompletion (IsLocalRing.maximalIdeal R) R) (d : ι → R)
    (hgen : IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) =
      Ideal.span (Set.range c))
    (hdiff : ∀ i, algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) (d i) - c i ∈
      IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ 2) :
    IsLocalRing.maximalIdeal R = Ideal.span (Set.range d) := by
  apply s2e_maximalIdeal_generators_of_adic_generators d
  apply s2e_maximalIdeal_generators_stable_mod_square c _ _ hgen hdiff
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal R)).map _

#print axioms s2e_maximalIdeal_generators_of_adic_approximation
/-- Every local adic element has an original-ring representative modulo any
power of the adic maximal ideal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10;
Mathlib, AdicCompletion.pow_smul_top_eq_ker_eval. -/
theorem s2e_local_adic_element_approximation
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (c : AdicCompletion (IsLocalRing.maximalIdeal R) R) (N : ℕ) :
    ∃ d : R, algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) d - c ∈
      IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ N := by
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (c.val N)
  refine ⟨d, ?_⟩
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow,
    ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (Ideal.fg_of_isNoetherianRing _)]
  change AdicCompletion.eval (IsLocalRing.maximalIdeal R) R N
    (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) d - c) = 0
  rw [map_sub]
  change Ideal.Quotient.mk _ d - c.val N = 0
  rw [hd, sub_self]

#print axioms s2e_local_adic_element_approximation
/-- Adic maximal-ideal generators can be approximated to any order at least
two by generators of the original local maximal ideal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 2 and 10. -/
theorem s2e_local_generators_approximating_adic_generators
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {ι : Type*} (c : ι → AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (hgen : IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) =
      Ideal.span (Set.range c)) (N : ℕ) (hN : 2 ≤ N) :
    ∃ d : ι → R, IsLocalRing.maximalIdeal R = Ideal.span (Set.range d) ∧
      ∀ i, algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) (d i) - c i ∈
        IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ N := by
  choose d hd using fun i => s2e_local_adic_element_approximation (c i) N
  refine ⟨d, ?_, hd⟩
  apply s2e_maximalIdeal_generators_of_adic_approximation c d hgen
  intro i
  exact (Ideal.pow_le_pow_right hN) (hd i)

#print axioms s2e_local_generators_approximating_adic_generators
/-- Membership in a power of the local adic maximal ideal is detected by
finite quotient evaluation.
Source: Mathlib, AdicCompletion.pow_smul_top_eq_ker_eval and maximalIdeal_eq_map. -/
theorem s2e_local_adic_mem_maximalIdeal_pow_iff_eval
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (z : AdicCompletion (IsLocalRing.maximalIdeal R) R) (N : ℕ) :
    z ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ N ↔
      AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) N z = 0 := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow,
    ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (Ideal.fg_of_isNoetherianRing _)]
  change AdicCompletion.eval (IsLocalRing.maximalIdeal R) R N z = 0 ↔ _
  have h : ((IsLocalRing.maximalIdeal R) ^ N • ⊤ : Ideal R) ≤
      (IsLocalRing.maximalIdeal R) ^ N := by simp
  rw [← AdicCompletion.factor_eval_eq_evalₐ _ _ h]
  have hi : Function.Injective (Ideal.Quotient.factor h) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    rw [Ideal.Quotient.factor_ker]
    apply Ideal.map_mk_eq_bot_of_le
    simp
  exact (map_eq_zero_iff _ hi).symm

#print axioms s2e_local_adic_mem_maximalIdeal_pow_iff_eval
end HodgeLean.Foundations.Program
