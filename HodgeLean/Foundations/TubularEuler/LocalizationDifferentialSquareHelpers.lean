import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal

/-! # Differentials of elements in localized maximal-ideal squares

A differential at a field-valued point kills the square of its kernel.
Denominators outside that kernel preserve this calculation.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.TubularEuler

theorem differential_zero_on_kernel_square
    {A K M : Type*} [CommRing A] [Field K] [AddCommGroup M] [Module K M]
    (ε : A →+* K) (D : A →+ M)
    (hleibniz : ∀ a b, D (a * b) = ε a • D b + ε b • D a)
    (a : A) (ha : a ∈ (RingHom.ker ε) ^ 2) : D a = 0 := by
  rw [pow_two] at ha
  refine Submodule.mul_induction_on ha ?_ ?_
  · intro a ha b hb
    rw [hleibniz, RingHom.mem_ker.mp ha, RingHom.mem_ker.mp hb,
      zero_smul, zero_smul, add_zero]
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]

theorem differential_zero_of_local_maximal_square
    {A S K M : Type*} [CommRing A] [CommRing S] [Field K]
    [Algebra A S] [IsLocalRing S] [AddCommGroup M] [Module K M]
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime S p]
    (ε : A →+* K) (hker : RingHom.ker ε = p) (D : A →+ M)
    (hleibniz : ∀ a b, D (a * b) = ε a • D b + ε b • D a)
    (a : A) (ha : ε a = 0)
    (hsq : algebraMap A S a ∈ IsLocalRing.maximalIdeal S ^ 2) : D a = 0 := by
  have hmap : algebraMap A S a ∈ (p ^ 2).map (algebraMap A S) := by
    rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal p S]
    exact hsq
  obtain ⟨s, hs, hsa⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl S (p ^ 2) a).mp hmap
  have hsz : ε s ≠ 0 := by
    intro hz
    exact hs (hker ▸ (show s ∈ RingHom.ker ε from hz))
  have hd := differential_zero_on_kernel_square ε D hleibniz (s * a)
    (by simpa only [hker] using hsa)
  rw [hleibniz, ha, zero_smul, add_zero] at hd
  exact (smul_eq_zero.mp hd).resolve_left hsz

#print axioms differential_zero_of_local_maximal_square

#print axioms differential_zero_on_kernel_square

end HodgeLean.Foundations.TubularEuler
