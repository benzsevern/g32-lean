import HodgeLean.Foundations.Program.SchoenTowerL1bKummerBranchUnits
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Exact prime multiplicities in a factorial domain give the weighted factorization up to a unit. -/
theorem s2v_l1b_unit_of_prime_multiplicities
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {J : Type*} [Fintype J] (g : J → R) (n : J → ℕ)
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (hg : ∀ j, g j ≠ 0)
    (hv : ∀ p : R, Prime p → emultiplicity p a =
      emultiplicity p b + ∑ j, (n j : ℕ∞) * emultiplicity p (g j)) :
    ∃ ε : Rˣ, a = (ε : R) * b * ∏ j, g j ^ n j := by
  have hc : b * ∏ j, g j ^ n j ≠ 0 :=
    mul_ne_zero hb (Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hg j))
  have heq (p : R) (hp : Prime p) :
      emultiplicity p a = emultiplicity p (b * ∏ j, g j ^ n j) := by
    rw [emultiplicity_mul hp, Finset.emultiplicity_prod hp]
    simp only [emultiplicity_pow hp]
    exact hv p hp
  have hab : a ∣ b * ∏ j, g j ^ n j :=
    (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le ha).mpr fun p hp => (heq p hp).le
  have hba : b * ∏ j, g j ^ n j ∣ a :=
    (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hc).mpr fun p hp => (heq p hp).ge
  obtain ⟨ε, hε⟩ := (dvd_dvd_iff_associated.mp ⟨hba, hab⟩)
  refine ⟨ε, ?_⟩
  rw [← hε]
  ring

/-- Prime multiplicities of a rational coefficient yield the weighted Kummer equation with a regular unit. -/
theorem s2v_l1b_branch_equation_of_prime_multiplicities
    {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field K]
    (ρ : R →+* K) {J : Type*} [Fintype J] (g : J → R) (n : J → ℕ)
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (hg : ∀ j, g j ≠ 0)
    (hρb : ρ b ≠ 0)
    (hv : ∀ p : R, Prime p → emultiplicity p a =
      emultiplicity p b + ∑ j, (n j : ℕ∞) * emultiplicity p (g j))
    (t : K) (m : ℕ) (ht : t ^ m = ρ a / ρ b) :
    ∃ ε : Rˣ, t ^ m = ρ (ε : R) * ∏ j, ρ (g j) ^ n j := by
  obtain ⟨ε, hε⟩ := s2v_l1b_unit_of_prime_multiplicities g n a b ha hb hg hv
  refine ⟨ε, ?_⟩
  rw [ht, hε, map_mul, map_mul, map_prod]
  simp only [map_pow]
  rw [mul_right_comm (ρ (ε : R)) (ρ b), mul_div_cancel_right₀ _ hρb]

end HodgeLean.Foundations.Program
