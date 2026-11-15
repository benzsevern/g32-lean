import HodgeLean.Foundations.Program.SchoenTowerL1bKummerCancellation
import Mathlib.RingTheory.Ideal.Operations

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Replacing principal branch equations changes their weighted product by a regular unit. -/
theorem s2v_l1b_weighted_generators_unit
    {R : Type*} [CommRing R] [IsDomain R]
    {J : Type*} [Fintype J] (f g : J → R) (n : J → ℕ)
    (hfg : ∀ j, Ideal.span {f j} = Ideal.span {g j}) :
    ∃ δ : Rˣ, (∏ j, f j ^ n j) = (δ : R) * ∏ j, g j ^ n j := by
  have hI : Ideal.span {∏ j, f j ^ n j} = Ideal.span {∏ j, g j ^ n j} := by
    simp only [← Ideal.prod_span_singleton, ← Ideal.span_singleton_pow]
    simp only [hfg]
  obtain ⟨δ, hδ⟩ := (Ideal.span_singleton_eq_span_singleton.mp hI).symm
  exact ⟨δ, by rw [← hδ]; ring⟩

/-- A weighted Kummer equation transfers to every family generating the same branch ideals. -/
theorem s2v_l1b_branch_equation_change_generators
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    (ρ : R →+* K) {J : Type*} [Fintype J]
    (f g : J → R) (n : J → ℕ)
    (hfg : ∀ j, Ideal.span {f j} = Ideal.span {g j})
    (t : K) (m : ℕ) (ε : Rˣ)
    (ht : t ^ m = ρ (ε : R) * ∏ j, ρ (f j) ^ n j) :
    ∃ ε' : Rˣ, t ^ m = ρ (ε' : R) * ∏ j, ρ (g j) ^ n j := by
  obtain ⟨δ, hδ⟩ := s2v_l1b_weighted_generators_unit f g n hfg
  refine ⟨ε * δ, ?_⟩
  have hmap := congrArg ρ hδ
  simp only [map_mul, map_prod, map_pow] at hmap
  rw [ht, hmap, Units.val_mul, map_mul, mul_assoc]

/-- Restricting regular sections preserves the equation, with arbitrary principal equations downstairs. -/
theorem s2v_l1b_branch_equation_restrict
    {R A K : Type*} [CommRing R] [CommRing A] [IsDomain A] [Field K]
    (φ : R →+* A) (ρ : R →+* K) (ρ' : A →+* K)
    (hρ : ρ'.comp φ = ρ) {J : Type*} [Fintype J]
    (f : J → R) (g : J → A) (n : J → ℕ)
    (hfg : ∀ j, Ideal.span {φ (f j)} = Ideal.span {g j})
    (t : K) (m : ℕ) (ε : Rˣ)
    (ht : t ^ m = ρ (ε : R) * ∏ j, ρ (f j) ^ n j) :
    ∃ ε' : Aˣ, t ^ m = ρ' (ε' : A) * ∏ j, ρ' (g j) ^ n j := by
  apply s2v_l1b_branch_equation_change_generators ρ' (fun j => φ (f j)) g n hfg
    t m (Units.map φ ε)
  have hpoint (a : R) : ρ' (φ a) = ρ a := DFunLike.congr_fun hρ a
  change t ^ m = ρ' (φ (ε : R)) * ∏ j, ρ' (φ (f j)) ^ n j
  simpa only [hpoint] using ht

end HodgeLean.Foundations.Program
