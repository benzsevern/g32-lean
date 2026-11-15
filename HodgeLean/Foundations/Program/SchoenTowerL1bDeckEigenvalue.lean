import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Adjoin.Field

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Powers of a field symmetry multiply a fixed eigenvector by the corresponding scalar power. -/
theorem s2v_l1b_deck_eigenvector_powers
    {K : Type*} [Field K] (φ : K ≃+* K) (t ξ : K)
    (hξ : φ ξ = ξ) (ht : φ t = ξ * t) (k : ℕ) :
    (φ ^ k) t = ξ ^ k * t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change φ ((φ ^ k) t) = ξ ^ (k + 1) * t
    rw [ih, map_mul, map_pow, hξ, ht, pow_succ]
    ring

/-- A generator detects the full order of the scalar of a base-fixing symmetry. -/
theorem s2v_l1b_deck_eigenvalue_primitive
    {R K : Type*} [CommRing R] [Field K] (ρ : R →+* K)
    (φ : K ≃+* K) (t ξ : K) (m : ℕ)
    (ht : t ≠ 0) (hgen : Subfield.closure (Set.range ρ ∪ {t}) = ⊤)
    (hfix : ∀ f, φ (ρ f) = ρ f) (hξ : φ ξ = ξ)
    (heigen : φ t = ξ * t) (horder : orderOf φ = m) :
    IsPrimitiveRoot ξ m := by
  refine ⟨?_, ?_⟩
  · have hp := s2v_l1b_deck_eigenvector_powers φ t ξ hξ heigen m
    have hord : φ ^ m = 1 := horder ▸ pow_orderOf_eq_one φ
    rw [hord] at hp
    have he : ξ ^ m * t = 1 * t := by simpa using hp.symm
    exact mul_right_cancel₀ ht he
  · intro k hk
    have hp : (φ ^ k).toRingHom = RingHom.id K := by
      apply RingHom.eq_of_eqOn_of_field_closure_eq_top hgen
      rintro z (⟨f, rfl⟩ | hz)
      · have hf := s2v_l1b_deck_eigenvector_powers φ (ρ f) 1
          (map_one φ) (by simpa only [one_mul] using hfix f) k
        simpa using hf
      · have hz' : z = t := Set.mem_singleton_iff.mp hz
        subst z
        change (φ ^ k) t = t
        rw [s2v_l1b_deck_eigenvector_powers φ t ξ hξ heigen k, hk, one_mul]
    have he : φ ^ k = 1 := by
      ext z
      exact congrArg (fun f : K →+* K => f z) hp
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one he

/-- A base-fixing symmetry of a binomial field generator has a primitive scalar in the algebraically closed constants. -/
theorem s2v_l1b_deck_binomial_scalar
    {F R K : Type*} [Field F] [IsAlgClosed F] [CommRing R] [Field K]
    [Algebra F K] (ρ : R →+* K) (φ : K ≃+* K)
    (t : K) (m : ℕ) (hm : 0 < m) (ht : t ≠ 0)
    (hgen : Subfield.closure (Set.range ρ ∪ {t}) = ⊤)
    (hfix : ∀ f, φ (ρ f) = ρ f)
    (hconst : ∀ c : F, φ (algebraMap F K c) = algebraMap F K c)
    (hpow : φ (t ^ m) = t ^ m) (horder : orderOf φ = m) :
    ∃ ξ₀ : F, IsPrimitiveRoot (algebraMap F K ξ₀) m ∧
      φ t = algebraMap F K ξ₀ * t := by
  let ξ := φ t / t
  have hξpow : ξ ^ m = 1 := by
    dsimp only [ξ]
    rw [div_pow, ← map_pow, hpow, div_self (pow_ne_zero _ ht)]
  have hint : IsIntegral F ξ := IsIntegral.of_pow hm (by
    rw [hξpow]
    exact isIntegral_one)
  have hrange : ξ ∈ (algebraMap F K).range := by
    apply hint.mem_range_algebraMap_of_minpoly_splits (K := F)
    exact IsAlgClosed.splits _
  obtain ⟨ξ₀, hξ₀⟩ := hrange
  have heigen : φ t = algebraMap F K ξ₀ * t := by
    rw [hξ₀]
    exact (div_mul_cancel₀ (φ t) ht).symm
  exact ⟨ξ₀, s2v_l1b_deck_eigenvalue_primitive ρ φ t _ m ht hgen hfix
    (hconst ξ₀) heigen horder, heigen⟩

end HodgeLean.Foundations.Program
