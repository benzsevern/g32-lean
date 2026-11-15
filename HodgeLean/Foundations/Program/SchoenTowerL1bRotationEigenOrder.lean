import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Iterating a field symmetry raises its fixed scalar eigenvalue to the same power. -/
theorem s2v_l1b_rotation_eigenfunction_iterate
    {K : Type*} [Field K] (τ : K ≃+* K) {t ζ : K}
    (hζ : τ ζ = ζ) (ht : τ t = ζ * t) (n : ℕ) :
    (τ ^ n) t = ζ ^ n * t := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact (one_mul t).symm
  | succ n ih =>
    rw [pow_succ']
    change τ ((τ ^ n) t) = ζ ^ (n + 1) * t
    rw [ih, map_mul, map_pow, hζ, ht, pow_succ]
    ring

/-- A generating eigenfunction detects every period of a base-fixing symmetry. -/
theorem s2v_l1b_rotation_eigenfunction_period_iff
    {R K : Type*} [CommRing R] [Field K] (ρ : R →+* K)
    (τ : K ≃+* K) {t ζ : K} (ht : t ≠ 0)
    (hgen : Subfield.closure (Set.range ρ ∪ {t}) = ⊤)
    (hfix : ∀ r, τ (ρ r) = ρ r) (hζ : τ ζ = ζ)
    (heigen : τ t = ζ * t) (n : ℕ) :
    τ ^ n = 1 ↔ ζ ^ n = 1 := by
  have hiterate := s2v_l1b_rotation_eigenfunction_iterate τ hζ heigen n
  constructor
  · intro hn
    rw [hn] at hiterate
    change t = ζ ^ n * t at hiterate
    exact mul_right_cancel₀ ht (hiterate.symm.trans (one_mul t).symm)
  · intro hn
    have hbase : ∀ r, (τ ^ n) (ρ r) = ρ r := by
      intro r
      simpa only [one_pow, one_mul] using
        s2v_l1b_rotation_eigenfunction_iterate τ (map_one τ)
          (show τ (ρ r) = 1 * ρ r by rw [one_mul]; exact hfix r) n
    have hh : (τ ^ n).toRingHom = (1 : K ≃+* K).toRingHom := by
      apply RingHom.eq_of_eqOn_of_field_closure_eq_top hgen
      rintro v (⟨r, rfl⟩ | hv)
      · exact hbase r
      · rcases Set.mem_singleton_iff.mp hv with rfl
        change (τ ^ n) v = v
        simpa only [hn, one_mul] using hiterate
    exact RingEquiv.ext (fun v => DFunLike.congr_fun hh v)

/-- A scalar on a generating eigenfunction has the exact order of the retained symmetry. -/
theorem s2v_l1b_rotation_eigenfunction_primitive
    {R K : Type*} [CommRing R] [Field K] (ρ : R →+* K)
    (τ : K ≃+* K) {t ζ : K} (ht : t ≠ 0)
    (hgen : Subfield.closure (Set.range ρ ∪ {t}) = ⊤)
    (hfix : ∀ r, τ (ρ r) = ρ r) (hζ : τ ζ = ζ)
    (heigen : τ t = ζ * t) {m : ℕ} (horder : orderOf τ = m) :
    IsPrimitiveRoot ζ m := by
  have hperiod := s2v_l1b_rotation_eigenfunction_period_iff ρ τ ht hgen hfix hζ heigen
  refine ⟨?_, ?_⟩
  · apply (hperiod m).mp
    rw [← horder]
    exact pow_orderOf_eq_one τ
  · intro n hn
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one ((hperiod n).mpr hn)

end HodgeLean.Foundations.Program
