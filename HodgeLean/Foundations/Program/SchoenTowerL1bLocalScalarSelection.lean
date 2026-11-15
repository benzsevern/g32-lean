import HodgeLean.Foundations.Program.SchoenTowerL1bRotationEigenOrder
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A binomial eigenvalue lies among the base roots of unity, and exact
order of the generating symmetry makes that same base scalar primitive. -/
theorem s2v_l1b_local_scalar_selection
    {R E : Type*} [CommRing R] [Field E]
    (ρ : R →+* E) (hρ : Function.Injective ρ)
    (t : E) (ht : t ≠ 0) (a b : R) (m : ℕ) (hm : m ≠ 0)
    (hgen : Subfield.closure (Set.range ρ ∪ {t}) = ⊤)
    (hpow : t ^ m = ρ a / ρ b) (τ : E ≃+* E)
    (hfix : ∀ v : R, τ (ρ v) = ρ v) (horder : orderOf τ = m)
    (α : E) (hchar : τ t = α * t)
    (γ : R) (hγ : IsPrimitiveRoot γ m) :
    ∃ k : ℕ, IsPrimitiveRoot (γ ^ k) m ∧ ρ (γ ^ k) = α := by
  have hα : α ^ m = 1 := by
    have h := congrArg τ hpow
    rw [map_pow, hchar, mul_pow, map_div₀, hfix, hfix, ← hpow] at h
    exact mul_right_cancel₀ (pow_ne_zero m ht) (h.trans (one_mul (t ^ m)).symm)
  have hγE : IsPrimitiveRoot (ρ γ) m := hγ.map_of_injective hρ
  letI : NeZero m := ⟨hm⟩
  obtain ⟨k, hk, hγk⟩ := hγE.eq_pow_of_pow_eq_one hα
  have hu : ρ (γ ^ k) = α := by rw [map_pow]; exact hγk
  have hfixα : τ α = α := by rw [← hu]; exact hfix _
  have hprim := s2v_l1b_rotation_eigenfunction_primitive ρ τ ht hgen hfix hfixα hchar horder
  refine ⟨k, ?_, hu⟩
  rw [← hu] at hprim
  exact hprim.of_map_of_injective hρ

/-- Generation over a represented domain also gives generation over its
ambient base field. -/
theorem s2v_l1b_adjoin_eq_top_of_domain_closure
    {R F E : Type*} [CommRing R] [Field F] [Field E] [Algebra R F] [Algebra F E]
    (t : E)
    (hgen : Subfield.closure
      (Set.range ((algebraMap F E).comp (algebraMap R F)) ∪ {t}) = ⊤) :
    IntermediateField.adjoin F ({t} : Set E) = ⊤ := by
  apply IntermediateField.toSubfield_injective
  apply top_unique
  rw [← hgen]
  apply Subfield.closure_le.mpr
  rintro z (⟨r, rfl⟩ | hz)
  · exact IntermediateField.algebraMap_mem _ (algebraMap R F r)
  · exact IntermediateField.subset_adjoin F ({t} : Set E) hz

end HodgeLean.Foundations.Program
