import HodgeLean.Blocks.Weil.RationalKernel

/-! # Recovering a quotient from a kernel complement -/

noncomputable section

namespace HodgeBlocks

/-- A surjection annihilating a diagonalizable operator restricts to an equivalence
on its kernel when the quotient and kernel have the same dimension. -/
theorem bijective_quotient_restrict_ker
    {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [Module.Finite K E] [AddCommGroup F] [Module K F] [Module.Finite K F]
    (T : E →ₗ[K] E) (q : E →ₗ[K] F) (hq : Function.Surjective q)
    (hzero : ∀ x, q (T x) = 0)
    (hdiag : ∀ x, T (T x) = 0 → T x = 0)
    (hdim : Module.finrank K ↥(LinearMap.ker T) = Module.finrank K F) :
    Function.Bijective (q.comp (LinearMap.ker T).subtype) := by
  have hrange : LinearMap.range T = LinearMap.ker q := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, rfl⟩
      exact hzero x
    · have hT := T.finrank_range_add_finrank_ker
      have hq' := q.finrank_range_add_finrank_ker
      rw [LinearMap.range_eq_top.mpr hq, finrank_top] at hq'
      omega
  have hinj : Function.Injective (q.comp (LinearMap.ker T).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx' : (x : E) ∈ LinearMap.range T := by
      rw [hrange]
      exact hx
    obtain ⟨y, hy⟩ := hx'
    have hyy : T (T y) = 0 := by rw [hy]; exact x.property
    have hy0 : T y = 0 := hdiag y hyy
    apply Subtype.ext
    exact hy.symm.trans hy0
  exact ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

#print axioms bijective_quotient_restrict_ker

end HodgeBlocks
