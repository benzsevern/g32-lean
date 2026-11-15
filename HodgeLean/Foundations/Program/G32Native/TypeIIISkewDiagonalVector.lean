import HodgeLean.Foundations.Program.G32Native.TypeIIITraceFormRegular

noncomputable section
open scoped Quaternion
namespace HodgeLean.Foundations.Program.G32Native

/-- A nondegenerate quaternion skew-Hermitian form on a nonzero module has
a vector with nonzero diagonal value. -/
theorem typeIII_skew_exists_diagonal (b : ℚ)
    {V : Type*} [AddCommGroup V] [Module ℍ[ℚ, -3, 0, b] V] [Nontrivial V]
    (H : V → V → ℍ[ℚ, -3, 0, b])
    (haddL : ∀ x x' y, H (x + x') y = H x y + H x' y)
    (haddR : ∀ x y y', H x (y + y') = H x y + H x y')
    (hsmul : ∀ (q : ℍ[ℚ, -3, 0, b]) x y, H (q • x) y = q * H x y)
    (hskew : ∀ x y, H y x = -star (H x y))
    (hnd : ∀ x, (∀ y, H x y = 0) → x = 0) :
    ∃ x, H x x ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hself (x y : V) : H x y = star (H x y) := by
    have h := hn (x + y)
    rw [haddL, haddR, haddR, hn x, hn y, zero_add, add_zero, hskew x y] at h
    exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)
  have hi (x y : V) : (H x y).imI = 0 := by
    have h := congrArg QuaternionAlgebra.imI (hself x y)
    simp only [QuaternionAlgebra.imI_star] at h
    linarith
  have hj (x y : V) : (H x y).imJ = 0 := by
    have h := congrArg QuaternionAlgebra.imJ (hself x y)
    simp only [QuaternionAlgebra.imJ_star] at h
    linarith
  have hk (x y : V) : (H x y).imK = 0 := by
    have h := congrArg QuaternionAlgebra.imK (hself x y)
    simp only [QuaternionAlgebra.imK_star] at h
    linarith
  have hr (x y : V) : (H x y).re = 0 := by
    have h := hi ((⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, b]) • x) y
    rw [hsmul] at h
    simpa [QuaternionAlgebra.imI_mul] using h
  have hall (x y : V) : H x y = 0 := by
    ext
    · exact hr x y
    · exact hi x y
    · exact hj x y
    · exact hk x y
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact hx (hnd x (hall x))

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_skew_exists_diagonal
