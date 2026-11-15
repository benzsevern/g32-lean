import HodgeLean.Foundations.Program.G32Native.PELHodgeGroupContainment

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)

/-- A bilinear form pairing only opposite circle weights is invariant under
all Hodge-circle operators.
Source: Abdulali, Annals of Mathematics 155 (2002), §2.1, p. 917;
Birkenhake–Lange, Complex Abelian Varieties, §4.2 (first Riemann relation). -/
theorem circleAction_preserves_form
    (E : LinearMap.BilinForm ℂ (ℂ ⊗[ℚ] V))
    (hE : ∀ p q r s : ℤ, ∀ x ∈ H (p, q), ∀ y ∈ H (r, s),
      p - q + (r - s) ≠ 0 → E x y = 0) (z : Circle) :
    E.compl₁₂ (g2_circleAction H hH z) (g2_circleAction H hH z) = E := by
  apply linearMap_ext_of_isInternal hH
  rintro ⟨p, q⟩ x hx
  apply linearMap_ext_of_isInternal hH
  rintro ⟨r, s⟩ y hy
  change E (g2_circleAction H hH z x) (g2_circleAction H hH z y) = E x y
  rw [g2_circleAction_apply_of_mem H hH z hx,
    g2_circleAction_apply_of_mem H hH z hy]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  by_cases he : p - q + (r - s) = 0
  · rw [← mul_assoc, ← zpow_add₀ (Circle.coe_ne_zero z), add_comm (r - s), he, zpow_zero, one_mul]
  · rw [hE p q r s x hx y hy he, mul_zero, mul_zero]

#print axioms circleAction_preserves_form
end HodgeLean.Foundations.Program.GeneralTypeIII
