import HodgeLean.Foundations.Program.MilneTensorPairedSchur

noncomputable section
namespace HodgeLean.Foundations.Program
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem m1b_alternating_pair_decomposition
    (Q : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × W)) (ha : ∀ x, Q x x = 0)
    (x y : (Fin 2 → ℂ) × W) :
    Q x y = Q (Pi.single 0 1, 0) (Pi.single 1 1, 0) *
      (x.1 0 * y.1 1 - x.1 1 * y.1 0) +
      x.1 0 * m1b_pairCross Q 0 y.2 + x.1 1 * m1b_pairCross Q 1 y.2 -
      y.1 0 * m1b_pairCross Q 0 x.2 - y.1 1 * m1b_pairCross Q 1 x.2 +
      m1b_pairRestriction Q x.2 y.2 := by
  let u₀ : (Fin 2 → ℂ) × W := (Pi.single 0 1, 0)
  let u₁ : (Fin 2 → ℂ) × W := (Pi.single 1 1, 0)
  have hx (z : (Fin 2 → ℂ) × W) : z = z.1 0 • u₀ + z.1 1 • u₁ + (0, z.2) := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [u₀, u₁, Pi.single_apply]
    · simp [u₀, u₁]
  have h₁₀ : Q u₁ u₀ = -Q u₀ u₁ := (LinearMap.BilinForm.IsAlt.neg_eq ha u₀ u₁).symm
  have h₀ (w : W) : Q (0, w) u₀ = -Q u₀ (0, w) :=
    (LinearMap.BilinForm.IsAlt.neg_eq ha u₀ (0, w)).symm
  have h₁ (w : W) : Q (0, w) u₁ = -Q u₁ (0, w) :=
    (LinearMap.BilinForm.IsAlt.neg_eq ha u₁ (0, w)).symm
  calc
    Q x y = Q (x.1 0 • u₀ + x.1 1 • u₁ + (0, x.2))
        (y.1 0 • u₀ + y.1 1 • u₁ + (0, y.2)) := congrArg₂ (fun a b => Q a b) (hx x) (hx y)
    _ = _ := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, ha u₀, ha u₁, h₁₀, h₀, h₁]
      change _ = Q u₀ u₁ * (x.1 0 * y.1 1 - x.1 1 * y.1 0) +
        x.1 0 * Q u₀ (0, y.2) + x.1 1 * Q u₁ (0, y.2) -
        y.1 0 * Q u₀ (0, x.2) - y.1 1 * Q u₁ (0, x.2) + Q (0, x.2) (0, y.2)
      ring

end HodgeLean.Foundations.Program
