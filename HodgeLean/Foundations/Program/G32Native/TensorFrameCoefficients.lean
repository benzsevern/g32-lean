import HodgeLean.Foundations.Program.G32Native.TensorFrameEquiv

/-! Coefficient comparisons for sections written against local line frames. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
namespace HodgeLean.Foundations.Program

/-- Scaling the line frame inversely scales its coefficient in an equal tensor section. -/
theorem g32l4_tensor_frame_coefficients_proportional
    {X : Scheme.{0}} (F L : X.Modules) (W : X.Opens)
    (s : Γ(L, ⊤)) (hs : IsFrameOn s W)
    (a : Γ(X, W)) (m m' : Γ(F, W)) (s' : Γ(L, W))
    (hs' : s' = a • L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s)
    (h : tensorSections m (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s) =
      tensorSections m' s') : m = a • m' := by
  apply hs.injective_tensorSections F le_top le_rfl
  dsimp only
  rw [tensorSections_smul_left, ← tensorSections_smul_right, ← hs']
  exact h

end HodgeLean.Foundations.Program
