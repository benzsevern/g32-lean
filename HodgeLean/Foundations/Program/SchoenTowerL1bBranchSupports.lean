import HodgeLean.Foundations.Program.SchoenTowerL1bTransformLocality
import HodgeLean.Foundations.Program.SchoenTowerInertiaSuppliers

/-! # Branch supports under the retained tower projection
Support propagation uses the actual reduced transforms and tower composite.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A branch support at any stage maps into its stage-zero support. -/
theorem s2v_l1b_tower_branch_support {r : ℕ} {T : Type*}
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, T → (B i).left.IdealSheafData)
    (K : ∀ i : Fin r, (B i.castSucc).left.IdealSheafData)
    (hD : ∀ (i : Fin r) t,
      D i.succ t = s2c_strictTransform (b i).left (D i.castSucc t) (K i))
    (i : Fin (r + 1)) :
    ∀ (t : T) (x : (B i).left), x ∈ (D i t).support →
      (s2v_towerToInitial B b i).left x ∈ (D 0 t).support := by
  induction i using Fin.induction with
  | zero => intro t x hx; exact hx
  | succ i ih =>
    intro t x hx
    rw [hD i t] at hx
    have hb := s2v_l1b_strictTransform_support_le (b i).left (D i.castSucc t) (K i) hx
    rw [Scheme.IdealSheafData.support_comap] at hb
    exact ih t ((b i).left x) hb

end HodgeLean.Foundations.Program
