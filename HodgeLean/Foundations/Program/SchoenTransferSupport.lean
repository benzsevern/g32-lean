import HodgeLean.Foundations.Program.SchoenTransferSmooth
import HodgeLean.Foundations.Program.SchoenCycleClassDefs

/-! Component codimension in a smooth ambient scheme. -/
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s4_support_codimension_smooth_iff
    (W : Over (Spec ↧ℂ)) [Smooth W.hom] (z : AlgebraicCycle W.left ℚ) (k : ℕ) :
    (∀ x ∈ z.support, Order.coheight x = k ∧
      ∃ U : W.left.Opens, x ∈ U ∧ Smooth (U.ι ≫ W.hom)) ↔
    (∀ x ∈ z.support, Order.coheight x = k) := by
  constructor
  · intro h x hx
    exact (h x hx).1
  · intro h x hx
    exact ⟨h x hx, s4_smooth_open_at W.hom x⟩

end HodgeLean.Foundations.Program
