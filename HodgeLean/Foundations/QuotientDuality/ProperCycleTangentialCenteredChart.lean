import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs

/-! # Actual tangential translation of an original product chart
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

/-- Subtract a literal tangential vector while retaining the original normal coordinate of a product chart.
Source: Hatcher, Algebraic Topology, section 3.3, translation of local orientation charts.
HC no distance; AV milestone no distance. -/
def properCycle_tangential_centered_chart
    {M : Type} [TopologicalSpace M] (r d : ℕ)
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin d → ℂ))) (v : Fin r → ℂ) :
    OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin d → ℂ)) :=
  e.trans
    ({ toFun := fun z => (z.1 - v, z.2)
       invFun := fun z => (z.1 + v, z.2)
       left_inv := by intro z; exact Prod.ext (sub_add_cancel _ _) rfl
       right_inv := by intro z; exact Prod.ext (add_sub_cancel_right _ _) rfl
       continuous_toFun := by fun_prop
       continuous_invFun := by fun_prop } :
      ((Fin r → ℂ) × (Fin d → ℂ)) ≃ₜ ((Fin r → ℂ) × (Fin d → ℂ))).toOpenPartialHomeomorph

example (r d : ℕ) (z : (Fin r → ℂ) × (Fin d → ℂ)) :
    properCycle_tangential_centered_chart r d (Homeomorph.refl _).toOpenPartialHomeomorph z.1 z = (0, z.2) := by
  change (z.1 - z.1, z.2) = (0, z.2)
  rw [sub_self]

end HodgeLean.Foundations.QuotientDuality
