import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]

theorem pole_set_eq_residue_divisor_support (h : Module.finrank ℂ E = 1)
    (D : C →₀ ℤ) (w : b4c_MeroForm E C h)
    (hr : ∀ x, b4c_res (hE := h) w x = (D x : ℂ))
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0) :
    (b4c_residue_poles_finite h w).toFinset = D.support := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hxs
    exact (not_lt_of_ge (ha x hxs).meromorphicOrderAt_nonneg)
      ((b4c_residue_poles_finite h w).mem_toFinset.mp hx)
  · intro hx
    apply (b4c_residue_poles_finite h w).mem_toFinset.mpr
    by_contra hxp
    have hz := TauCeti.Contour.residue_eq_zero_of_meromorphicOrderAt_nonneg
      (f := HurwitzPrymRR_loc h w x) (le_of_not_gt hxp)
    have hn : (D x : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (Finsupp.mem_support_iff.mp hx)
    exact hn ((hr x).symm.trans hz)

end HodgeLean.Foundations.Curves.AbelTheorem
