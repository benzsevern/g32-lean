import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Actual rational functionals on an exact pair of linear maps -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

/-- A functional annihilating the first map factors through the second map of an exact pair of vector-space maps.
Source: Weibel, An Introduction to Homological Algebra, section 2.3, injectivity of vector spaces.
HC no distance; AV milestone no distance. -/
lemma properCycle_dual_exact_lift {U V W : Type*}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module ℚ U] [Module ℚ V] [Module ℚ W]
    (f : U →ₗ[ℚ] V) (g : V →ₗ[ℚ] W)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (a : Module.Dual ℚ V) (ha : ∀ u, a (f u) = 0) :
    ∃ b : Module.Dual ℚ W, b.comp g = a := by
  have h : a ∈ LinearMap.range g.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, ← hfg]
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    obtain ⟨u, rfl⟩ := hv
    exact ha u
  obtain ⟨b, hb⟩ := h
  exact ⟨b, hb⟩

end HodgeLean.Foundations.QuotientDuality
