import HodgeLean.Foundations.Program.RelativeFrameOperatorPole

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

def rf4_poleDatum {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (D : rf4_OuterData C O) (ε : Fin D.m → ℂ)
    (hε : ∀ x, ‖ε x‖ < D.r) (x : Fin D.m) : rf4_Tgt D := by
  classical
  exact Pi.single x (rf4_poleMultiplier (D.deg x) (D.hdeg x) D.r D.hr (ε x) (hε x))

theorem rf4_poleDatum_apply {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (D : rf4_OuterData C O) (ε : Fin D.m → ℂ)
    (hε : ∀ x, ‖ε x‖ < D.r) (x₀ x : Fin D.m) (u : b63r_annulus (D.deg x) D.r) :
    (rf4_poleDatum D ε hε x₀ x : b63r_annulus (D.deg x) D.r →ᵇ ℂ) u =
      if x = x₀ then rf4_poleMultiplierFun (D.deg x) (ε x) u else 0 := by
  classical
  by_cases h : x = x₀
  · subst x
    simp only [rf4_poleDatum, Pi.single_eq_same, if_pos rfl]
    rfl
  · simp [rf4_poleDatum, Pi.single_apply, h]

end HodgeLean.Foundations.Program
