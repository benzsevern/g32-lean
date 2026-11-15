import HodgeLean.Foundations.Program.RelativeFrameOperatorPoleWitness

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_delta_not_surjective_core {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] (S : rf4_Plumbing D ε X) (hm : 0 < D.m) :
    ¬ Function.Surjective (rf4_delta D ε) := by
  intro hsurj
  let x₀ : Fin D.m := ⟨0, hm⟩
  obtain ⟨k, hk⟩ := hsurj (rf4_poleDatum D ε S.small x₀)
  obtain ⟨w, hone, hzero⟩ := rf4_pole_residue_witness S x₀ k hk
  have hglobal := b4c_residue_sum (Module.finrank_self ℂ) w
  have hsum := finsum_eq_single (fun p : X ↦ b4c_res (hE := Module.finrank_self ℂ) w p)
    ((S.w x₀).symm 0) hzero
  rw [hsum, hone] at hglobal
  exact one_ne_zero hglobal

end HodgeLean.Foundations.Program
