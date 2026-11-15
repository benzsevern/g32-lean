import HodgeLean.Foundations.Program.G32SelectedRealizationSubgroupRotation

noncomputable section
open Manifold HodgeLean.Papers
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem g32y_rotation_character_invariant {E C G : Type} {A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C] [CommGroup A]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (r : C → G) (hr : ∀ x, b4_IsRotGen E x (r x))
    (χ : G →* A) (k : G) (x : C) : χ (r (k • x)) = χ (r x) := by
  have hc := RiemannRochTop_rotGen_conjugate hG x k (r x) (hr x)
  have he := b4_rotGen_unique hE hG (k • x) (r (k • x)) (k * r x * k⁻¹) (hr _) hc
  rw [he, map_mul, map_mul, map_inv, mul_comm (χ k) (χ (r x)), mul_assoc,
    mul_inv_cancel, mul_one]

end HodgeLean.Foundations.Program
