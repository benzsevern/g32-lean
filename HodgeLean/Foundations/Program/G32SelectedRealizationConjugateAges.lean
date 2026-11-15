import HodgeLean.Foundations.Program.G32SelectedRealizationSingleOrbitAges

noncomputable section
open Manifold HodgeLean.Papers
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem g32y_conjugate_exponent_weights
    {E C G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ a : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun y : C ↦ a • y))
    (H : Subgroup G) (x : C) (g k : G) (hg : b4_IsRotGen E x g)
    {m : ℕ} (χ : H →* Multiplicative (ZMod m))
    (w : ZMod m → ℝ) (hw : w 0 = 0)
    (r : C → H) (hr : ∀ y, b4_IsRotGen E y (r y)) :
    ((papersExps H χ (k * g * k⁻¹)).map w).sum =
      ((papersExps H χ g).map w).sum := by
  classical
  letI : Finite (MulAction.orbit G x) := g32y_finite_group_orbit x
  letI : Fintype (MulAction.orbit G x) := Fintype.ofFinite _
  letI : Finite (MulAction.orbit G (k • x)) := g32y_finite_group_orbit (k • x)
  letI : Fintype (MulAction.orbit G (k • x)) := Fintype.ofFinite _
  have hk := RiemannRochTop_rotGen_conjugate hG x k g hg
  rw [← g32y_single_orbit_exponent_weights hE hG H (k • x) _ hk χ w hw r hr,
    ← g32y_single_orbit_exponent_weights hE hG H x g hg χ w hw r hr]
  let e : MulAction.orbit G (k • x) ≃ MulAction.orbit G x :=
    Set.equivOfEq (MulAction.orbit_smul k x)
  exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)

end HodgeLean.Foundations.Program
