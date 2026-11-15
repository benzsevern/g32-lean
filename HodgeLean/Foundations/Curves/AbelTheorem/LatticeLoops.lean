import HodgeLean.Foundations.Curves.AbelTheorem.LoopAvoidance

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology Set
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [ConnectedSpace C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem lattice_element_good_path (p : C) (ell : b3_periodLattice E C) :
    ∃ γ : ℝ → C, b3A_IsGoodPath (E := E) γ p p ∧
      ∀ θ : b3_HolForm E C, b3_pathIntegral E C γ θ = ell.val θ := by
  have hex (u : b3_HolForm E C → ℂ) (hu : u ∈ b3_periodLattice E C) :
      ∃ γ : ℝ → C, b3A_IsGoodPath (E := E) γ p p ∧
        ∀ θ : b3_HolForm E C, b3_pathIntegral E C γ θ = u θ := by
    change u ∈ AddSubgroup.closure (Set.range (b3_period E C)) at hu
    induction hu using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨δ, rfl⟩ := hu
      obtain ⟨α, hα⟩ := b3A_joined (E := E) p (δ.val 0)
      have hδ := b3A_isGoodPath_reparam δ.val δ.property.2
      have hd01 : δ.val 1 = δ.val 0 := by simpa only [zero_add] using δ.property.1 0
      rw [hd01] at hδ
      have hloop := (hα.trans hδ).trans hα.symm
      refine ⟨_, hloop, fun θ => ?_⟩
      rw [b3A_pathIntegral_trans θ.property (hα.trans hδ) hα.symm,
        b3A_pathIntegral_trans θ.property hα hδ,
        b3A_pathIntegral_reparam θ.property δ.val δ.property.2,
        b3A_pathIntegral_symm θ.property α hα.1]
      change _ + _ + -_ = b3_pathIntegral E C δ.val θ
      ring
    | zero =>
      refine ⟨fun _ => p, b3A_isGoodPath_const p, fun θ => ?_⟩
      have hz : (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) ⟨p, 0⟩ = 0 := by
        simpa only [zero_smul, zero_mul] using b3A_holForm_smul_apply θ.property p 0 0
      simp only [b3_pathIntegral, b3_velocity, mfderiv_const, ContinuousLinearMap.zero_apply,
        hz, intervalIntegral.integral_zero, Pi.zero_apply]
    | add u v _ _ ihu ihv =>
      obtain ⟨γ, hγ, hgu⟩ := ihu
      obtain ⟨δ, hδ, hdv⟩ := ihv
      refine ⟨_, hγ.trans hδ, fun θ => ?_⟩
      rw [b3A_pathIntegral_trans θ.property hγ hδ, hgu, hdv]
      rfl
    | neg u _ ihu =>
      obtain ⟨γ, hγ, hgu⟩ := ihu
      refine ⟨_, hγ.symm, fun θ => ?_⟩
      rw [b3A_pathIntegral_symm θ.property γ hγ.1, hgu]
      rfl
  exact hex ell.val ell.property

theorem lattice_element_loop_avoiding (h : Module.finrank ℂ E = 1) (p : C)
    (s : Finset C) (ell : b3_periodLattice E C) :
    ∃ γ : b3_SmoothLoop E C, (∀ t, γ.val t ∉ s) ∧ b3_latticePeriod E C γ = ell := by
  obtain ⟨δ, hδ, hp⟩ := lattice_element_good_path p ell
  obtain ⟨γ, hav, he⟩ := loop_periods_avoiding_finite h p s (b3A_toLoop hδ)
  refine ⟨γ, hav, Subtype.ext ?_⟩
  change b3_period E C γ = ell.val
  rw [he]
  funext θ
  exact (b3A_toLoop_pathIntegral θ hδ).trans (hp θ)

end HodgeLean.Foundations.Curves.AbelTheorem
