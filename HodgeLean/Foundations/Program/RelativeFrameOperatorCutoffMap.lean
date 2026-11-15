import HodgeLean.Foundations.Program.RelativeFrameOperatorTransport

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_cutoff_density_data {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {ε : Fin D.m → ℂ} {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] (S : rf4_Plumbing D ε X) :
    ∃ χ : Fin D.m → ℂ → ℂ,
      (∀ x, ContDiff ℝ ∞ (χ x) ∧
        (∀ u : ℂ, ‖u‖ ^ D.deg x < 5 * D.r / 4 → χ x u = 1) ∧
        (∀ u : ℂ, 7 * D.r / 4 ≤ ‖u‖ ^ D.deg x → χ x u = 0) ∧
        HasCompactSupport (wirtingerDbar (χ x)) ∧
        tsupport (wirtingerDbar (χ x)) ⊆ b63r_annulus (D.deg x) D.r) ∧
      ∃ M : rf4_Tgt D →ₗ[ℂ] rf2_smoothForms X 1 1,
        (∀ φ, (M φ).val = ∑ x,
          rf4_chartTensor (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x))
            (fun u ↦ rf4_extendBdd (φ x) u * wirtingerDbar (χ x) u) 1 1) ∧
        ∀ φ y (z : (chartAt ℂ y).target),
          (chartAt ℂ y).symm z ∉ ⋃ x,
            S.h '' ((D.P.chart (D.ann x)).symm '' b63r_annulus (D.deg x) D.r) →
          (M φ).val y z = 0 := by
  classical
  let e : Fin D.m → OpenPartialHomeomorph X ℂ := fun x ↦
    S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)
  have ht (x : Fin D.m) : b63r_annulus (D.deg x) D.r ⊆ (e x).target := by
    dsimp only [e]
    rw [rf4_stationaryChart_target]
    exact (D.hann x).ge.trans (subset_closure.trans (D.P.contained (D.ann x)))
  choose χ hχ using fun x : Fin D.m ↦
    rf4_annulus_cutoff_dbar (D.deg x) (D.hdeg x) D.r D.hr
  choose L hformula hL using fun x : Fin D.m ↦
    rf4_annulus_density_map (e x) (S.stationary (D.ann x)) (D.deg x) D.r (ht x)
      (χ x) (hχ x).1 (hχ x).2.2.2.1 (hχ x).2.2.2.2
  let M : rf4_Tgt D →ₗ[ℂ] rf2_smoothForms X 1 1 :=
    ∑ x, (L x).comp (LinearMap.proj x)
  refine ⟨χ, hχ, M, ?_, ?_⟩
  · intro φ
    simp only [M, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.coe_sum, hformula]
    rfl
  intro φ y z hz
  have hM : M φ = ∑ x, L x (φ x) := by simp [M]
  rw [hM]
  simp only [Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro x _
  apply hL x (φ x) y z
  rintro ⟨u, hu, heu⟩
  apply hz
  apply mem_iUnion.mpr
  refine ⟨x, ?_⟩
  exact ⟨(D.P.chart (D.ann x)).symm u, ⟨u, hu, rfl⟩, heu⟩

theorem rf4_cutoff_map_supported {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {ε : Fin D.m → ℂ} {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] (S : rf4_Plumbing D ε X) :
    ∃ τ : rf4_Tgt D →ₗ[ℂ] (rf2_smoothForms X 1 1 ⧸ rf2_boundaries X),
      ∀ φ, ∃ σ : rf2_smoothForms X 1 1,
        Submodule.Quotient.mk σ = τ φ ∧
        ∀ y (z : (chartAt ℂ y).target),
          (chartAt ℂ y).symm z ∉ ⋃ x,
            S.h '' ((D.P.chart (D.ann x)).symm '' b63r_annulus (D.deg x) D.r) →
          σ.val y z = 0 := by
  obtain ⟨χ, hχ, M, hM, hs⟩ := rf4_cutoff_density_data S
  let τ := (rf2_boundaries X).mkQ.comp M
  exact ⟨τ, fun φ ↦ ⟨M φ, rfl, hs φ⟩⟩

end HodgeLean.Foundations.Program
