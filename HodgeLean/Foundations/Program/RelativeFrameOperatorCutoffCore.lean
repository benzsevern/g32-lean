import HodgeLean.Foundations.Program.RelativeFrameOperatorRecoveryMatch

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_cutoff_obstruction_core {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] (S : rf4_Plumbing D ε X) :
    ∃ τ : rf4_Tgt D →ₗ[ℂ] (rf2_smoothForms X 1 1 ⧸ rf2_boundaries X),
      LinearMap.ker τ ≤ (rf4_delta D ε).range ∧
        ∀ φ : rf4_Tgt D, ∃ σ : rf2_smoothForms X 1 1, Submodule.Quotient.mk σ = τ φ ∧
          ∀ (y : X) (z : (chartAt ℂ y).target),
            (chartAt ℂ y).symm z ∉
                ⋃ x, S.h '' ((D.P.chart (D.ann x)).symm '' b63r_annulus (D.deg x) D.r) →
              σ.val y z = 0 := by
  classical
  obtain ⟨χ, hχ, M, hM, hSupp⟩ := rf4_cutoff_density_data S
  let τ := (rf2_boundaries X).mkQ.comp M
  refine ⟨τ, ?_, ?_⟩
  · intro φ hφ
    have hzero := LinearMap.mem_ker.mp hφ
    change Submodule.Quotient.mk (M φ) = 0 at hzero
    obtain ⟨v, hv⟩ := rf4_boundary_representative X (M φ) hzero
    obtain ⟨α, hα⟩ := rf4_outerCorrection_tuple S χ (fun x ↦ (hχ x).1)
      (fun x ↦ (hχ x).2.2.1) (fun x ↦ (hχ x).2.2.2.1) (fun x ↦ (hχ x).2.2.2.2)
      φ v (M φ) (hM φ) hv
    have hβ (x : Fin D.m) := rf4_innerCorrection_data S χ (fun y ↦ (hχ y).1)
      (fun y ↦ (hχ y).2.1) (fun y ↦ (hχ y).2.2.2.1) (fun y ↦ (hχ y).2.2.2.2)
      φ v (M φ) (hM φ) hv x
    apply rf4_delta_mem_range_of_local_coefficients S φ α
      (fun x ↦ rf4_innerCorrection S χ φ v x (S.w x))
      (fun x ↦ (hβ x).1) (fun x ↦ (hβ x).2)
    intro x u
    rw [hα (D.ann x) ⟨u, (D.hann x).ge u.property⟩]
    exact rf4_correction_annulus_difference S χ φ v x u
  · intro φ
    exact ⟨M φ, rfl, hSupp φ⟩

end HodgeLean.Foundations.Program
