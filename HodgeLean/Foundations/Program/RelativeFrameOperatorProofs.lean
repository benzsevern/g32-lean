import HodgeLean.Foundations.Program.RelativeFrameOperatorDefs
import HodgeLean.Foundations.Program.CurveJacobian
import HodgeLean.Foundations.Program.RelativeFrameOperatorSectors
import HodgeLean.Foundations.Program.RelativeFrameOperatorAnalytic
import HodgeLean.Foundations.Program.RelativeFrameOperatorDescent
import HodgeLean.Foundations.Program.RelativeFrameOperatorGluing
import HodgeLean.Foundations.Program.RelativeFrameOperatorCutoffCore
import HodgeLean.Foundations.Program.RelativeFrameOperatorNonSurjective

set_option maxHeartbeats 400000

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_delta_analytic_aux {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (D : rf4_OuterData C O) :
    AnalyticOnNhd ℂ (rf4_delta D) (rf4_polydisc D.m D.r) := by
  exact rf4_delta_analytic_core D

theorem rf4_sector_injective_aux (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) (c ε : ℂ)
    (hε : ‖ε‖ < r) (g : Fin n → b63r_bddHol (Metric.ball c (2 * r)))
    (hg : ∀ w ∈ rf4_innerDisc n r ε,
      rf4_sectorCoeff n (fun j ↦ rf4_extendBdd (g j)) (c + ε) w = 0) :
    g = 0 := by
  exact rf4_sector_injective_core n hn r hr c ε hε g hg

theorem rf4_sector_surjective_aux (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) (c ε : ℂ)
    (hε : ‖ε‖ < r) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (rf4_innerDisc n r ε))
    (hb : BddAbove ((fun w ↦ ‖f w‖) '' rf4_innerDisc n r ε)) :
    ∃ g : Fin n → b63r_bddHol (Metric.ball c (2 * r)), ∀ w ∈ rf4_innerDisc n r ε,
      f w = rf4_sectorCoeff n (fun j ↦ rf4_extendBdd (g j)) (c + ε) w := by
  exact rf4_sector_surjective_core n hn r hr c ε hε f hf hb

theorem rf4_kernel_equiv_aux {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) :
    ∃ e : (rf4_delta D ε).ker ≃ₗ[ℂ] b3_HolForm ℂ X,
      ∀ k : (rf4_delta D ε).ker, (e k : TangentBundle 𝓘(ℂ, ℂ) X → ℂ) = rf4_glue S k := by
  exact rf4_kernel_equiv_core S

theorem rf4_ker_finrank_aux {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] (S : rf4_Plumbing D ε X) :
    FiniteDimensional ℂ (rf4_delta D ε).ker ∧
      Module.finrank ℂ (rf4_delta D ε).ker = Module.finrank ℂ (b3_HolForm ℂ X) := by
  obtain ⟨e, _⟩ := rf4_kernel_equiv_aux S
  letI := b3_holForm_finiteDimensional (C := X) (Module.finrank_self ℂ)
  exact ⟨Module.Finite.equiv e.symm, e.finrank_eq⟩

theorem rf4_cutoff_obstruction_aux {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
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
  exact rf4_cutoff_obstruction_core S

theorem rf4_delta_range_cofg_aux {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] (S : rf4_Plumbing D ε X) :
    (rf4_delta D ε).range.CoFG := by
  obtain ⟨τ, hτ, _⟩ := rf4_cutoff_obstruction_aux S
  obtain ⟨w, hw, hgw⟩ := b4c_exists_meroForm (C := X) (Module.finrank_self ℂ)
  haveI := (rf2_dbar_forms X w hw hgw).1
  exact (Submodule.CoFG.ker τ).of_le hτ

theorem rf4_delta_isFredholm_aux {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] (S : rf4_Plumbing D ε X) :
    (rf4_delta D ε).IsFredholm := by
  exact b63r_isFredholm_of_finite (rf4_delta D ε) (rf4_ker_finrank_aux S).1
    (rf4_delta_range_cofg_aux S)

theorem rf4_delta_not_surjective_aux {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] (S : rf4_Plumbing D ε X) (hm : 0 < D.m) :
    ¬ Function.Surjective (rf4_delta D ε) := by
  exact rf4_delta_not_surjective_core S hm

end HodgeLean.Foundations.Program
