import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.AbelLocalPrimitives
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.PrimitiveChartDerivative
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.AbelDiscNormalization

/-! # Differential of the original analytic Abel map

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open HodgeLean.Foundations.Program Set Filter
open scoped Manifold ContDiff TensorProduct Topology
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [Module.Finite ℤ (b3_periodLattice E C)]
  [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]

/-- Differentiating normalized local Abel primitives returns the original basis-form tangent value.
Source: Forster, §21; abelJacobi_localLift_of_primitives.
HC no distance; AV milestone no distance. -/
theorem abelJacobi_basis_differential_of_primitives
    (h : Module.finrank ℂ E = 1) (p : C) (aj : C → b3_Jacobian E C)
    (haj : b3_IsAbelJacobi E C p aj) (q : C) {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℂ (b3_HolForm E C)) (κ : E →L[ℂ] ℂ) (u : E)
    (hκ : ∀ w : E, w = κ w • u) (hκu : κ u = 1) (R : ℝ) (hR : 0 < R)
    (hchart : ∀ z : ℂ, ‖z‖ < R → chartAt E q q + z • u ∈ (chartAt E q).target)
    (G : ι → ℂ → ℂ)
    (hG : ∀ j, ∀ z ∈ Metric.ball (0 : ℂ) R,
      HasDerivAt (G j) (b3A_discCoef (b j).val q u z) z) (j : ι) (v : E) :
    periodLinear (b j) (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) aj q v) =
      (b j).val ⟨q, v⟩ := by
  obtain ⟨c, g, _, hg, he, hvalues⟩ :=
    abelJacobi_localLift_of_primitives h p aj haj q b κ u hκ hκu R hR hchart G hG
  have hd := torusCover_lift_mfderiv (b3_periodF E C) aj g q
    (hg.mdifferentiableAt (by simp)) he
  have hcomp : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ)
      (fun y : C ↦ periodLinear (b j) (g y)) q v =
      periodLinear (b j) (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) g q v) := by
    have hh := mfderiv_comp_apply q (periodLinear (b j)).mdifferentiableAt
      (hg.mdifferentiableAt (by simp)) v
    have hl : mfderiv 𝓘(ℂ, b3Rest2_VJ E C) 𝓘(ℂ, ℂ) (periodLinear (b j)) (g q) =
        periodLinear (b j) := ContinuousLinearMap.mfderiv_eq _
    exact hh.trans (congrArg (fun L : b3Rest2_VJ E C →L[ℂ] ℂ ↦
      L (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) g q v)) hl)
  have hfn : (fun y : C ↦ periodLinear (b j) (g y)) =
      (fun y : C ↦ periodLinear (b j) c + (G j (κ (chartAt E q y - chartAt E q q)) - G j 0)) :=
    funext (hvalues j)
  have hdiff := congrArg (fun f : C → ℂ ↦ tangentSpaceCastModel 𝓘(ℂ, ℂ) (f q)
    (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ) f q v)) hfn
  have hp : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ)
      (fun y : C ↦ periodLinear (b j) c + (G j (κ (chartAt E q y - chartAt E q q)) - G j 0)) q v =
      b3A_discCoef (b j).val q u 0 * κ v :=
    primitive_centeredChart_mfderiv q κ (G j) _ (periodLinear (b j) c)
      (hG j 0 (Metric.mem_ball_self hR)) v
  have hs : b3A_discCoef (b j).val q u 0 * κ v = (b j).val ⟨q, v⟩ := by
    rw [discCoef_zero]
    have hh := (b3Forms_holCLM (b j) q).map_smul (κ v) u
    rw [← hκ v] at hh
    change (b j).val ⟨q, v⟩ = (κ v) • (b j).val ⟨q, u⟩ at hh
    have hm : (κ v) • (b j).val ⟨q, u⟩ = (b j).val ⟨q, u⟩ * κ v := by
      rw [smul_eq_mul, mul_comm]
    exact hm.symm.trans hh.symm
  exact (congrArg (fun L : E →L[ℂ] b3Rest2_VJ E C ↦ periodLinear (b j) (L v)) hd).trans
    (hcomp.symm.trans (hdiff.trans (hp.trans hs)))

/-- The original analytic Abel map pulls each original period covector back to its curve tangent value.
Source: Forster, §21; abelJacobi_basis_differential_of_primitives.
HC no distance; AV milestone no distance. -/
theorem abelJacobi_invariant_differential
    (h : Module.finrank ℂ E = 1) (p : C) (aj : C → b3_Jacobian E C)
    (haj : b3_IsAbelJacobi E C p aj) (θ : b3_HolForm E C) (q : C) (v : E) :
    periodLinear θ (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) aj q v) = θ.val ⟨q, v⟩ := by
  letI := b3_holForm_finiteDimensional (C := C) h
  let b := Module.finBasis ℂ (b3_HolForm E C)
  let bE := Module.finBasisOfFinrankEq ℂ E h
  let u := bE 0
  let κ : E →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (bE.coord 0)
  have hκ : ∀ w : E, w = κ w • u := by
    intro w
    conv_lhs => rw [← bE.sum_repr w]
    simp [κ, u]
  have hκu : κ u = 1 := by simp [κ, u]
  have hu : u ≠ 0 := bE.ne_zero 0
  obtain ⟨R, hR, hchart⟩ := b3A_chart_radius u hu q
  have hex : ∀ j, ∃ G : ℂ → ℂ, ∀ z ∈ Metric.ball (0 : ℂ) R,
      HasDerivAt G (b3A_discCoef (b j).val q u z) z := by
    intro j
    exact DifferentiableOn.isExactOn_ball fun z hz ↦
      (b3A_discCoef_differentiableAt (b j).2 q u
        (hchart z (mem_ball_zero_iff.1 hz))).differentiableWithinAt
  choose G hG using hex
  let w : b3Rest2_VJ E C := mfderiv 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) aj q v
  let ev₁ : b3_HolForm E C →ₗ[ℂ] ℂ :=
    (ContinuousLinearMap.apply ℂ ℂ w).toLinearMap.comp (periodFormEquiv h).toLinearMap
  let ev₂ : b3_HolForm E C →ₗ[ℂ] ℂ :=
    { toFun η := η.val ⟨q, v⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hev : ev₁ = ev₂ := by
    apply b.ext
    intro j
    change periodFormEquiv h (b j) w = (b j).val ⟨q, v⟩
    exact (congrArg (fun L : b3Rest2_VJ E C →L[ℂ] ℂ ↦ L w)
      (periodFormEquiv_apply h (b j))).trans
        (abelJacobi_basis_differential_of_primitives h p aj haj q b κ u hκ hκu R hR hchart G hG j v)
  have hh := LinearMap.congr_fun hev θ
  exact (congrArg (fun L : b3Rest2_VJ E C →L[ℂ] ℂ ↦ L w)
    (periodFormEquiv_apply h θ)).symm.trans hh

/-- Pullback of the original invariant period form along an analytic Abel map is the original form.
Source: Forster, §21; abelJacobi_invariant_differential.
HC no distance; AV milestone no distance. -/
theorem abelJacobi_invariant_pullback
    (h : Module.finrank ℂ E = 1) (p : C) (aj : C → b3_Jacobian E C)
    (haj : b3_IsAbelJacobi E C p aj) (θ : b3_HolForm E C) :
    b3_pullback E (b3Rest2_VJ E C) aj (b3A_invForm (b3_periodF E C) (periodLinear θ)) = θ.val := by
  funext v
  exact abelJacobi_invariant_differential h p aj haj θ v.1 v.2

#print axioms abelJacobi_basis_differential_of_primitives
#print axioms abelJacobi_invariant_differential
#print axioms abelJacobi_invariant_pullback

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
