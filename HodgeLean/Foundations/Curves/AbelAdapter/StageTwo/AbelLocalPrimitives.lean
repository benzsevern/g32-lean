import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.PeriodBasisCoordinates

/-! # Normalized local lifts of the analytic Abel map

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

/-- Local Abel lifts retain the literal primitives of each specified basis form.
Source: Forster, §21; b3Rest_abelJacobi_disc and quotientBasisEquiv_symm_eval.
HC no distance; AV milestone no distance. -/
theorem abelJacobi_localLift_of_primitives
    (h : Module.finrank ℂ E = 1) (p : C) (aj : C → b3_Jacobian E C)
    (haj : b3_IsAbelJacobi E C p aj) (q : C) {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℂ (b3_HolForm E C)) (κ : E →L[ℂ] ℂ) (u : E)
    (hκ : ∀ w : E, w = κ w • u) (hκu : κ u = 1) (R : ℝ) (hR : 0 < R)
    (hchart : ∀ z : ℂ, ‖z‖ < R → chartAt E q q + z • u ∈ (chartAt E q).target)
    (G : ι → ℂ → ℂ)
    (hG : ∀ j, ∀ z ∈ Metric.ball (0 : ℂ) R,
      HasDerivAt (G j) (b3A_discCoef (b j).val q u z) z) :
    ∃ c : b3Rest2_VJ E C, ∃ g : C → b3Rest2_VJ E C,
      b3Rest2_covHom (E := E) (C := C) c = aj q ∧ ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) ω g q ∧
      (aj =ᶠ[𝓝 q] b3Rest2_covHom (E := E) (C := C) ∘ g) ∧
      ∀ j y, periodLinear (b j) (g y) = periodLinear (b j) c +
        (G j (κ (chartAt E q y - chartAt E q q)) - G j 0) := by
  let L := (quotientBasisEquiv h b).symm.toLinearMap
  have hL : L.comp (b3Rest_evalQ b) = LinearMap.id := by
    apply LinearMap.ext
    intro w
    change (quotientBasisEquiv h b).symm (b3Rest_evalQ b w) = w
    rw [← quotientBasisEquiv_apply h b w]
    exact (quotientBasisEquiv h b).symm_apply_apply w
  let Gv : ℂ → (ι → ℂ) := fun z j ↦ G j z - G j 0
  let ζ : C → ℂ := fun y ↦ κ (chartAt E q y - chartAt E q q)
  have hζ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω ζ q := by
    have h1 := contMDiffAt_extChartAt (I := 𝓘(ℂ, E)) (n := ω) (x := q)
    have h2 : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun w : E ↦ κ (w - chartAt E q q)) :=
      (κ.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff
    exact (h2 _).comp q h1
  have hζ0 : ζ q = 0 := by simp only [ζ, sub_self, map_zero]
  obtain ⟨c, hc⟩ := (b3Rest2_covHom_spec (E := E) (C := C)).2 (aj q)
  let g : C → b3Rest2_VJ E C := fun y ↦ c + b2_coord (b3Rest2_QJ E C) (L (Gv (ζ y)))
  have hg : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) ω g q := by
    have hGv : ContDiffAt ℂ ω Gv 0 := by
      have hd : DifferentiableOn ℂ Gv (Metric.ball (0 : ℂ) R) := by
        rw [differentiableOn_pi]
        intro j z hz
        exact ((hG j z hz).differentiableAt.sub_const _).differentiableWithinAt
      exact (hd.analyticAt (Metric.ball_mem_nhds 0 hR)).contDiffAt
    have hGv' : ContDiffAt ℂ ω Gv (ζ q) := by rw [hζ0]; exact hGv
    exact contMDiffAt_const.add
      ((b3Rest_contDiffAt_coord_comp L Gv hGv').contMDiffAt.comp q hζ)
  refine ⟨c, g, hc, hg, ?_, ?_⟩
  · have hU : (chartAt E q).source ∩ {y | ‖ζ y‖ < R} ∈ 𝓝 q := by
      refine inter_mem ((chartAt E q).open_source.mem_nhds (mem_chart_source E q)) ?_
      exact hζ.continuousAt.preimage_mem_nhds
        ((isOpen_lt continuous_norm continuous_const).mem_nhds (by change ‖ζ q‖ < R; simpa only [hζ0, norm_zero] using hR))
    filter_upwards [hU] with y ⟨hy, hyR⟩
    have hdisc : b3A_disc q u (ζ y) = y := by
      rw [b3A_disc, ← hκ, add_sub_cancel]
      exact (chartAt E q).left_inv hy
    have hseg := b3Rest_abelJacobi_disc b L hL p aj haj κ u hκ hκu q hchart G hG (ζ y) hyR
    rw [hdisc] at hseg
    change aj y = b3Rest2_covHom (E := E) (C := C) (c + b2_coord (b3Rest2_QJ E C) (L (Gv (ζ y))))
    rw [map_add, hc, b3Rest2_covHom_coord]
    exact hseg
  · intro j y
    change periodLinear (b j) (c + b2_coord (b3Rest2_QJ E C)
      ((quotientBasisEquiv h b).symm (Gv (ζ y)))) = _
    rw [map_add, periodLinear_basis_coord h b (Gv (ζ y)) j]

#print axioms abelJacobi_localLift_of_primitives

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
