import HodgeLean.Foundations.Curves.AbelTheorem.IntegralTestDual
import HodgeLean.Foundations.Curves.AbelTheorem.LocalMeromorphicPairing
import HodgeLean.Foundations.Curves.AbelTheorem.RationalVertexShift
import HodgeLean.Foundations.Curves.AbelTheorem.LoopIntegralShift

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory Metric
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem exists_integral_meromorphic_dual (h : Module.finrank ℂ E = 1)
    (D : C →₀ ℤ) (w : b4c_MeroForm E C h)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (γ : b3_SmoothLoop E C) (hav : ∀ t, γ.val t ∉ D.support)
    {ι : Type} [Fintype ι] (δ : ι → ℝ → C)
    (hδ : ∀ j, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (δ j))
    (hbound : ∀ j, range (δ j) = (δ j) '' Icc (0 : ℝ) 1)
    (htr : ∀ j s t, γ.val s = δ j t →
      b3_orient E (b3_velocity E C γ.val s) (b3_velocity E C (δ j) t) ≠ 0)
    (hends : ∀ j s, γ.val s ≠ δ j 0 ∧ γ.val s ≠ δ j 1) :
    ∃ η : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth η ∧
      (∀ x ∈ D.support, η =ᶠ[𝓝 x] 0) ∧
      (∀ j, ∃ n : ℤ, b3Forms_lineIntegral η (δ j) 0 1 = (n : ℝ)) ∧
      (∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α → b3Forms_d α = 0 →
        b3Forms_integral (b3Rest_b h) (b3Forms_wedgeForm α η) =
          b3Forms_lineIntegral α γ.val 0 1) ∧
      ∀ P : ℂ →L[ℝ] ℝ, b3Forms_integral (b3Rest_b h)
        (b3Forms_wedgeForm (b4c_residue_realForm h (b4c_residue_normalizedForm h w) P) η) =
          P (loopIntegral γ w) := by
  classical
  obtain ⟨a, haδ⟩ := exists_shift_avoiding_rational_path_vertices γ δ hδ htr
  have hPa : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun t => γ.val (t + a)) :=
    b3A_contMDiff_reparam γ.property.2 (contDiff_id.add contDiff_const)
  let γa : b3_SmoothLoop E C := ⟨fun t => γ.val (t + a), by
    intro t
    change γ.val (t + 1 + a) = γ.val (t + a)
    rw [show t + 1 + a = (t + a) + 1 by ring]
    exact γ.property.1 (t + a), hPa⟩
  let S : Set C := D.support
  have hS : IsClosed S := D.support.finite_toSet.isClosed
  obtain ⟨N, hN, x, r, hK, hx, hr, hball, hmem⟩ :=
    compact_chart_cover_avoiding_closed_set (E := E) γa.val hPa.continuous γa.property.1
      S hS (fun t => hav (t + a))
  let K : b3Rest_Cover E γa.val := ⟨N, hN, x, r, hx, hr, hball, hmem⟩
  let T : Set C := S ∪ ⋃ j, range (δ j)
  have hTc : IsClosed T := hS.union (isClosed_iUnion_of_finite fun j => by
    have hc : IsCompact (range (δ j)) := by
      rw [hbound j]
      exact isCompact_Icc.image (hδ j).continuous
    exact hc.isClosed)
  have hw : ∀ k : ℤ, γa.val (k / K.N) ∉ T := by
    intro k hk
    rcases hk with hs | ht
    · exact hav (k / K.N + a) hs
    · obtain ⟨j, hj⟩ := mem_iUnion.mp ht
      rw [hbound j] at hj
      obtain ⟨u, hu, he⟩ := hj
      exact haδ K.N k j u hu he.symm
  have htra : ∀ j s t, γa.val s = δ j t →
      b3_orient E (b3_velocity E C γa.val s) (b3_velocity E C (δ j) t) ≠ 0 := by
    intro j s t he
    have hv := b3Rest2_velocity_shift γ.property.2 a s
    change b3_velocity E C γa.val s = b3_velocity E C γ.val (s + a) at hv
    rw [hv]
    exact htr j (s + a) t he
  obtain ⟨η, hη, hzero, hout, hint, hlocal⟩ := exists_dual_with_integral_test_paths h K
    hPa γa.property.1 δ hδ T hTc S (fun _ hs => Or.inl hs)
    (fun k => (image_mono ball_subset_closedBall).trans (hK k).2) hw
    (fun j s => Or.inr (mem_iUnion.mpr ⟨j, s, rfl⟩))
    (fun j t => hends j (t + a))
    (fun i j => finite_transverse_crossings_in_box γa.val (δ j) hPa (hδ j) (htra j) _ _ _ _)
    htra
  have hdual : ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α → b3Forms_d α = 0 →
      b3Forms_integral (b3Rest_b h) (b3Forms_wedgeForm α η) =
        b3Forms_lineIntegral α γ.val 0 1 := by
    intro α hα hd
    choose f hf using fun k : ℤ => b3Forms_exists_local_primitive hα hd
      (K.x k) (convex_ball _ _) isOpen_ball (K.ball_sub k)
    exact (hlocal α hα f hf).trans (b3Rest2_lineIntegral_shift α γ.property.2 γ.property.1 a)
  refine ⟨η, hη, hzero, hint, hdual, ?_⟩
  intro P
  have he := local_dual_pairs_meromorphic_form h D w ha γa (fun t => hav (t + a))
    K hK η hout hlocal P
  exact he.trans (congrArg P (loop_integral_parameter_shift γ w a))

end HodgeLean.Foundations.Curves.AbelTheorem
