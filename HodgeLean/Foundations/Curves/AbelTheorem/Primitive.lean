import HodgeLean.Foundations.Curves.AbelTheorem.ScalarTransport

noncomputable section
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open Manifold Filter Topology Set
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [ConnectedSpace C]

theorem primitive_construction (h : Module.finrank ℂ E = 1) (D : C →₀ ℤ)
    (w : b4c_MeroForm E C h)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (p : divisorComplement D)
    (hperiod : ∀ γ : b3_SmoothLoop E (divisorComplement D),
      Complex.exp (b3_period E (divisorComplement D) γ
        (divisorDifferentialRestriction h D w ha)) = 1) :
    ∃ f : C → ℂ,
      ContinuousOn f (divisorComplement D : Set C) ∧
      (∀ x, x ∉ D.support → f x ≠ 0) ∧
      (∀ (q : divisorComplement D) (γ : ℝ → divisorComplement D),
        b3A_IsGoodPath (E := E) γ p q →
          f q.val = exponentialIntegral (E := E) γ (divisorDifferentialRestriction h D w ha)) ∧
      ∀ x, ∀ᶠ z in 𝓝[≠] 0,
        centeredScalar h f x z ≠ 0 ∧
          HasDerivAt (centeredScalar h f x)
            (HurwitzPrymRR_loc h w x z * centeredScalar h f x z) z := by
  classical
  have hc : IsPreconnected ((Set.univ : Set C) \ (D.support : Set C)) :=
    b4cov_isPreconnected_diff_finite isOpen_univ isPreconnected_univ
      D.support.finite_toSet (fun x _ => b4cov_goodPoint h x)
  have hU : ((Set.univ : Set C) \ (D.support : Set C)) = (divisorComplement D : Set C) := by
    ext x
    simp [divisorComplement]
  rw [hU] at hc
  letI : ConnectedSpace (divisorComplement D) :=
    isConnected_iff_connectedSpace.mp ⟨⟨p.val, p.property⟩, hc⟩
  obtain ⟨F, hF, hFn, hFp⟩ := exponentialPrimitive_on_divisorComplement h D w ha p hperiod
  let f : C → ℂ := fun x => if hx : x ∈ (divisorComplement D : Set C) then F ⟨x, hx⟩ else 0
  have hf (x : divisorComplement D) : f x.val = F x := by
    dsimp only [f]
    split_ifs with hx
    · rfl
    · exact (hx x.property).elim
  have hfc : ContinuousOn f (divisorComplement D : Set C) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (fun x : divisorComplement D => f x.val) = F := funext hf
    change Continuous (fun x : divisorComplement D => f x.val)
    rw [he]
    exact hF.continuous
  have hne (x : C) (hx : x ∉ D.support) : f x ≠ 0 := by
    rw [show f x = F ⟨x, hx⟩ from hf ⟨x, hx⟩]
    exact hFn _
  have hlocal (x : C) (hx : x ∉ D.support) :
      ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω f x := by
    apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : divisorComplement D))).mp
    have he : (fun x : divisorComplement D => f x.val) = F := funext hf
    rw [he]
    exact hF _
  have hcenter := puncturedPrimitive_ambient_derivative h D w ha p F hFp f hf
  refine ⟨f, hfc, hne, fun q γ hγ => (hf q).trans (hFp q γ hγ), fun x => ?_⟩
  have hopen : ((D.support.erase x : Finset C) : Set C)ᶜ ∈ 𝓝 x :=
    ((D.support.erase x).finite_toSet.isClosed.isOpen_compl).mem_nhds (by simp)
  have haway : ∀ᶠ y in 𝓝[≠] x, y ∉ D.support := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hopen,
      (self_mem_nhdsWithin : {x}ᶜ ∈ 𝓝[≠] x)] with y hy hyx
    intro hys
    exact hy (Finset.mem_erase.mpr ⟨hyx, hys⟩)
  have hAaway := RiemannRochAna_inverse_coordinate_punctured h x haway
  have ht : ∀ᶠ z in 𝓝 (0 : ℂ), extChartAt 𝓘(ℂ, E) x x + b4cov_lineEquiv h z ∈
      (extChartAt 𝓘(ℂ, E) x).target := by
    have hcont : Continuous (fun z : ℂ => extChartAt 𝓘(ℂ, E) x x + b4cov_lineEquiv h z) :=
      continuous_const.add (b4cov_lineEquiv h).continuous
    apply hcont.continuousAt.preimage_mem_nhds
    simpa only [map_zero, add_zero] using
      (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  filter_upwards [hAaway, ht.filter_mono nhdsWithin_le_nhds] with z hz hzt
  let y := (extChartAt 𝓘(ℂ, E) x).symm
    (extChartAt 𝓘(ℂ, E) x x + b4cov_lineEquiv h z)
  have hy : y ∈ (extChartAt 𝓘(ℂ, E) x).source :=
    (extChartAt 𝓘(ℂ, E) x).map_target hzt
  have hσ : b4c_centeredCoordinate h x y = z := by
    dsimp only [b4c_centeredCoordinate, y]
    rw [(extChartAt 𝓘(ℂ, E) x).right_inv hzt, add_sub_cancel_left,
      ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨hne y hz, ?_⟩
  have hd := scalar_equation_in_chart h w f x y hy (hlocal y hz) (hcenter ⟨y, hz⟩)
  rw [hσ] at hd
  exact hd

end HodgeLean.Foundations.Curves.AbelTheorem
