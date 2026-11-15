import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSegments

noncomputable section

namespace HodgeLean.Foundations.Program

open Manifold Filter Topology Set
open scoped Manifold ContDiff

theorem b6m_contMDiffAt_complex_of_unramified_comp {D X : Type}
    [TopologicalSpace D] [TopologicalSpace X] [ChartedSpace ℂ D] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω D] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (g : ℂ → D) (k : D → X) (z : ℂ) (hg : ContinuousAt g z)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hkd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k (g z) ≠ 0)
    (hkg : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (k ∘ g) z) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g z := by
  let ψ := extChartAt 𝓘(ℂ, ℂ) (g z)
  let G : ℂ → ℂ := ψ ∘ g
  let K := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g z) k
  have hGc : ContinuousAt G z :=
    (contMDiffAt_extChartAt (I := 𝓘(ℂ, ℂ)) (n := ω) (x := g z)).continuousAt.comp hg
  have hK : AnalyticAt ℂ K (G z) :=
    b4cov_analyticOnNhd k hk (g z) _ (b4cov_mem_good k (g z))
  have hKd : fderiv ℂ K (G z) ≠ 0 :=
    hkd ∘ (b4cov_mfderiv_eq_zero_iff k hk (g z) (g z)
      (mem_extChartAt_source _) (mem_extChartAt_source _)).mpr
  have heq : K ∘ G =ᶠ[𝓝 z] extChartAt 𝓘(ℂ, ℂ) (k (g z)) ∘ (k ∘ g) := by
    have hsrc : ψ.source ∈ 𝓝 (g z) := extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) (g z)
    filter_upwards [hg.eventually hsrc] with w hw
    change extChartAt 𝓘(ℂ, ℂ) (k (g z)) (k (ψ.symm (ψ (g w)))) = _
    rw [ψ.left_inv hw]
    rfl
  have hF : ContDiffAt ℂ ω (extChartAt 𝓘(ℂ, ℂ) (k (g z)) ∘ (k ∘ g)) z := by
    have H := (contMDiffAt_iff_target.mp hkg).2.contDiffAt
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply] using H
  have hG := b6m_analyticAt_of_comp hGc hK hKd
    (hF.analyticAt.congr heq.symm)
  apply contMDiffAt_iff_target.mpr
  refine ⟨hg, ?_⟩
  apply contMDiffAt_iff_contDiffAt.mpr
  simpa only [G, ψ, extChartAt_coe, modelWithCornersSelf_coe] using hG.contDiffAt

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6m_filling_local_chart {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (f : C → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (x : C) (a : ℂ) (hxa : f x = (a : OnePoint ℂ))
    (U : Set C) (hU : U ∈ 𝓝 x)
    (hfd : ∀ y ∈ U, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f y ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ ι : ℂ → C, ι a = x ∧ ι '' Metric.ball a r ∈ 𝓝 x ∧
      ∀ z ∈ Metric.ball a r,
        ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω ι z ∧ f (ι z) = (z : OnePoint ℂ) ∧ ι z ∈ U := by
  obtain ⟨F, hxF, hF⟩ :=
    b4cov_isLocalHomeomorphOn (by simp) (by simp) f hf x (hfd x (mem_of_mem_nhds hU))
  let ι : ℂ → C := fun z ↦ F.symm (z : OnePoint ℂ)
  have haF : (a : OnePoint ℂ) ∈ F.target := by
    rw [← hxa, hF]
    exact F.map_source hxF
  have hia : ι a = x := by
    change F.symm (a : OnePoint ℂ) = x
    rw [← hxa, hF]
    exact F.left_inv hxF
  have hι (z : ℂ) (hz : (z : OnePoint ℂ) ∈ F.target) : ContinuousAt ι z :=
    (F.symm.continuousAt hz).comp OnePoint.continuous_coe.continuousAt
  have hN : {z : ℂ | (z : OnePoint ℂ) ∈ F.target ∧ ι z ∈ U} ∈ 𝓝 a := by
    apply inter_mem
    · exact OnePoint.continuous_coe.continuousAt.preimage_mem_nhds
        (F.open_target.mem_nhds haF)
    · apply (hι a haF).preimage_mem_nhds
      simpa [hia] using hU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hN
  have him : ι '' Metric.ball a r ∈ 𝓝 x := by
    have hbase : (fun z : ℂ ↦ (z : OnePoint ℂ)) '' Metric.ball a r ∈ 𝓝 (f x) :=
      (OnePoint.isOpenMap_coe _ Metric.isOpen_ball).mem_nhds
        ⟨a, Metric.mem_ball_self hr, hxa.symm⟩
    filter_upwards [F.open_source.mem_nhds hxF,
      hf.continuous.continuousAt.preimage_mem_nhds hbase] with y hyF hy
    obtain ⟨z, hz, hzy⟩ := hy
    change (z : OnePoint ℂ) = f y at hzy
    refine ⟨z, hz, ?_⟩
    change F.symm (z : OnePoint ℂ) = y
    rw [hzy, hF]
    exact F.left_inv hyF
  refine ⟨r, hr, ι, hia, him, ?_⟩
  intro z hz
  have hzF := (hball hz).1
  have hzU := (hball hz).2
  have heq : f ∘ ι =ᶠ[𝓝 z] (fun w : ℂ ↦ (w : OnePoint ℂ)) := by
    filter_upwards [OnePoint.continuous_coe.continuousAt.preimage_mem_nhds
      (F.open_target.mem_nhds hzF)] with w hw
    change f (F.symm (w : OnePoint ℂ)) = (w : OnePoint ℂ)
    rw [hF]
    exact F.right_inv hw
  refine ⟨b6m_contMDiffAt_complex_of_unramified_comp ι f z (hι z hzF) hf
    (hfd (ι z) hzU) ?_, heq.eq_of_nhds, hzU⟩
  exact (b4cov_coe_contMDiff z).congr_of_eventuallyEq heq

theorem b6m_filling_local_good_paths {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (x : C) (a : ℂ) (hxa : f x = (a : OnePoint ℂ))
    (U : Set C) (hU : U ∈ 𝓝 x)
    (hfd : ∀ y ∈ U, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f y ≠ 0)
    (hkd : ∀ y ∈ U, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k (e y) ≠ 0) :
    ∃ V ∈ 𝓝 x, ∀ y ∈ V, ∃ γ : ℝ → C,
      b3A_IsGoodPath (E := ℂ) γ x y ∧
      b3A_IsGoodPath (E := ℂ) (e ∘ γ) (e x) (e y) ∧ (∀ s, γ s ∈ U) ∧
      (Set.range γ \ {x | ∃ z : ℂ, (z : OnePoint ℂ) = f x ∧
        ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b}).Finite := by
  obtain ⟨r, hr, ι, hia, him, hchart⟩ := b6m_filling_local_chart f hf x a hxa U hU hfd
  refine ⟨ι '' Metric.ball a r, him, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have hseg : segment ℝ a (a + (z - a)) ⊆ Metric.ball a r :=
    (convex_ball a r).segment_subset (Metric.mem_ball_self hr) (by simpa using hz)
  obtain ⟨γ, hγ, hγt, hγr, hbad⟩ := b6m_filling_good_segment b t hb f k hk e he a (z - a) ι
    (fun w hw ↦ (hchart w (hseg hw)).1)
    (fun w hw ↦ (hchart w (hseg hw)).2.1)
    (fun w hw ↦ hkd (ι w) (hchart w (hseg hw)).2.2)
  refine ⟨γ, ?_, ?_, ?_, hbad⟩
  · simpa [hia] using hγ
  · simpa [hia] using hγt
  · intro s
    obtain ⟨w, hw, hws⟩ := hγr s
    rw [← hws]
    exact (hchart w (hseg hw)).2.2

theorem b6m_filling_good_paths_on {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (U : Set C) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hfinite : ∀ x ∈ U, ∃ a : ℂ, f x = (a : OnePoint ℂ))
    (hfd : ∀ x ∈ U, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x ≠ 0)
    (hkd : ∀ x ∈ U, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k (e x) ≠ 0)
    {x y : C} (hx : x ∈ U) (hy : y ∈ U) :
    ∃ γ : ℝ → C, b3A_IsGoodPath (E := ℂ) γ x y ∧
      b3A_IsGoodPath (E := ℂ) (e ∘ γ) (e x) (e y) ∧ (∀ s, γ s ∈ U) ∧
      (Set.range γ \ {x | ∃ z : ℂ, (z : OnePoint ℂ) = f x ∧
        ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b}).Finite := by
  refine hUc.induction₂ (fun x y ↦ ∃ γ : ℝ → C, b3A_IsGoodPath (E := ℂ) γ x y ∧
    b3A_IsGoodPath (E := ℂ) (e ∘ γ) (e x) (e y) ∧ (∀ s, γ s ∈ U) ∧
    (Set.range γ \ {x | ∃ z : ℂ, (z : OnePoint ℂ) = f x ∧
      ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b}).Finite) ?_ ?_ ?_ hx hy
  · intro z hz
    obtain ⟨a, ha⟩ := hfinite z hz
    obtain ⟨V, hV, hpaths⟩ := b6m_filling_local_good_paths b t hb f k hf hk e he
      z a ha U (hUo.mem_nhds hz) hfd hkd
    exact nhdsWithin_le_nhds (Filter.eventually_of_mem hV hpaths)
  · rintro p q r _ _ _ ⟨γ, hγ, hγt, hγU, hγbad⟩ ⟨δ, hδ, hδt, hδU, hδbad⟩
    refine ⟨fun s ↦ if s ≤ 1 / 2 then γ (2 * s) else δ (2 * s - 1),
      hγ.trans hδ, ?_, ?_, ?_⟩
    · simpa only [Function.comp_def, apply_ite] using hγt.trans hδt
    · intro s
      dsimp only
      split_ifs
      · exact hγU _
      · exact hδU _
    · apply (hγbad.union hδbad).subset
      rintro z ⟨⟨s, rfl⟩, hs⟩
      dsimp only at hs ⊢
      split_ifs at hs ⊢
      · exact Or.inl ⟨⟨2 * s, rfl⟩, hs⟩
      · exact Or.inr ⟨⟨2 * s - 1, rfl⟩, hs⟩
  · rintro p q _ _ ⟨γ, hγ, hγt, hγU, hγbad⟩
    refine ⟨fun s ↦ γ (1 - s), hγ.symm, hγt.symm, (fun s ↦ hγU (1 - s)), ?_⟩
    apply hγbad.subset
    rintro z ⟨⟨s, rfl⟩, hs⟩
    exact ⟨⟨1 - s, rfl⟩, hs⟩

theorem b6m_filling_good_paths_off_finite {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hfn : ∃ x y, f x ≠ f y) (hkn : ∃ x y, k x ≠ k y)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x)) :
    ∃ S : Set C, S.Finite ∧ ∀ W : Set C, IsOpen W → IsPreconnected W →
      ∀ x ∈ W \ S, ∀ y ∈ W \ S, ∃ γ : ℝ → C,
      b3A_IsGoodPath (E := ℂ) γ x y ∧
      b3A_IsGoodPath (E := ℂ) (e ∘ γ) (e x) (e y) ∧ (∀ s, γ s ∈ W \ S) ∧
      (Set.range γ \ {x | ∃ z : ℂ, (z : OnePoint ℂ) = f x ∧
        ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b}).Finite := by
  let A : Set C := {x | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x = 0}
  let B : Set D := {y | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k y = 0}
  let S : Set C := A ∪ e ⁻¹' B ∪ f ⁻¹' {OnePoint.infty}
  have hA : A.Finite := b4cov_critical_finite (by simp) f hf hfn
  have hB : B.Finite := b4cov_critical_finite (by simp) k hk hkn
  have hS : S.Finite := (hA.union (Set.Finite.preimage e.injective.injOn hB)).union
    (b4cov_fiber_finite (by simp) f hf hfn OnePoint.infty)
  refine ⟨S, hS, fun W hWo hWc x hx y hy ↦ ?_⟩
  have hconn : IsPreconnected (W \ S) :=
    b4cov_isPreconnected_diff_finite hWo hWc hS
      (fun x _ ↦ b4cov_goodPoint (by simp : Module.finrank ℂ ℂ = 1) x)
  apply b6m_filling_good_paths_on b t hb f k hf hk e he (W \ S)
    (hWo.sdiff hS.isClosed) hconn
    (fun z hz ↦ ?_) (fun z hz ↦ ?_) (fun z hz ↦ ?_) hx hy
  · have hinf : f z ≠ OnePoint.infty := fun h ↦ hz.2 (Or.inr h)
    obtain ⟨a, ha⟩ := OnePoint.ne_infty_iff_exists.mp hinf
    exact ⟨a, ha.symm⟩
  · exact fun h ↦ hz.2 (Or.inl (Or.inl h))
  · exact fun h ↦ hz.2 (Or.inl (Or.inr h))

end HodgeLean.Foundations.Program
