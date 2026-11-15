import HodgeLean.Foundations.Program.RelativeFrameChartsLemmas
import HodgeLean.Foundations.Program.RelativeFrameOperator
import HodgeLean.Foundations.Program.PrymVariationFramesRelative
import HodgeLean.Foundations.Mathlib.FredholmAnalytic

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem rf5_outer_chart_analytic_aux {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {V : Set (Fin 10 → ℂ)} {hV : V ⊆ b6t_polydisc b}
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (F : rf5_FamilyPlumbing b C D V hV) (W : Set (Fin 10 → ℂ)) (hW : IsOpen W)
    (e : (Fin 10 → ℂ) → rf4_Src D) (he : AnalyticOnNhd ℂ e W)
    (φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hφ : φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hp : ∀ y ∈ φ.source, (φ y).1 = y.1.val) :
    ∃ a : (Fin 10 → ℂ) × ℂ → ℂ,
      AnalyticOn ℂ a (φ.target ∩ Prod.fst ⁻¹' (V ∩ W) ∩ φ.symm ⁻¹' {q | q.2 ∈ O}) ∧
      ∀ (t : V) (x : b63l_parameterFibre b C V hV t), t.val ∈ W → x.val ∈ φ.source →
        x.val.2 ∈ O → ∀ v : TangentSpace 𝓘(ℂ, ℂ) x,
          rf4_glue (F.S t) (e t.val) ⟨x, v⟩ = a (φ x.val) * (show ℂ from
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
              (fun z : b63l_parameterFibre b C V hV t ↦ (φ z.val).2) x v) := by
  classical
  let U : Fin D.P.n → (Fin 10 → ℂ) × ℂ → ℂ := fun i ↦
    (fun q : b6t_polydisc b × C ↦ D.P.chart i q.2) ∘ φ.symm
  let A : Fin D.P.n → Set (b6t_polydisc b × C) := fun i ↦ Prod.snd ⁻¹' (D.P.chart i).source
  have hA : ∀ i, IsOpen (A i) := fun i ↦ (D.P.chart i).open_source.preimage continuous_snd
  have hUan : ∀ i, AnalyticOnNhd ℂ (U i) (φ.target ∩ φ.symm ⁻¹' A i) := fun i ↦
    rf5_chart_analyticOnNhd hφ (hA i) (F.outer_analytic i)
  let ai : Fin D.P.n → (Fin 10 → ℂ) × ℂ → ℂ := fun i p ↦
    rf4_extendBdd ((e p.1).1.val i) (U i p) * fderiv ℂ (U i) p ((0 : Fin 10 → ℂ), (1 : ℂ))
  let cond : Fin D.P.n → (Fin 10 → ℂ) × ℂ → Prop := fun i p ↦
    (φ.symm p).2 ∈ (D.P.chart i).source ∧ D.P.chart i (φ.symm p).2 ∈ D.P.piece i
  let a : (Fin 10 → ℂ) × ℂ → ℂ := fun p ↦
    if h : ∃ i, cond i p then ai (Classical.choose h) p else 0
  have ha : ∀ p i, p ∈ φ.target → cond i p → a p = ai i p := by
    intro p i hpt hi
    have h : ∃ i, cond i p := ⟨i, hi⟩
    simp only [a, h, ↓reduceDIte]
    have hc := Classical.choose_spec h
    exact rf5_outer_chart_compat φ (e p.1).1 hpt _ i hc.1 hc.2 hi.1 hi.2
      ((hUan _ p ⟨hpt, hc.1⟩).differentiableAt)
  have hcondO : ∀ q : b6t_polydisc b × C, q.2 ∈ O →
      ∃ i, q.2 ∈ (D.P.chart i).source ∧ D.P.chart i q.2 ∈ D.P.piece i := by
    intro q hq
    obtain ⟨i, z, hz, hzq⟩ := mem_iUnion.mp ((Set.ext_iff.mp D.P.covers _).mp hq)
    have hzt : z ∈ (D.P.chart i).target := D.P.contained i (subset_closure hz)
    refine ⟨i, hzq ▸ (D.P.chart i).map_target hzt, ?_⟩
    rw [← hzq, (D.P.chart i).right_inv hzt]
    exact hz
  refine ⟨a, ?_, ?_⟩
  · rintro p ⟨⟨hpt, hpV, hpW⟩, hpO⟩
    obtain ⟨i, hi⟩ := hcondO _ hpO
    have hN : IsOpen (φ.target ∩ φ.symm ⁻¹' (Prod.snd ⁻¹' ((D.P.chart i).source ∩
        D.P.chart i ⁻¹' D.P.piece i)) ∩ Prod.fst ⁻¹' W) :=
      (φ.isOpen_inter_preimage_symm (((D.P.chart i).isOpen_inter_preimage
        (D.P.isOpen i)).preimage continuous_snd)).inter (hW.preimage continuous_fst)
    have hev : ai i =ᶠ[𝓝 p] a := by
      filter_upwards [hN.mem_nhds ⟨⟨hpt, hi⟩, hpW⟩] with q hq
      exact (ha q i hq.1.1 hq.1.2).symm
    refine AnalyticAt.analyticWithinAt (AnalyticAt.congr ?_ hev)
    have hUp : AnalyticAt ℂ (U i) p := hUan i p ⟨hpt, hi.1⟩
    have he' : AnalyticOnNhd ℂ (fun s ↦ (e s).1.val i) W := fun s hs ↦
      (((rf2_bddForm_coeff D.P i).comp
        (ContinuousLinearMap.fst ℂ (rf2_bddForm D.P) (rf4_Disc D))).analyticAt _).comp (he s hs)
    have hpair : AnalyticAt ℂ (fun q : (Fin 10 → ℂ) × ℂ ↦ (q.1, U i q)) p :=
      analyticAt_fst.prod hUp
    exact ((rf5_extendBdd_analyticAt (D.P.isOpen i) hW he' hpW hi.2).comp_of_eq hpair rfl).mul
      (rf5_vertical_analyticAt hUp)
  · intro t y ht hy hyO v
    have hh : ∀ z : b63l_parameterFibre b C V hV t, (F.S t).h.symm z = z.val.2 := by
      intro z; rw [F.h_eq t]; rfl
    have hfst := rf5_fibre_fst hp y hy
    obtain ⟨i, hi⟩ := hcondO _ hyO
    have hO : ∃ i, (F.S t).h.symm y ∈ (D.P.chart i).source ∧
        D.P.chart i ((F.S t).h.symm y) ∈ D.P.piece i := ⟨i, by rw [hh]; exact hi⟩
    have hc := Classical.choose_spec hO
    simp only [rf4_glue, hO, ↓reduceDIte]
    rw [rf5_outer_compat (F.S t) (e t.val).1 y _ i hc.1 hc.2 (by rw [hh]; exact hi.1)
      (by rw [hh]; exact hi.2) v]
    have hcy : cond i (φ y.val) := by
      simp only [cond, φ.left_inv hy]; exact hi
    rw [ha _ i (φ.map_source hy) hcy]
    have hd := rf5_fibre_mfderiv t (hincl t) hφ hp hy
      (G := fun q : b6t_polydisc b × C ↦ D.P.chart i q.2)
      (hUan i (φ y.val) ⟨φ.map_source hy, by
        simp only [A, Set.mem_preimage, φ.left_inv hy]; exact hi.1⟩)
      (g := fun p ↦ D.P.chart i ((F.S t).h.symm p))
      (Filter.Eventually.of_forall fun z ↦ by simp only [hh]) v
    rw [hd]
    simp only [ai, U, Function.comp_apply, φ.left_inv hy, hfst, hh]
    exact (mul_assoc _ _ _).symm


theorem rf5_sector_chart_analytic_aux {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {V : Set (Fin 10 → ℂ)} {hV : V ⊆ b6t_polydisc b}
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (F : rf5_FamilyPlumbing b C D V hV) (W : Set (Fin 10 → ℂ)) (hW : IsOpen W)
    (e : (Fin 10 → ℂ) → rf4_Src D) (he : AnalyticOnNhd ℂ e W)
    (φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hφ : φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hp : ∀ y ∈ φ.source, (φ y).1 = y.1.val) (x₀ : Fin D.m) :
    ∃ a : (Fin 10 → ℂ) × ℂ → ℂ,
      AnalyticOn ℂ a (φ.target ∩ Prod.fst ⁻¹' (V ∩ W) ∩ {p | φ.symm p ∈ F.wSrc x₀ ∧
        F.wTot x₀ (φ.symm p) ∈ rf4_innerDisc (D.deg x₀) D.r (F.ε p.1 x₀)}) ∧
      ∀ (t : V) (y : b63l_parameterFibre b C V hV t), t.val ∈ W → y.val ∈ φ.source →
        y ∈ ((F.S t).w x₀).source →
        (F.S t).w x₀ y ∈ rf4_innerDisc (D.deg x₀) D.r (F.ε t x₀) →
        ∀ v : TangentSpace 𝓘(ℂ, ℂ) y,
          rf5_sectorForm (F.S t) (e t.val) x₀ ⟨y, v⟩ = a (φ y.val) * (show ℂ from
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
              (fun z : b63l_parameterFibre b C V hV t ↦ (φ z.val).2) y v) := by
  set Wφ := F.wTot x₀ ∘ φ.symm with hWφ
  have hWan := rf5_chart_analyticOnNhd hφ (F.wSrc_open x₀) (F.w_analytic x₀)
  refine ⟨fun p ↦ rf4_sectorCoeff (D.deg x₀) (fun j ↦ rf4_extendBdd ((e p.1).2 x₀ j))
      (D.c x₀ + F.ε p.1 x₀) (Wφ p) * fderiv ℂ Wφ p ((0 : Fin 10 → ℂ), (1 : ℂ)), ?_, ?_⟩
  · rintro p ⟨⟨hpt, hpV, hpW⟩, hpS, hpD⟩
    refine AnalyticAt.analyticWithinAt ?_
    have hWp : AnalyticAt ℂ Wφ p := hWan p ⟨hpt, hpS⟩
    have hεp : AnalyticAt ℂ (fun q : (Fin 10 → ℂ) × ℂ ↦ F.ε q.1 x₀) p :=
      ((ContinuousLinearMap.proj x₀ : (Fin D.m → ℂ) →L[ℂ] ℂ).analyticAt _).comp
        ((F.ε_analytic p.1 hpV).comp analyticAt_fst)
    refine AnalyticAt.mul ?_ (rf5_vertical_analyticAt hWp)
    unfold rf4_sectorCoeff
    refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun j _ ↦ (hWp.pow _).mul ?_)
    have he' : AnalyticOnNhd ℂ (fun s ↦ (e s).2 x₀ j) W := fun s hs ↦
      (((ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.proj x₀).comp
        (ContinuousLinearMap.snd ℂ (rf2_bddForm D.P) (rf4_Disc D)))).analyticAt _).comp (he s hs)
    have hball : D.c x₀ + F.ε p.1 x₀ + Wφ p ^ D.deg x₀ ∈ Metric.ball (D.c x₀) (2 * D.r) := by
      rw [Metric.mem_ball, dist_eq_norm]
      have : D.c x₀ + F.ε p.1 x₀ + Wφ p ^ D.deg x₀ - D.c x₀ = Wφ p ^ D.deg x₀ + F.ε p.1 x₀ := by
        ring
      rw [this]
      exact hpD
    have hpair : AnalyticAt ℂ
        (fun q : (Fin 10 → ℂ) × ℂ ↦ (q.1, D.c x₀ + F.ε q.1 x₀ + Wφ q ^ D.deg x₀)) p :=
      analyticAt_fst.prod ((analyticAt_const.add hεp).add (hWp.pow _))
    exact (rf5_extendBdd_analyticAt Metric.isOpen_ball hW he' hpW hball).comp_of_eq hpair rfl
  · intro t y ht hy hyw hyD v
    have hys : y.val ∈ F.wSrc x₀ := (F.w_source t x₀ y).mp hyw
    have hfst := rf5_fibre_fst hp y hy
    have hd := rf5_fibre_mfderiv t (hincl t) hφ hp hy
      (hWan (φ y.val) ⟨φ.map_source hy, by rw [Set.mem_preimage, φ.left_inv hy]; exact hys⟩)
      (g := (F.S t).w x₀)
      (Filter.eventually_of_mem (((F.S t).w x₀).open_source.mem_nhds hyw)
        fun z hz ↦ F.w_eq t x₀ z hz) v
    have hwy : (F.S t).w x₀ y = Wφ (φ y.val) := by
      rw [F.w_eq t x₀ y hyw, hWφ, Function.comp_apply, φ.left_inv hy]
    change rf4_sectorCoeff (D.deg x₀) (fun j ↦ rf4_extendBdd ((e t.val).2 x₀ j))
        (D.c x₀ + F.ε t x₀) ((F.S t).w x₀ y) *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ((F.S t).w x₀) y v) = _
    rw [hd, hwy]
    beta_reduce
    rw [hfst, hWφ, mul_assoc]


theorem rf5_glue_eq_sector_aux {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (k : rf4_Src D) (hk : k ∈ (rf4_delta D ε).ker) (x : Fin D.m)
    (y : X) (hy : y ∈ (S.w x).source) (hyD : S.w x y ∈ rf4_innerDisc (D.deg x) D.r (ε x))
    (v : TangentSpace 𝓘(ℂ, ℂ) y) :
    rf4_glue S k ⟨y, v⟩ = rf5_sectorForm S k x ⟨y, v⟩ := by
  classical
  have hyw : y ∈ (S.w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x) :=
    ⟨S.w x y, hyD, (S.w x).left_inv hy⟩
  by_cases hO : ∃ i, S.h.symm y ∈ (D.P.chart i).source ∧
      D.P.chart i (S.h.symm y) ∈ D.P.piece i
  · have hyO : y ∈ S.h '' O := by
      obtain ⟨i, hi, hi'⟩ := hO
      refine ⟨S.h.symm y, ?_, S.h.apply_symm_apply y⟩
      exact (Set.ext_iff.mp D.P.covers _).mpr
        (mem_iUnion.mpr ⟨i, _, hi', (D.P.chart i).left_inv hi⟩)
    have hyA : y ∈ S.h '' ((D.P.chart (D.ann x)).symm '' b63r_annulus (D.deg x) D.r) := by
      rw [← S.overlap x]; exact ⟨hyO, hyw⟩
    obtain ⟨_, ⟨u, hu, rfl⟩, hyu⟩ := hyA
    have hut : u ∈ (D.P.chart (D.ann x)).target :=
      D.P.contained (D.ann x) (subset_closure (by rw [D.hann x]; exact hu))
    have hp : S.h.symm y = (D.P.chart (D.ann x)).symm u := by
      rw [← hyu, S.h.symm_apply_apply]
    have hpa : S.h.symm y ∈ (D.P.chart (D.ann x)).source := hp ▸ (D.P.chart (D.ann x)).map_target hut
    have hpa' : D.P.chart (D.ann x) (S.h.symm y) = u := by rw [hp, (D.P.chart (D.ann x)).right_inv hut]
    have hpp : D.P.chart (D.ann x) (S.h.symm y) ∈ D.P.piece (D.ann x) := by
      rw [hpa', D.hann x]; exact hu
    have hε := S.small x
    simp only [rf4_glue, hO, ↓reduceDIte]
    rw [rf5_outer_compat S k.1 y _ (D.ann x) (Classical.choose_spec hO).1
      (Classical.choose_spec hO).2 hpa hpp v, hpa', rf5_kernel_coeff k hk x hε hu]
    -- the sector side
    have hwy : S.w x y = rf4_rootMap (D.deg x) (ε x) u := by
      rw [← hyu]; exact (S.glue x u hu).2
    have hfa : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (fun p : X ↦ D.P.chart (D.ann x) (S.h.symm p)) y :=
      rf5_mdifferentiableAt_chart (S.stationary (D.ann x)) (by simpa using hpa)
    have hder := rf5_rootMap_hasDerivAt (D.hdeg x) D.hr hε hu
    have hev : (S.w x : X → ℂ) =ᶠ[𝓝 y]
        rf4_rootMap (D.deg x) (ε x) ∘ (fun p : X ↦ D.P.chart (D.ann x) (S.h.symm p)) := by
      have hN : IsOpen ((D.P.chart (D.ann x)).source ∩
          D.P.chart (D.ann x) ⁻¹' b63r_annulus (D.deg x) D.r) :=
        (D.P.chart (D.ann x)).isOpen_inter_preimage (rf4_annulus_isOpen _ _)
      filter_upwards [S.h.symm.continuous.continuousAt.preimage_mem_nhds
        (hN.mem_nhds ⟨hpa, by rw [Set.mem_preimage, hpa']; exact hu⟩)] with q hq
      have h1 := (S.glue x _ hq.2).2
      rw [(D.P.chart (D.ann x)).left_inv hq.1, S.h.apply_symm_apply] at h1
      exact h1
    rw [rf5_sectorForm]
    change _ = rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (k.2 x j)) (D.c x + ε x)
      (S.w x y) * (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w x : X → ℂ) y v)
    rw [rf5_mfderiv_comp_apply hfa (by rw [hpa']; exact hder.differentiableAt) hev v, hpa', hwy,
      rf4_sectorCoeff, rf5_rootMap_pow (D.hdeg x) D.hr hu, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← rf5_rootMap_pow_mul_deriv (D.hdeg x) D.hr hε hu j]
    have : D.c x + ε x + (u ^ D.deg x - ε x) = D.c x + u ^ D.deg x := by ring
    rw [this]
    ring
  · have hD : ∃ x', y ∈ (S.w x').source ∧ S.w x' y ∈ rf4_innerDisc (D.deg x') D.r (ε x') :=
      ⟨x, hy, hyD⟩
    have hx : Classical.choose hD = x := by
      by_contra hne
      have hs := Classical.choose_spec hD
      exact (S.disjoint hne).ne_of_mem ⟨_, hs.2, (S.w _).left_inv hs.1⟩ hyw rfl
    simp only [rf4_glue, hO, hD, ↓reduceDIte]
    have key : ∀ x', x' = x →
        rf4_sectorCoeff (D.deg x') (fun j ↦ rf4_extendBdd (k.2 x' j)) (D.c x' + ε x')
          (S.w x' y) * (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w x') y v) =
        rf5_sectorForm S k x ⟨y, v⟩ := by
      rintro _ rfl; rfl
    exact key _ hx


theorem rf5_relForm_of_kernel_aux {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {V : Set (Fin 10 → ℂ)} {hV : V ⊆ b6t_polydisc b}
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (F : rf5_FamilyPlumbing b C D V hV) (W : Set (Fin 10 → ℂ)) (hW : IsOpen W)
    (e : (Fin 10 → ℂ) → rf4_Src D) (he : AnalyticOnNhd ℂ e W)
    (hk : ∀ t : V, t.val ∈ W → e t.val ∈ (rf4_delta D (F.ε t)).ker) :
    rf5_relGlue F W e ∈ b63e_relForm b C V hV W := by
  classical
  have hh : ∀ (t : V) (z : b63l_parameterFibre b C V hV t), (F.S t).h.symm z = z.val.2 := by
    intro t z; rw [F.h_eq t]; rfl
  refine ⟨fun t ↦ ?_, fun φ hφ hp ↦ ?_⟩
  · by_cases ht : t.val ∈ W
    · obtain ⟨E, hE⟩ := rf4_kernel_equiv (F.S t)
      have h := hE ⟨e t.val, hk t ht⟩
      simp only [rf5_relGlue, ht, ↓reduceIte]
      rw [← h]
      exact (E _).property
    · simp only [rf5_relGlue, ht, ↓reduceIte]
      exact (b3_HolForm ℂ _).zero_mem
  obtain ⟨a1, ha1an, ha1⟩ := rf5_outer_chart_analytic_aux hincl F W hW e he φ hφ hp
  choose a2 ha2an ha2 using fun x₀ ↦ rf5_sector_chart_analytic_aux hincl F W hW e he φ hφ hp x₀
  let inner : Fin D.m → (Fin 10 → ℂ) × ℂ → Prop := fun x p ↦
    φ.symm p ∈ F.wSrc x ∧ F.wTot x (φ.symm p) ∈ rf4_innerDisc (D.deg x) D.r (F.ε p.1 x)
  let a : (Fin 10 → ℂ) × ℂ → ℂ := fun p ↦
    if (φ.symm p).2 ∈ O then a1 p else if h : ∃ x, inner x p then a2 (Classical.choose h) p else 0
  -- the vertical coordinate has nonvanishing differential on every fibre
  have hnz : ∀ (t : V) (y : b63l_parameterFibre b C V hV t), y.val ∈ φ.source →
      (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (fun z : b63l_parameterFibre b C V hV t ↦ (φ z.val).2) y (1 : ℂ)) ≠ 0 := by
    intro t y hy h0
    rcases (F.S t).cover y with hO | ⟨x, z, hz, hzy⟩
    · rw [hh] at hO
      obtain ⟨i, w, hw, hwq⟩ := mem_iUnion.mp ((Set.ext_iff.mp D.P.covers _).mp hO)
      have hwt : w ∈ (D.P.chart i).target := D.P.contained i (subset_closure hw)
      have hi : y.val.2 ∈ (D.P.chart i).source := hwq ▸ (D.P.chart i).map_target hwt
      have hA : IsOpen (Prod.snd ⁻¹' (D.P.chart i).source : Set (b6t_polydisc b × C)) :=
        (D.P.chart i).open_source.preimage continuous_snd
      have hd := rf5_fibre_mfderiv t (hincl t) hφ hp hy
        (G := fun q : b6t_polydisc b × C ↦ D.P.chart i q.2)
        (rf5_chart_analyticOnNhd hφ hA (F.outer_analytic i) (φ y.val)
          ⟨φ.map_source hy, by simp only [Set.mem_preimage, φ.left_inv hy]; exact hi⟩)
        (g := ((F.S t).h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i : _ → ℂ))
        (Filter.Eventually.of_forall fun z ↦ by
          simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
            Homeomorph.toOpenPartialHomeomorph_apply, hh]) (1 : ℂ)
      refine rf5_mfderiv_atlas_ne_zero ((F.S t).stationary i) (y := y)
        (by simpa [hh] using hi) ?_
      rw [hd, h0, mul_zero]
    · have hzt := (F.S t).w_target x (subset_closure hz)
      have hyw : y ∈ ((F.S t).w x).source := hzy ▸ ((F.S t).w x).map_target hzt
      have hd := rf5_fibre_mfderiv t (hincl t) hφ hp hy (G := F.wTot x)
        (rf5_chart_analyticOnNhd hφ (F.wSrc_open x) (F.w_analytic x) (φ y.val)
          ⟨φ.map_source hy, by
            rw [Set.mem_preimage, φ.left_inv hy]; exact (F.w_source t x y).mp hyw⟩)
        (g := (F.S t).w x)
        (Filter.eventually_of_mem (((F.S t).w x).open_source.mem_nhds hyw)
          fun z hz ↦ F.w_eq t x z hz) (1 : ℂ)
      refine rf5_mfderiv_atlas_ne_zero ((F.S t).w_mem x) hyw ?_
      rw [hd, h0, mul_zero]
  -- the glued form in the chart
  have hid : ∀ (t : V) (y : b63l_parameterFibre b C V hV t), t.val ∈ W → y.val ∈ φ.source →
      ∀ v : TangentSpace 𝓘(ℂ, ℂ) y, rf4_glue (F.S t) (e t.val) ⟨y, v⟩ = a (φ y.val) *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (fun z : b63l_parameterFibre b C V hV t ↦ (φ z.val).2) y v) := by
    intro t y ht hy v
    have hfst := rf5_fibre_fst hp y hy
    by_cases hO : y.val.2 ∈ O
    · have : (φ.symm (φ y.val)).2 ∈ O := by rw [φ.left_inv hy]; exact hO
      simp only [a, this, ↓reduceIte]
      exact ha1 t y ht hy hO v
    · have hO' : ¬ (φ.symm (φ y.val)).2 ∈ O := by rw [φ.left_inv hy]; exact hO
      have hin : ∃ x, inner x (φ y.val) := by
        rcases (F.S t).cover y with hO2 | ⟨x, z, hz, hzy⟩
        · rw [hh] at hO2; exact absurd hO2 hO
        · have hzt := (F.S t).w_target x (subset_closure hz)
          have hyw : y ∈ ((F.S t).w x).source := hzy ▸ ((F.S t).w x).map_target hzt
          refine ⟨x, ?_, ?_⟩
          · rw [φ.left_inv hy]; exact (F.w_source t x y).mp hyw
          · rw [φ.left_inv hy, hfst, ← F.w_eq t x y hyw, ← hzy, ((F.S t).w x).right_inv hzt]
            exact hz
      simp only [a, hO', hin, ↓reduceIte, ↓reduceDIte]
      have hc := Classical.choose_spec hin
      set x := Classical.choose hin
      have hyw : y ∈ ((F.S t).w x).source := by
        rw [F.w_source t x y]; have := hc.1; rwa [φ.left_inv hy] at this
      have hyD : (F.S t).w x y ∈ rf4_innerDisc (D.deg x) D.r (F.ε t x) := by
        rw [F.w_eq t x y hyw]; have := hc.2; rwa [φ.left_inv hy, hfst] at this
      rw [rf5_glue_eq_sector_aux (F.S t) (e t.val) (hk t ht) x y hyw hyD v]
      exact ha2 x t y ht hy hyw hyD v
  -- fibre points of chart points
  have hfib : ∀ p : (Fin 10 → ℂ) × ℂ, p ∈ φ.target → ∀ hpV : p.1 ∈ V,
      (φ.symm p).1 = ⟨p.1, hV hpV⟩ := by
    intro p hpt hpV
    apply Subtype.ext
    rw [← hp _ (φ.map_target hpt), φ.right_inv hpt]
  refine ⟨a, fun p₀ hp₀ ↦ ?_, fun t y ht hy v ↦ ?_⟩
  · obtain ⟨hpt, hpV, hpW⟩ := hp₀
    by_cases hO0 : (φ.symm p₀).2 ∈ O
    · obtain ⟨i, w, hw, hwq⟩ := mem_iUnion.mp ((Set.ext_iff.mp D.P.covers _).mp hO0)
      have hwt : w ∈ (D.P.chart i).target := D.P.contained i (subset_closure hw)
      have hN : IsOpen (φ.target ∩ φ.symm ⁻¹' (Prod.snd ⁻¹' ((D.P.chart i).source ∩
          D.P.chart i ⁻¹' D.P.piece i))) :=
        φ.isOpen_inter_preimage_symm (((D.P.chart i).isOpen_inter_preimage
          (D.P.isOpen i)).preimage continuous_snd)
      have hp₀N : p₀ ∈ φ.target ∩ φ.symm ⁻¹' (Prod.snd ⁻¹' ((D.P.chart i).source ∩
          D.P.chart i ⁻¹' D.P.piece i)) := by
        refine ⟨hpt, hwq ▸ (D.P.chart i).map_target hwt, ?_⟩
        simp only [Set.mem_preimage]
        rw [← hwq, (D.P.chart i).right_inv hwt]; exact hw
      have hNO : ∀ q ∈ φ.target ∩ φ.symm ⁻¹' (Prod.snd ⁻¹' ((D.P.chart i).source ∩
          D.P.chart i ⁻¹' D.P.piece i)), (φ.symm q).2 ∈ O := by
        intro q hq
        exact (Set.ext_iff.mp D.P.covers _).mpr (mem_iUnion.mpr
          ⟨i, _, hq.2.2, (D.P.chart i).left_inv hq.2.1⟩)
      have hmem : φ.target ∩ Prod.fst ⁻¹' (V ∩ W) ∩ φ.symm ⁻¹' {q | q.2 ∈ O} ∈
          𝓝[φ.target ∩ Prod.fst ⁻¹' (V ∩ W)] p₀ :=
        mem_nhdsWithin.mpr ⟨_, hN, hp₀N, fun q hq ↦ ⟨hq.2, hNO q hq.1⟩⟩
      refine ((ha1an p₀ ⟨⟨hpt, hpV, hpW⟩, hO0⟩).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq
        ?_ (by simp only [a, hO0, ↓reduceIte])
      filter_upwards [nhdsWithin_le_nhds (hN.mem_nhds hp₀N)] with q hq
      simp only [a, hNO q hq, ↓reduceIte]
    · let t₀ : V := ⟨p₀.1, hpV⟩
      let y₀ : b63l_parameterFibre b C V hV t₀ := ⟨φ.symm p₀, hfib p₀ hpt hpV⟩
      obtain ⟨x, hxin⟩ : ∃ x, inner x p₀ := by
        rcases (F.S t₀).cover y₀ with hO2 | ⟨x, z, hz, hzy⟩
        · rw [hh] at hO2; exact absurd hO2 hO0
        · have hzt := (F.S t₀).w_target x (subset_closure hz)
          have hyw : y₀ ∈ ((F.S t₀).w x).source := hzy ▸ ((F.S t₀).w x).map_target hzt
          refine ⟨x, (F.w_source t₀ x y₀).mp hyw, ?_⟩
          change F.wTot x y₀.val ∈ rf4_innerDisc (D.deg x) D.r (F.ε t₀ x)
          rw [← F.w_eq t₀ x y₀ hyw, ← hzy, ((F.S t₀).w x).right_inv hzt]
          exact hz
      have hWan := rf5_chart_analyticOnNhd hφ (F.wSrc_open x) (F.w_analytic x)
      have hU : IsOpen (φ.target ∩ φ.symm ⁻¹' F.wSrc x) :=
        φ.isOpen_inter_preimage_symm (F.wSrc_open x)
      have hcont : ContinuousAt (fun q : (Fin 10 → ℂ) × ℂ ↦
          ‖(F.wTot x ∘ φ.symm) q ^ D.deg x + F.ε q.1 x‖) p₀ :=
        (((hWan p₀ ⟨hpt, hxin.1⟩).continuousAt.pow _).add
          ((continuous_apply x).continuousAt.comp
            ((F.ε_analytic p₀.1 hpV).continuousAt.comp continuous_fst.continuousAt))).norm
      have hev : ∀ᶠ q in 𝓝 p₀, q ∈ φ.target ∩ φ.symm ⁻¹' F.wSrc x ∧
          ‖(F.wTot x ∘ φ.symm) q ^ D.deg x + F.ε q.1 x‖ < 2 * D.r :=
        Filter.Eventually.and (show ∀ᶠ q in 𝓝 p₀, q ∈ φ.target ∩ φ.symm ⁻¹' F.wSrc x from
          hU.mem_nhds ⟨hpt, hxin.1⟩) (hcont.preimage_mem_nhds (isOpen_Iio.mem_nhds hxin.2))
      -- on chart points of the fibres near `p₀`, `a` agrees with the sector coefficient
      have hagree : ∀ q, q ∈ φ.target → ∀ hqV : q.1 ∈ V, q.1 ∈ W → inner x q → a q = a2 x q := by
        intro q hqt hqV hqW hqx
        let t : V := ⟨q.1, hqV⟩
        let y : b63l_parameterFibre b C V hV t := ⟨φ.symm q, hfib q hqt hqV⟩
        have hy : y.val ∈ φ.source := φ.map_target hqt
        have hyw : y ∈ ((F.S t).w x).source := (F.w_source t x y).mpr hqx.1
        have hyD : (F.S t).w x y ∈ rf4_innerDisc (D.deg x) D.r (F.ε t x) := by
          rw [F.w_eq t x y hyw]; exact hqx.2
        have h1 := hid t y hqW hy (1 : ℂ)
        rw [rf5_glue_eq_sector_aux (F.S t) (e t.val) (hk t hqW) x y hyw hyD (1 : ℂ),
          ha2 x t y hqW hy hyw hyD (1 : ℂ)] at h1
        have h2 := mul_right_cancel₀ (hnz t y hy) h1
        change a2 x (φ (φ.symm q)) = a (φ (φ.symm q)) at h2
        rw [φ.right_inv hqt] at h2
        exact h2.symm
      have hmem : φ.target ∩ Prod.fst ⁻¹' (V ∩ W) ∩ {p | φ.symm p ∈ F.wSrc x ∧
          F.wTot x (φ.symm p) ∈ rf4_innerDisc (D.deg x) D.r (F.ε p.1 x)} ∈
          𝓝[φ.target ∩ Prod.fst ⁻¹' (V ∩ W)] p₀ := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hev] with q hq hq'
        exact ⟨hq, hq'.1.2, hq'.2⟩
      refine ((ha2an x p₀ ⟨⟨hpt, hpV, hpW⟩, hxin⟩).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq
        ?_ (hagree p₀ hpt hpV hpW hxin)
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hev] with q hq hq'
      exact hagree q hq.1 hq.2.1 hq.2.2 ⟨hq'.1.2, hq'.2⟩
  · simp only [rf5_relGlue, ht, ↓reduceIte]
    exact hid t y ht hy v


theorem rf5_relForm_extend_aux {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {V : Set (Fin 10 → ℂ)} {hV : V ⊆ b6t_polydisc b} (hVo : IsOpen V)
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (F : rf5_FamilyPlumbing b C D V hV) (t₀ : V)
    (η : b3_HolForm ℂ (b63l_parameterFibre b C V hV t₀)) :
    ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ V ∧
      ∃ θ : b63e_relForm b C V hV W, b63e_relFormAt b C V hV θ t₀ = η := by
  classical
  let T : (Fin 10 → ℂ) → rf4_Src D →L[ℂ] rf4_Tgt D := fun t ↦ rf4_delta D (F.ε t)
  have hT : AnalyticOnNhd ℂ T V := fun t ht ↦
    (rf4_delta_analytic D (F.ε t) ((F.S ⟨t, ht⟩).small)).comp (F.ε_analytic t ht)
  have hd : ∀ t ∈ V, Module.finrank ℂ (T t).ker =
      Module.finrank ℂ (b3_HolForm ℂ (b63l_parameterFibre b C V hV t₀)) := by
    intro t ht
    rw [(rf4_ker_finrank (F.S ⟨t, ht⟩)).2]
    exact b63e_holForm_finrank_homeomorph _ _
      (b6m_transport b C ⟨t, hV ht⟩ ⟨t₀.val, hV t₀.property⟩)
  obtain ⟨W, hW, htW, hWV, f, hf, hfr⟩ :=
    b63r_analytic_kernel_frame V hVo T hT t₀.val t₀.property (rf4_delta_isFredholm (F.S t₀)) hd
  obtain ⟨E, hE⟩ := rf4_kernel_equiv (F.S t₀)
  have hk₀ : ((E.symm η : (rf4_delta D (F.ε t₀)).ker) : rf4_Src D) ∈
      Submodule.span ℂ (Set.range fun i ↦ f i t₀.val) := by
    rw [(hfr t₀.val htW).2]
    exact (E.symm η).property
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.mp hk₀
  let e : (Fin 10 → ℂ) → rf4_Src D := fun t ↦ ∑ i, c i • f i t
  have he : AnalyticOnNhd ℂ e W := fun t ht ↦ by
    exact Finset.analyticAt_fun_sum _ fun i _ ↦ (analyticAt_const (v := c i)).smul (hf i t ht)
  have hk : ∀ t : V, t.val ∈ W → e t.val ∈ (rf4_delta D (F.ε t)).ker := by
    intro t ht
    have : e t.val ∈ Submodule.span ℂ (Set.range fun i ↦ f i t.val) :=
      Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [(hfr t.val ht).2] at this
    exact this
  refine ⟨W, hW, htW, hWV,
    ⟨rf5_relGlue F W e, rf5_relForm_of_kernel_aux hincl F W hW e he hk⟩, ?_⟩
  apply Subtype.ext
  change rf5_relGlue F W e t₀ = (η : TangentBundle 𝓘(ℂ, ℂ) _ → ℂ)
  have hη : (η : TangentBundle 𝓘(ℂ, ℂ) _ → ℂ) = rf4_glue (F.S t₀) (E.symm η) := by
    rw [← hE, E.apply_symm_apply]
  simp only [hη, rf5_relGlue, htW, ↓reduceIte]
  exact congrArg _ hc

end HodgeLean.Foundations.Program
