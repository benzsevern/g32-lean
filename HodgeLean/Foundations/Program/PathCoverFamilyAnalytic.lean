import HodgeLean.Foundations.Program.PathCoverFamilyRanks

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

theorem b65z_disc_root {b : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (R : b65z_SharedFamily b g) {O : Set R.C} (D : rf4_OuterData R.C O)
    (k : Fin D.m) (i : Fin 10) (x : R.C)
    (hx : R.atlas.f x = ((b i : ℂ) : OnePoint ℂ)) (hc : D.c k = b i)
    (hdeg : D.deg k = R.atlas.n x) (hDr : D.r = rf7_radius b)
    (hsrc : (D.P.chart (D.ann k)).source ⊆
      rf7_component R.atlas.f (b i) (3 * b6t_radius b) x)
    (hform : ∀ y ∈ (D.P.chart (D.ann k)).source,
      R.atlas.f y = ((D.c k + D.P.chart (D.ann k) y ^ D.deg k : ℂ) : OnePoint ℂ)) :
    ∃ (ζ : ℂ) (w : b6t_polydisc b × R.C → ℂ), ζ ^ D.deg k = 1 ∧
      ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω w
        (univ ×ˢ rf7_component R.atlas.f (b i) (3 * b6t_radius b) x) ∧
      ∀ t : b6t_polydisc b,
        InjOn (fun y ↦ w (t, y)) (rf7_component R.atlas.f (b i) (3 * b6t_radius b) x) ∧
        (fun y ↦ w (t, y)) '' rf7_component R.atlas.f (b i) (3 * b6t_radius b) x =
          {v : ℂ | ‖v ^ D.deg k + (t.val i - b i)‖ < 3 * b6t_radius b} ∧
        (fun y ↦ w (t, y)) '' rf7_inner b R.atlas.f i x =
          rf4_innerDisc (D.deg k) D.r (t.val i - b i) ∧
        ∀ u ∈ b63r_annulus (D.deg k) D.r,
          ζ * w (t, (D.P.chart (D.ann k)).symm u) = rf4_rootMap (D.deg k) (t.val i - b i) u := by
  obtain ⟨w, hw, hwt⟩ := rf7_moving_root R.atlas i x hx
  have hn := R.atlas.hn x
  have hA : b63r_annulus (D.deg k) D.r ⊆ (D.P.chart (D.ann k)).target := by
    rw [← D.hann k]
    exact subset_closure.trans (D.P.contained _)
  let t₀ : b6t_polydisc b := ⟨b, (b6t_polydisc_neighbourhood b R.atlas.hb).1⟩
  let φ := D.P.chart (D.ann k)
  have hYc : ConnectedSpace (b63r_annulus (D.deg k) D.r) :=
    isConnected_iff_connectedSpace.mp (rf8_annulus_isConnected (D.hdeg k) D.hr)
  have hmemK : ∀ a ∈ b63r_annulus (D.deg k) D.r,
      φ.symm a ∈ rf7_component R.atlas.f (b i) (3 * b6t_radius b) x :=
    fun a ha ↦ hsrc (φ.map_target (hA ha))
  have hcont : Continuous (fun a : b63r_annulus (D.deg k) D.r ↦ w (t₀, φ.symm a)) := by
    refine hw.continuousOn.comp_continuous ?_ (fun a ↦ ⟨mem_univ _, hmemK a a.2⟩)
    exact continuous_const.prodMk
      (φ.continuousOn_symm.comp_continuous continuous_subtype_val (fun a ↦ hA a.2))
  have hpowA : ∀ a ∈ b63r_annulus (D.deg k) D.r, a ^ D.deg k = w (t₀, φ.symm a) ^ D.deg k := by
    intro a ha
    have h1 := hform (φ.symm a) (φ.map_target (hA ha))
    rw [φ.right_inv (hA ha), hc] at h1
    have h2 := ((hwt t₀).1 (φ.symm a) (hmemK a ha))
    have h3 : b6a_map b R.atlas.f (t₀, φ.symm a) = R.atlas.f (φ.symm a) := by
      change b6t_sphere b b _ = _
      rw [b6t_identity]; rfl
    rw [h3, h1] at h2
    have h4 := OnePoint.coe_injective h2
    change b i + a ^ D.deg k = b i + w (t₀, φ.symm a) ^ R.atlas.n x at h4
    rw [← hdeg] at h4
    exact add_left_cancel h4
  have hane : ∀ a ∈ b63r_annulus (D.deg k) D.r, a ≠ 0 := by
    intro a ha h
    have := ha.1
    rw [h, norm_zero, zero_pow (by have := D.hdeg k; omega)] at this
    linarith [D.hr]
  obtain ⟨ζ, hζ, hal⟩ := rf8_root_alignment_aux (D.deg k) (by have := D.hdeg k; omega)
    (fun a : b63r_annulus (D.deg k) D.r ↦ (a : ℂ)) (fun a ↦ w (t₀, φ.symm a))
    continuous_subtype_val hcont
    (fun a h ↦ hane a a.2 (pow_eq_zero_iff (by have := D.hdeg k; omega) |>.mp
      ((hpowA a a.2).trans (by rw [h, zero_pow (by have := D.hdeg k; omega)]))))
    (fun a ↦ hpowA a a.2)
  refine ⟨ζ, w, hζ, hw, fun t ↦ ?_⟩
  obtain ⟨-, hinj, himg, hinner, -, hcol⟩ := hwt t
  rw [hdeg, hDr]
  refine ⟨hinj, himg, hinner, fun u hu ↦ ?_⟩
  rw [← hdeg, ← hDr] at hu
  have hy := hmemK u hu
  have h1 := hform (φ.symm u) (φ.map_target (hA hu))
  rw [φ.right_inv (hA hu), hc] at h1
  have hr0 : 0 < b6t_radius b := (b6t_discs b R.atlas.hb).1
  have hcl := hcol (φ.symm u) hy (b i + u ^ D.deg k) h1 (by
    rw [dist_eq_norm, add_sub_cancel_left, norm_pow]
    have := hu.1
    rw [hDr] at this
    have := (rf7_radius_bounds b R.atlas.hb).1
    linarith)
  have hal' := hal ⟨u, hu⟩
  change u = ζ * w (t₀, φ.symm u) at hal'
  change ζ * w (t, φ.symm u) = _
  rw [hcl, ← rf8_principal_equivariance_aux _ hn _ _ _ (hdeg ▸ hζ), ← hal']

theorem b65z_family_plumbing {b : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (R : b65z_SharedFamily b g) :
    ∃ (D : rf4_OuterData R.C (rf7_outer b R.atlas.f))
      (e : Fin D.m ≃ {x : R.C // ∃ i : Fin 10,
        R.atlas.f x = ((b i : ℂ) : OnePoint ℂ)})
      (idx : Fin D.m → Fin 10)
      (F : rf5_FamilyPlumbing b R.C D (b6t_polydisc b) (Subset.refl _)),
      D.r = rf7_radius b ∧
      (∀ k, R.atlas.f (e k).val = ((b (idx k) : ℂ) : OnePoint ℂ) ∧
        D.c k = b (idx k) ∧ D.deg k = R.atlas.n (e k).val) ∧
      (∀ t k, F.ε t k = t (idx k) - b (idx k)) ∧
      (∀ k, F.wSrc k = univ ×ˢ
        rf7_component R.atlas.f (b (idx k)) (3 * b6t_radius b) (e k).val) ∧
      ∀ (t : b6t_polydisc b) k,
        ((F.S t).w k).source = {y | y.val.2 ∈
          rf7_component R.atlas.f (b (idx k)) (3 * b6t_radius b) (e k).val} := by
  classical
  obtain ⟨D, e, idx, hDr, hk, hann, -, hout⟩ := rf7_outer_data R.atlas
  obtain ⟨-, h2ρ, -, -, -, hsmall⟩ := rf7_radius_bounds b R.atlas.hb
  obtain ⟨-, -, hdisj, hcov, hOI⟩ := rf7_pieces R.atlas
  have hr0 : 0 < b6t_radius b := (b6t_discs b R.atlas.hb).1
  let K : Fin D.m → Set R.C := fun k ↦
    rf7_component R.atlas.f (b (idx k)) (3 * b6t_radius b) (e k).val
  have hKo : ∀ k, IsOpen (K k) := fun k ↦
    (rf7_component_props R.atlas (idx k) (e k).val (hk k).1).1
  have hdisc := fun k ↦ b65z_disc_root R D k (idx k) (e k).val (hk k).1 (hk k).2.1 (hk k).2.2 hDr
    (hann k).1 (hann k).2
  choose ζ w hζ hw hwt using hdisc
  have hζ0 : ∀ k, ζ k ≠ 0 := fun k h ↦ by
    have := hζ k
    rw [h, zero_pow (by have := D.hdeg k; omega)] at this
    exact zero_ne_one this
  let ε : (Fin 10 → ℂ) → Fin D.m → ℂ := fun t k ↦ t (idx k) - b (idx k)

  let W : Fin D.m → b6t_polydisc b × R.C → ℂ := fun k q ↦ ζ k * w k q
  have hW : ∀ k, ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω (W k) (univ ×ˢ K k) := fun k ↦
    ((contDiff_const.mul contDiff_id).contMDiff).comp_contMDiffOn (hw k)
  have hval : ∀ (t : b6t_polydisc b) (p : b65z_fibre b R.C t), p.val = (t, p.val.2) :=
    fun t p ↦ Prod.ext p.property rfl

  have hch : ∀ (t : b6t_polydisc b) (k : Fin D.m),
      ∃ φ : OpenPartialHomeomorph (b65z_fibre b R.C t) ℂ,
        φ.source = {p | p.val.2 ∈ K k} ∧
        φ.target = (fun p : b65z_fibre b R.C t ↦ W k p.val) '' {p | p.val.2 ∈ K k} ∧
        (∀ p ∈ {p : b65z_fibre b R.C t | p.val.2 ∈ K k}, φ p = W k p.val) ∧
        φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω (b65z_fibre b R.C t) := by
    intro t k
    refine rf8_chart_of_injOn (X := b65z_fibre b R.C t) {p | p.val.2 ∈ K k}
      ((hKo k).preimage (b6m_coordinate b R.C t).continuous) _ ?_ ?_
    · exact (hW k).comp (R.hincl t).contMDiffOn (fun p hp ↦ ⟨mem_univ _, hp⟩)
    · intro p hp p' hp' h
      have h1 : w k (t, p.val.2) = w k (t, p'.val.2) := by
        have := mul_left_cancel₀ (hζ0 k) h
        rwa [hval t p, hval t p'] at this
      have h2 := ((hwt k t).1 hp hp' h1)
      exact (b6m_coordinate b R.C t).injective h2
  choose φ hφs hφt hφe hφm using hch
  have hA : ∀ k, b63r_annulus (D.deg k) D.r ⊆ (D.P.chart (D.ann k)).target := fun k ↦ by
    rw [← D.hann k]
    exact subset_closure.trans (D.P.contained _)

  have hstat : ∀ (t : b6t_polydisc b) (j : Fin D.P.n),
      (b6m_coordinate b R.C t).toOpenPartialHomeomorph ≫ₕ D.P.chart j ∈
        IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω (b65z_fibre b R.C t) := by
    intro t j
    obtain ⟨ψ, hψs, -, hψe, hψm⟩ := rf8_chart_of_injOn (X := b65z_fibre b R.C t)
      {p | p.val.2 ∈ (D.P.chart j).source}
      ((D.P.chart j).open_source.preimage (b6m_coordinate b R.C t).continuous)
      (fun p ↦ D.P.chart j p.val.2)
      ((hout j).comp (R.hincl t).contMDiffOn (fun p hp ↦ hp))
      (fun p hp p' hp' h ↦ (b6m_coordinate b R.C t).injective
        ((D.P.chart j).injOn hp hp' h))
    refine StructureGroupoid.mem_maximalAtlas_of_eqOnSource
      (G := contDiffGroupoid ω 𝓘(ℂ, ℂ)) ⟨?_, ?_⟩ hψm
    · rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
        univ_inter, hψs]
      rfl
    · intro p hp
      rw [hψe p (by
        rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
          univ_inter] at hp
        exact hp)]
      rfl

  have hInner : ∀ (t : b6t_polydisc b) (k : Fin D.m),
      (φ t k).symm '' rf4_innerDisc (D.deg k) D.r (ε t.val k) =
        {p | p.val.2 ∈ rf7_inner b R.atlas.f (idx k) (e k).val} := by
    intro t k
    obtain ⟨-, -, hinner, -⟩ := hwt k t
    ext p
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : (ζ k)⁻¹ * v ∈ rf4_innerDisc (D.deg k) D.r (ε t.val k) :=
        (rf8_innerDisc_rot (by rw [inv_pow, hζ k, inv_one])).mpr hv
      rw [← hinner] at hv'
      obtain ⟨y, hy, hyv⟩ := hv'
      change w k (t, y) = _ at hyv
      have hq : (b6m_coordinate b R.C t).symm y ∈ (φ t k).source := by
        rw [hφs]; exact hy.1
      have hφq : φ t k ((b6m_coordinate b R.C t).symm y) = v := by
        rw [hφe t k _ (hφs t k ▸ hq)]
        change ζ k * w k (t, y) = v
        rw [hyv, ← mul_assoc, mul_inv_cancel₀ (hζ0 k), one_mul]
      rw [← hφq, (φ t k).left_inv hq]
      exact hy
    · intro hp
      have hq : p ∈ (φ t k).source := by rw [hφs]; exact hp.1
      refine ⟨φ t k p, ?_, (φ t k).left_inv hq⟩
      rw [hφe t k p (hφs t k ▸ hq)]
      change ζ k * w k p.val ∈ _
      rw [hval t p, rf8_innerDisc_rot (hζ k), ← hinner]
      exact ⟨_, hp, rfl⟩
  have hcoord : ∀ (t : b6t_polydisc b) (s : Set R.C),
      {p : b65z_fibre b R.C t | p.val.2 ∈ s} = (b6m_coordinate b R.C t).symm '' s :=
    fun t s ↦ (congrFun (b6m_coordinate b R.C t).image_symm s).symm
  have hwtarget : ∀ (t : b6t_polydisc b) (k : Fin D.m),
      closure (rf4_innerDisc (D.deg k) D.r (ε t.val k)) ⊆ (φ t k).target := by
    intro t k v hv
    have hle := closure_lt_subset_le (by fun_prop) continuous_const hv
    simp only [Set.mem_ofPred_eq] at hle
    rw [hφt]
    have h3 : (ζ k)⁻¹ * v ∈ {v : ℂ | ‖v ^ D.deg k + (t.val (idx k) - b (idx k))‖ <
        3 * b6t_radius b} := by
      change ‖((ζ k)⁻¹ * v) ^ D.deg k + _‖ < _
      rw [mul_pow, inv_pow, hζ k, inv_one, one_mul]
      change ‖v ^ D.deg k + ε t.val k‖ < _
      rw [hDr] at hle
      linarith
    rw [← (hwt k t).2.1] at h3
    obtain ⟨y, hy, hyv⟩ := h3
    change w k (t, y) = _ at hyv
    refine ⟨(b6m_coordinate b R.C t).symm y, hy, ?_⟩
    change ζ k * w k (t, y) = v
    rw [hyv, ← mul_assoc, mul_inv_cancel₀ (hζ0 k), one_mul]
  have hcover : ∀ (t : b6t_polydisc b) (p : b65z_fibre b R.C t),
      (b6m_coordinate b R.C t) p ∈ rf7_outer b R.atlas.f ∨
        ∃ k, p ∈ (φ t k).symm '' rf4_innerDisc (D.deg k) D.r (ε t.val k) := by
    intro t p
    rcases hcov p.val.2 with hO | ⟨i, y, hy, hin⟩
    · exact Or.inl hO
    · obtain ⟨k, hky⟩ : ∃ k, (e k).val = y := ⟨e.symm ⟨y, i, hy⟩, by rw [e.apply_symm_apply]⟩
      have h2 : R.atlas.f y = ((b (idx k) : ℂ) : OnePoint ℂ) := hky ▸ (hk k).1
      have hi : idx k = i :=
        (rf8_branch_inj R.atlas.hb (OnePoint.coe_injective (hy.symm.trans h2))).symm
      refine Or.inr ⟨k, ?_⟩
      rw [hInner]
      change p.val.2 ∈ rf7_inner b R.atlas.f (idx k) (e k).val
      rw [hi, hky]
      exact hin
  have hdisjoint : ∀ (t : b6t_polydisc b), Pairwise fun k k' : Fin D.m ↦
      Disjoint ((φ t k).symm '' rf4_innerDisc (D.deg k) D.r (ε t.val k))
        ((φ t k').symm '' rf4_innerDisc (D.deg k') D.r (ε t.val k')) := by
    intro t k k' hkk'
    rw [hInner, hInner]
    have hne : (e k).val ≠ (e k').val := fun h ↦ hkk' (e.injective (Subtype.ext h))
    exact ((hdisj _ _ _ _ (hk k).1 (hk k').1 hne).mono inter_subset_left
      inter_subset_left).preimage (b6m_coordinate b R.C t)
  have hoverlap : ∀ (t : b6t_polydisc b) (k : Fin D.m),
      (b6m_coordinate b R.C t).symm '' rf7_outer b R.atlas.f ∩
        (φ t k).symm '' rf4_innerDisc (D.deg k) D.r (ε t.val k) =
      (b6m_coordinate b R.C t).symm ''
        ((D.P.chart (D.ann k)).symm '' b63r_annulus (D.deg k) D.r) := by
    intro t k
    rw [hInner, hcoord, ← image_inter (b6m_coordinate b R.C t).symm.injective,
      hOI (idx k) (e k).val (hk k).1, ← hDr]
    congr 1
    refine rf8_collar_image R.atlas.f (K k) (D.P.chart (D.ann k)) (D.hdeg k) (b (idx k))
      D.hr (hA k) (hann k).1 (fun y hy ↦ (hk k).2.1 ▸ (hann k).2 y hy) ?_
    intro z hz1 hz2
    rw [(hk k).2.2]
    refine (rf7_component_props R.atlas (idx k) (e k).val (hk k).1).2.2.2.2.2 z ?_ ?_
    · rw [Metric.mem_ball]
      rw [hDr] at hz2
      linarith
    · rintro rfl
      rw [dist_self] at hz1
      linarith [D.hr]
  have hglue : ∀ (t : b6t_polydisc b) (k : Fin D.m), ∀ u ∈ b63r_annulus (D.deg k) D.r,
      (b6m_coordinate b R.C t).symm ((D.P.chart (D.ann k)).symm u) ∈ (φ t k).source ∧
        φ t k ((b6m_coordinate b R.C t).symm ((D.P.chart (D.ann k)).symm u)) =
          rf4_rootMap (D.deg k) (ε t.val k) u := by
    intro t k u hu
    have hs : (b6m_coordinate b R.C t).symm ((D.P.chart (D.ann k)).symm u) ∈
        (φ t k).source := by
      rw [hφs]
      exact (hann k).1 ((D.P.chart (D.ann k)).map_target (hA k hu))
    refine ⟨hs, ?_⟩
    rw [hφe t k _ (hφs t k ▸ hs)]
    exact (hwt k t).2.2.2 u hu
  let S : ∀ t : b6t_polydisc b, rf4_Plumbing D (ε t.val) (b65z_fibre b R.C t) := fun t ↦
    { h := (b6m_coordinate b R.C t).symm
      stationary := hstat t
      small := fun k ↦ hDr ▸ hsmall t.val t.property (idx k)
      w := φ t
      w_mem := hφm t
      w_target := hwtarget t
      cover := hcover t
      disjoint := hdisjoint t
      overlap := hoverlap t
      glue := hglue t }
  let F : rf5_FamilyPlumbing b R.C D (b6t_polydisc b) (Subset.refl _) :=
    { ε := ε
      ε_analytic := fun s _ ↦ AnalyticAt.pi fun k ↦ ((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 10 ↦ ℂ) (idx k)).analyticAt s).sub analyticAt_const
      S := S
      h_eq := fun t ↦ rfl
      outer_analytic := hout
      wTot := W
      wSrc := fun k ↦ univ ×ˢ K k
      wSrc_open := fun k ↦ isOpen_univ.prod (hKo k)
      w_analytic := hW
      w_source := fun t k p ↦ by
        change p ∈ (φ t k).source ↔ _
        rw [hφs]
        simp
      w_eq := fun t k p hp ↦ hφe t k p (hφs t k ▸ hp) }
  exact ⟨D, e, idx, F, hDr, hk, fun t k ↦ rfl, fun k ↦ rfl, fun t k ↦ hφs t k⟩

theorem b65z_transported_finrank {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (s t : b6t_polydisc c) :
    Module.finrank ℂ (b63e_transportedF c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t) = 6 := by
  obtain ⟨E, -, hE⟩ := b63e_lattice_period_transport c D.C D.hC (b6t_polydisc c)
    (Subset.refl _) D.hG D.P D.hP s t
  have hd := (b63d_saturated_dimensions (b65z_fibre c D.C t) (D.hG t)
    (b65z_period_multiplicities hg D t)).2.1
  let eC := E.baseChange ℤ ℂ
    (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s)
    (b63l_periodLattice (b65z_fibre c D.C t))
  rw [hE]
  change Module.finrank ℂ ↥((b63l_periodF _).comap eC.toLinearMap) = 6
  exact (Submodule.comap_equiv_self_of_inj_of_le (p := b63l_periodF _)
    eC.injective (by rw [LinearMap.range_eq_top.mpr eC.surjective]; exact le_top)).finrank_eq.trans hd


theorem b65z_period_chart {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (s : b6t_polydisc c)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((D.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) s (D.P s) (D.Q s)).baseChange ℚ x y) :
    ∀ t ∈ (b6t_polydisc c), b64c_geomPeriod c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s m t ∈ g32m_Domain ∧
      b60_F (b64c_geomPeriod c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s m t) =
        b64c_markedF _ m (b64c_transportedFamily c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s) t := by
  obtain ⟨B⟩ := b65z_lattice_basis hg D s
  have : Module.Free ℤ (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s) := Module.Free.of_basis B
  have : Module.Finite ℤ (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s) := Module.Finite.of_basis B
  have hfam (u : Fin 10 → ℂ) (hu : u ∈ (b6t_polydisc c)) :
      b64c_transportedFamily c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s u = b63e_transportedF c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s ⟨u, hu⟩ := by
    simp [b64c_transportedFamily, hu]
  have hR : ∀ u ∈ (b6t_polydisc c), b2_IsRiemannForm _ (b64c_transportedFamily c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s u)
      (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) s (D.P s) (D.Q s)) := by
    intro u hu
    rw [hfam u hu]
    exact (b63e_weight_one_riemann c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.hG D.atlas.hb D.atlas.f D.atlas.hf D.atlas.hsurj D.hk D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP s
      ⟨u, hu⟩).2
  have hdim : ∀ u ∈ (b6t_polydisc c), Module.finrank ℂ (b64c_transportedFamily c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s u) = 6 := by
    intro u hu
    rw [hfam u hu]
    exact b65z_transported_finrank hg D s ⟨u, hu⟩
  have hneg : ∀ u ∈ (b6t_polydisc c), Module.finrank ℂ ↥(b64c_transportedFamily c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s u ⊓
      Module.End.eigenspace ((D.A s).baseChange ℂ) (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
    intro u hu
    rw [hfam u hu]
    exact (b65z_period_eigen_ranks hg D s ⟨u, hu⟩).1
  have hpos : ∀ u ∈ (b6t_polydisc c), Module.finrank ℂ ↥(b64c_transportedFamily c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s u ⊓
      Module.End.eigenspace ((D.A s).baseChange ℂ) (Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
    intro u hu
    rw [hfam u hu]
    exact (b65z_period_eigen_ranks hg D s ⟨u, hu⟩).2
  intro t ht
  exact ⟨b64c_period_mapsTo_aux _ _ (D.A s) m hJ hpol (b6t_polydisc c) _ hR hdim hneg hpos ht,
    b64c_period_filtration_aux _ _ (D.A s) m hJ hpol (b6t_polydisc c) _ hR hdim hneg hpos t ht⟩

end HodgeLean.Foundations.Program
