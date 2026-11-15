import HodgeLean.Foundations.Program.RelativeFrameChartsDefs
import HodgeLean.Foundations.Program.RelativeFrameOperator
import HodgeLean.Foundations.Mathlib.FredholmAnalytic

/-! # Relative frames in atlas charts: lemmas for the C12 proofs
Chain rule for chart differentials on a Riemann surface, holomorphy of chart transitions, the
nonvanishing differential of a chart, and the derivative of the root map on the annulus.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

/-- Chain rule for a function `g = G ∘ f` near `y`, with `f` a complex function on a Riemann
surface and `G` holomorphic at `f y`. -/
theorem rf5_mfderiv_comp_apply {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {f g : X → ℂ} {G : ℂ → ℂ} {y : X} (hf : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f y)
    (hG : DifferentiableAt ℂ G (f y)) (hg : g =ᶠ[𝓝 y] G ∘ f) (v : TangentSpace 𝓘(ℂ, ℂ) y) :
    (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g y v) =
      deriv G (f y) * (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f y v) := by
  have h : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g y ((fderiv ℂ G (f y)).comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f y)) :=
    (hG.hasFDerivAt.hasMFDerivAt.comp y hf.hasMFDerivAt).congr_of_eventuallyEq hg
  rw [h.mfderiv]
  change fderiv ℂ G (f y) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f y v) = _
  set w : ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f y v
  rw [show w = w • (1 : ℂ) by simp, ContinuousLinearMap.map_smul, fderiv_apply_one_eq_deriv, smul_eq_mul,
    mul_comm]
  simp

/-- A chart transition between two members of the maximal atlas is analytic. -/
theorem rf5_transition_analyticAt {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {f g : OpenPartialHomeomorph X ℂ}
    (hf : f ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X) (hg : g ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    {z : ℂ} (hz : z ∈ f.target) (hz' : f.symm z ∈ g.source) : AnalyticAt ℂ (g ∘ f.symm) z := by
  have h := (contMDiffAt_of_mem_maximalAtlas hg hz').comp z
    (contMDiffAt_symm_of_mem_maximalAtlas hf hz)
  exact (contMDiffAt_iff_contDiffAt.mp h).analyticAt

/-- A member of the maximal atlas is differentiable on its source. -/
theorem rf5_mdifferentiableAt_chart {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {f : OpenPartialHomeomorph X ℂ}
    (hf : f ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X) {y : X} (hy : y ∈ f.source) :
    MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f y :=
  (contMDiffAt_of_mem_maximalAtlas hf hy).mdifferentiableAt (by simp)

/-- The differential of a member of the maximal atlas does not vanish. -/
theorem rf5_mfderiv_atlas_ne_zero {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X) {y : X} (hy : y ∈ e.source) :
    (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e y (1 : ℂ)) ≠ 0 := by
  have h := isInvertible_mfderiv_extend (I := 𝓘(ℂ, ℂ))
    (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) hy
  have hext : ((e.extend 𝓘(ℂ, ℂ) : X → ℂ)) = e := by
    funext z; simp
  rw [hext] at h
  intro h0
  obtain ⟨L, hL⟩ := h
  have h1 : L (1 : ℂ) = 0 := by
    rw [← ContinuousLinearEquiv.coe_coe, hL]; exact h0
  exact one_ne_zero (α := ℂ) (L.injective (h1.trans (map_zero L).symm))

/-- On the annulus, `Φ_ε(u)ⁿ = uⁿ − ε`. -/
theorem rf5_rootMap_pow {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) {ε u : ℂ}
    (hu : u ∈ b63r_annulus n r) : rf4_rootMap n ε u ^ n = u ^ n - ε := by
  have hu0 := rf4_closedAnnulus_ne_zero hn hr (rf4_annulus_subset_closed n r hu)
  rw [rf4_rootMap, mul_pow, Complex.cpow_nat_inv_pow _ (by omega), zpow_neg, zpow_natCast]
  field_simp

/-- The derivative of the root map on the annulus: `Φ_ε' = (1 − εu⁻ⁿ)^{1/n − 1}`. -/
theorem rf5_rootMap_hasDerivAt {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) {ε : ℂ}
    (hε : ‖ε‖ < r) {u : ℂ} (hu : u ∈ b63r_annulus n r) :
    HasDerivAt (rf4_rootMap n ε) ((1 - ε * u ^ (-(n : ℤ))) ^ ((n : ℂ)⁻¹ - 1)) u := by
  have hc := rf4_annulus_subset_closed n r hu
  have hu0 := rf4_closedAnnulus_ne_zero hn hr hc
  have hslit := rf4_slit hn hr hε hc
  have hB0 : 1 - ε * u ^ (-(n : ℤ)) ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hB := ((hasDerivAt_zpow (-(n : ℤ)) u (Or.inl hu0)).const_mul ε).const_sub 1
  have h : HasDerivAt (rf4_rootMap n ε) _ u :=
    (hasDerivAt_id u).mul (hB.cpow_const (c := (n : ℂ)⁻¹) hslit)
  convert h using 1
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  set B := 1 - ε * u ^ (-(n : ℤ)) with hBdef
  have hsplit : B ^ ((n : ℂ)⁻¹) = B ^ ((n : ℂ)⁻¹ - 1) * B := by
    conv_lhs => rw [show (n : ℂ)⁻¹ = ((n : ℂ)⁻¹ - 1) + 1 by ring]
    rw [Complex.cpow_add _ _ hB0, Complex.cpow_one]
  rw [hsplit, zpow_sub_one₀ hu0]
  simp only [id, hBdef]
  push_cast
  field_simp
  ring

/-- The differential pullback along the root map: `Φ_εʲ Φ_ε' = uʲ (1 − εu⁻ⁿ)^{s_j}`. -/
theorem rf5_rootMap_pow_mul_deriv {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) {ε : ℂ}
    (hε : ‖ε‖ < r) {u : ℂ} (hu : u ∈ b63r_annulus n r) (j : Fin n) :
    rf4_rootMap n ε u ^ (j : ℕ) * deriv (rf4_rootMap n ε) u = rf4_multiplierFun n ε j u := by
  have hc := rf4_annulus_subset_closed n r hu
  have hB0 : 1 - ε * u ^ (-(n : ℤ)) ≠ 0 := Complex.slitPlane_ne_zero (rf4_slit hn hr hε hc)
  rw [(rf5_rootMap_hasDerivAt hn hr hε hu).deriv, rf4_rootMap, rf4_multiplierFun, mul_pow,
    ← Complex.cpow_nat_mul, mul_assoc, ← Complex.cpow_add _ _ hB0, rf4_sectorExp]
  congr 2
  ring

/-- On the outer region, the glued coefficient does not depend on the piece: the compatibility of
`rf2_bddForm` and the chain rule for the transition. -/
theorem rf5_outer_compat {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (α : rf2_bddForm D.P) (y : X) (i j : Fin D.P.n)
    (hi : S.h.symm y ∈ (D.P.chart i).source) (hi' : D.P.chart i (S.h.symm y) ∈ D.P.piece i)
    (hj : S.h.symm y ∈ (D.P.chart j).source) (hj' : D.P.chart j (S.h.symm y) ∈ D.P.piece j)
    (v : TangentSpace 𝓘(ℂ, ℂ) y) :
    rf4_extendBdd (α.val i) (D.P.chart i (S.h.symm y)) * (show ℂ from
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun p : X ↦ D.P.chart i (S.h.symm p)) y v) =
      rf4_extendBdd (α.val j) (D.P.chart j (S.h.symm y)) * (show ℂ from
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun p : X ↦ D.P.chart j (S.h.symm p)) y v) := by
  have hcomp := α.property i j ⟨_, hi'⟩ ⟨_, hj'⟩ (by
    simp only [(D.P.chart i).left_inv hi, (D.P.chart j).left_inv hj])
  have hfi : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun p : X ↦ D.P.chart i (S.h.symm p)) y :=
    rf5_mdifferentiableAt_chart (S.stationary i) (by simpa using hi)
  have hG : DifferentiableAt ℂ (D.P.chart j ∘ (D.P.chart i).symm) (D.P.chart i (S.h.symm y)) :=
    (rf5_transition_analyticAt (D.P.analytic i) (D.P.analytic j) ((D.P.chart i).map_source hi)
      (by rw [(D.P.chart i).left_inv hi]; exact hj)).differentiableAt
  have hev : (fun p : X ↦ D.P.chart j (S.h.symm p)) =ᶠ[𝓝 y]
      (D.P.chart j ∘ (D.P.chart i).symm) ∘ (fun p : X ↦ D.P.chart i (S.h.symm p)) := by
    filter_upwards [S.h.symm.continuous.continuousAt.preimage_mem_nhds
      ((D.P.chart i).open_source.mem_nhds hi)] with q hq
    simp [(D.P.chart i).left_inv hq]
  rw [rf5_mfderiv_comp_apply hfi hG hev v]
  simp only [rf4_extendBdd, hi', hj', ↓reduceDIte]
  rw [hcomp]
  exact mul_assoc _ _ _


/-- A kernel element of `δ_ε` has outer coefficient `S(ε) g` on each annulus. -/
theorem rf5_kernel_coeff {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    (k : rf4_Src D) (hk : k ∈ (rf4_delta D ε).ker) (x : Fin D.m) (hε : ‖ε x‖ < D.r) {u : ℂ}
    (hu : u ∈ b63r_annulus (D.deg x) D.r) :
    rf4_extendBdd (k.1.val (D.ann x)) u = D.deg x * ∑ j : Fin (D.deg x),
      rf4_multiplierFun (D.deg x) (ε x) j u * rf4_extendBdd (k.2 x j) (D.c x + u ^ D.deg x) := by
  have h0 := congrArg (fun φ : rf4_Tgt D ↦
    ((φ x : b63r_bddHol (b63r_annulus (D.deg x) D.r)) : b63r_annulus (D.deg x) D.r →ᵇ ℂ) ⟨u, hu⟩)
    (LinearMap.mem_ker.mp hk)
  have hs := rf4_sectorOp_apply (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x) hε (k.2 x) ⟨u, hu⟩
  have hpu : u ∈ D.P.piece (D.ann x) := by rw [D.hann x]; exact hu
  simp only [rf4_delta] at h0
  rw [← hs, ← sub_eq_zero]
  rw [show rf4_extendBdd (k.1.val (D.ann x)) u = ((k.1.val (D.ann x) : b63r_bddHol _) :
    D.P.piece (D.ann x) →ᵇ ℂ) ⟨u, hpu⟩ by simp [rf4_extendBdd, hpu]]
  exact h0

/-- A function analytic on an open set of the total space is analytic in every atlas chart. -/
theorem rf5_chart_analyticOnNhd {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    {φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ)}
    (hφ : φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    {G : b6t_polydisc b × C → ℂ} {A : Set (b6t_polydisc b × C)} (hA : IsOpen A)
    (hG : ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω G A) :
    AnalyticOnNhd ℂ (G ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' A) := by
  intro p hp
  have h := (hG.contMDiffAt (hA.mem_nhds hp.2)).comp p
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hφ) hp.1)
  exact (contMDiffAt_iff_contDiffAt.mp h).analyticAt

/-- The vertical derivative `∂_z` of a function analytic near a point of `(Fin 10 → ℂ) × ℂ` is
analytic there. -/
theorem rf5_vertical_analyticAt {f : (Fin 10 → ℂ) × ℂ → ℂ} {p : (Fin 10 → ℂ) × ℂ}
    (hf : AnalyticAt ℂ f p) :
    AnalyticAt ℂ (fun q ↦ fderiv ℂ f q ((0 : Fin 10 → ℂ), (1 : ℂ))) p :=
  (ContinuousLinearMap.apply ℂ ℂ ((0 : Fin 10 → ℂ), (1 : ℂ))).analyticAt _ |>.comp hf.fderiv

/-- Vertical chain rule on a fibre: the differential along the fibre at `t` of a function `G` of
the total space is its vertical derivative in the chart `φ` times the differential of the vertical
coordinate of `φ`. -/
theorem rf5_fibre_mfderiv {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    {V : Set (Fin 10 → ℂ)} {hV : V ⊆ b6t_polydisc b}
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    (t : V) (hincl : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    {φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ)}
    (hφ : φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hp : ∀ y ∈ φ.source, (φ y).1 = y.1.val)
    {G : b6t_polydisc b × C → ℂ} {y : b63l_parameterFibre b C V hV t} (hy : y.val ∈ φ.source)
    (hG : AnalyticAt ℂ (G ∘ φ.symm) (φ y.val))
    {g : b63l_parameterFibre b C V hV t → ℂ} (hg : g =ᶠ[𝓝 y] fun z ↦ G z.val)
    (v : TangentSpace 𝓘(ℂ, ℂ) y) :
    (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g y v) =
      fderiv ℂ (G ∘ φ.symm) (φ y.val) ((0 : Fin 10 → ℂ), (1 : ℂ)) * (show ℂ from
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun z : b63l_parameterFibre b C V hV t ↦ (φ z.val).2) y v) := by
  have hfib : ∀ z : b63l_parameterFibre b C V hV t, z.val ∈ φ.source →
      ((t.val, (φ z.val).2) : (Fin 10 → ℂ) × ℂ) = φ z.val := by
    intro z hz
    refine Prod.ext ?_ rfl
    rw [hp _ hz]
    exact (congrArg Subtype.val z.property).symm
  have hψ : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun z : b63l_parameterFibre b C V hV t ↦ (φ z.val).2) y := by
    have h1 : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
        (fun z : b63l_parameterFibre b C V hV t ↦ (φ z.val).2) y :=
      (contDiff_snd.contMDiff.contMDiffAt).comp y
        ((contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hφ) hy).comp y
          hincl.contMDiffAt)
    exact h1.mdifferentiableAt (by simp)
  have hpr : HasDerivAt (fun s : ℂ ↦ ((t.val, s) : (Fin 10 → ℂ) × ℂ))
      ((0 : Fin 10 → ℂ), (1 : ℂ)) (φ y.val).2 :=
    (hasDerivAt_const _ t.val).prodMk (hasDerivAt_id _)
  have hd : HasDerivAt (fun s : ℂ ↦ (G ∘ φ.symm) (t.val, s))
      (fderiv ℂ (G ∘ φ.symm) (φ y.val) ((0 : Fin 10 → ℂ), (1 : ℂ))) (φ y.val).2 := by
    have h2 := hG.differentiableAt.hasFDerivAt
    rw [← hfib y hy] at h2
    have h3 := h2.comp_hasDerivAt (φ y.val).2 hpr
    rw [hfib y hy] at h3
    exact h3
  have hev : g =ᶠ[𝓝 y] (fun s : ℂ ↦ (G ∘ φ.symm) (t.val, s)) ∘
      (fun z : b63l_parameterFibre b C V hV t ↦ (φ z.val).2) := by
    filter_upwards [hg, continuous_subtype_val.continuousAt.preimage_mem_nhds
      (φ.open_source.mem_nhds hy)] with z hz hzs
    rw [hz]
    simp only [Function.comp, hfib z hzs, φ.left_inv hzs]
  rw [rf5_mfderiv_comp_apply hψ hd.differentiableAt hev v, hd.deriv]

/-- Joint analyticity of the evaluation of an analytic family of bounded holomorphic functions,
in the form of `rf4_extendBdd`. -/
theorem rf5_extendBdd_analyticAt {U : Set ℂ} (hU : IsOpen U) {W : Set (Fin 10 → ℂ)}
    (hW : IsOpen W) {e : (Fin 10 → ℂ) → b63r_bddHol U} (he : AnalyticOnNhd ℂ e W)
    {s : Fin 10 → ℂ} {z : ℂ} (hs : s ∈ W) (hz : z ∈ U) :
    AnalyticAt ℂ (fun q : (Fin 10 → ℂ) × ℂ ↦ rf4_extendBdd (e q.1) q.2) (s, z) := by
  classical
  have h := b63r_eval_analytic hU W hW e he (s, z) ⟨hs, hz⟩
  refine h.congr (Filter.Eventually.of_forall fun q ↦ ?_)
  simp only [rf4_extendBdd]


/-- A fibre point in a fibre-preserving chart has first chart coordinate its parameter. -/
theorem rf5_fibre_fst {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    {V : Set (Fin 10 → ℂ)} {hV : V ⊆ b6t_polydisc b}
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    {φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ)}
    (hp : ∀ y ∈ φ.source, (φ y).1 = y.1.val) {t : V} (y : b63l_parameterFibre b C V hV t)
    (hy : y.val ∈ φ.source) : (φ y.val).1 = t.val := by
  rw [hp _ hy]
  exact congrArg Subtype.val y.property

/-- In a chart `φ` of a space over `C`, the outer coefficient `α_i(U_i) ∂_z U_i` does not depend on
the piece `i`. -/
theorem rf5_outer_chart_compat {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {P : rf2_PieceCover C O} {Y : Type}
    [TopologicalSpace Y] (φ : OpenPartialHomeomorph (Y × C) ((Fin 10 → ℂ) × ℂ))
    (α : rf2_bddForm P) {p : (Fin 10 → ℂ) × ℂ} (hpt : p ∈ φ.target) (i j : Fin P.n)
    (hi : (φ.symm p).2 ∈ (P.chart i).source) (hi' : P.chart i (φ.symm p).2 ∈ P.piece i)
    (hj : (φ.symm p).2 ∈ (P.chart j).source) (hj' : P.chart j (φ.symm p).2 ∈ P.piece j)
    (hd : DifferentiableAt ℂ ((fun q : Y × C ↦ P.chart i q.2) ∘ φ.symm) p) :
    rf4_extendBdd (α.val i) (((fun q : Y × C ↦ P.chart i q.2) ∘ φ.symm) p) *
        fderiv ℂ ((fun q : Y × C ↦ P.chart i q.2) ∘ φ.symm) p ((0 : Fin 10 → ℂ), (1 : ℂ)) =
      rf4_extendBdd (α.val j) (((fun q : Y × C ↦ P.chart j q.2) ∘ φ.symm) p) *
        fderiv ℂ ((fun q : Y × C ↦ P.chart j q.2) ∘ φ.symm) p ((0 : Fin 10 → ℂ), (1 : ℂ)) := by
  have hcomp := α.property i j ⟨_, hi'⟩ ⟨_, hj'⟩ (by
    simp only [(P.chart i).left_inv hi, (P.chart j).left_inv hj])
  have hT : DifferentiableAt ℂ (P.chart j ∘ (P.chart i).symm) (P.chart i (φ.symm p).2) :=
    (rf5_transition_analyticAt (P.analytic i) (P.analytic j) ((P.chart i).map_source hi)
      (by rw [(P.chart i).left_inv hi]; exact hj)).differentiableAt
  have hN : IsOpen (φ.target ∩ φ.symm ⁻¹' (Prod.snd ⁻¹' (P.chart i).source)) :=
    φ.isOpen_inter_preimage_symm ((P.chart i).open_source.preimage continuous_snd)
  have hev : ((fun q : Y × C ↦ P.chart j q.2) ∘ φ.symm) =ᶠ[𝓝 p]
      (P.chart j ∘ (P.chart i).symm) ∘ ((fun q : Y × C ↦ P.chart i q.2) ∘ φ.symm) := by
    filter_upwards [hN.mem_nhds ⟨hpt, hi⟩] with q hq
    simp [(P.chart i).left_inv hq.2]
  rw [hev.fderiv_eq, fderiv_comp p hT hd]
  simp only [rf4_extendBdd, Function.comp_apply, hi', hj', ↓reduceDIte]
  rw [hcomp]
  change _ = _ * (fderiv ℂ (P.chart j ∘ (P.chart i).symm) (P.chart i (φ.symm p).2)
    (fderiv ℂ ((fun q : Y × C ↦ P.chart i q.2) ∘ φ.symm) p ((0 : Fin 10 → ℂ), (1 : ℂ))))
  set w : ℂ := fderiv ℂ ((fun q : Y × C ↦ P.chart i q.2) ∘ φ.symm) p ((0 : Fin 10 → ℂ), (1 : ℂ))
  rw [show w = w • (1 : ℂ) by simp, ContinuousLinearMap.map_smul, fderiv_apply_one_eq_deriv,
    smul_eq_mul]
  simp only [smul_eq_mul, mul_one]
  ring

end HodgeLean.Foundations.Program
