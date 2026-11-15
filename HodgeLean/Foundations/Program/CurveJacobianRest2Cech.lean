import HodgeLean.Foundations.Program.CurveJacobianRest2Simplex
import HodgeLean.Foundations.Program.CurveJacobianRest2Lattice

/-! # Track B3, lane Rest2: a rational `1`-cocycle on a convex chart cover

On a compact manifold choose finitely many chart balls `O_x` (convex in their charts) covering it
(`b3Rest2_Cov`). For a singular `1`-cocycle `ψ` and a ball `O_x` with centre `x`, put
`b_x(p) = ψ([x, p])` (the chart segment). By the cone identity, `ψ(g) = b_x(g 1) - b_x(g 0)` for
every path `g` in `O_x` (`b3Rest2_P_eq_b`), and on `O_x ∩ O_y` the difference `b_x - b_y` is locally
constant (`b3Rest2_b_sub_locallyConst`): both compute `ψ` of a short chart segment.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold Metric
open scoped Topology ContDiff Simplicial

namespace HodgeLean.Foundations.Program

open HodgeLean.Adapters

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C]

/-- **A finite cover by convex chart balls.** -/
structure b3Rest2_Cov (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Type)
    [TopologicalSpace C] [ChartedSpace E C] where
  S : Finset C
  r : C → ℝ
  r_pos : ∀ x, 0 < r x
  ball_sub : ∀ x, ball (chartAt E x x) (r x) ⊆ (chartAt E x).target
  cover : ∀ p, ∃ x ∈ S, p ∈ (chartAt E x).source ∧ chartAt E x p ∈ ball (chartAt E x x) (r x)

namespace b3Rest2_Cov

variable (K : b3Rest2_Cov E C)

/-- The ball of the cover with centre `x`, in `C`. -/
def O (x : C) : Set C := (chartAt E x).source ∩ chartAt E x ⁻¹' ball (chartAt E x x) (K.r x)

theorem isOpen_O (x : C) : IsOpen (K.O x) :=
  (chartAt E x).continuousOn.isOpen_inter_preimage (chartAt E x).open_source isOpen_ball

theorem mem_O_self (x : C) : x ∈ K.O x :=
  ⟨mem_chart_source E x, mem_ball_self (K.r_pos x)⟩

theorem center_mem (x : C) : chartAt E x x ∈ ball (chartAt E x x) (K.r x) :=
  mem_ball_self (K.r_pos x)

end b3Rest2_Cov

theorem b3Rest2_exists_cov [CompactSpace C] : Nonempty (b3Rest2_Cov E C) := by
  have hρ : ∀ y : C, ∃ ρ > 0, ball (chartAt E y y) ρ ⊆ (chartAt E y).target := fun y ↦
    Metric.isOpen_iff.1 (chartAt E y).open_target _ ((chartAt E y).map_source (mem_chart_source E y))
  choose r hr hrsub using hρ
  let U : C → Set C := fun y ↦ (chartAt E y).source ∩ chartAt E y ⁻¹' ball (chartAt E y y) (r y)
  have hUo : ∀ y, IsOpen (U y) := fun y ↦
    (chartAt E y).continuousOn.isOpen_inter_preimage (chartAt E y).open_source isOpen_ball
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun p _ ↦ mem_iUnion.2 ⟨p, mem_chart_source E p, mem_ball_self (hr p)⟩)
  refine ⟨⟨S, r, hr, hrsub, fun p ↦ ?_⟩⟩
  obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.1 (hS (mem_univ p))
  exact ⟨x, hx, hpx⟩

namespace b3Rest2_Cov

variable (K : b3Rest2_Cov E C)

/-- **The cone values** `b_x(p) = ψ([x, p])` of a cochain on the ball with centre `x`. -/
def b (ψ : AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj (TopCat.of C)) 1)
    (x : C) (p : C) : ℝ :=
  open scoped Classical in
  if hp : p ∈ K.O x then
    ((b3Rest2_P ψ (b3Rest2_seg (chartAt E x) (convex_ball _ _) (K.ball_sub x) (K.center_mem x)
      hp.2) : ℚ) : ℝ)
  else 0

/-- **The value of a cocycle on a path in a ball of the cover** is the difference of its cone
values at the ends. -/
theorem P_eq_b (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of C)) 1)
    (x : C) (g : C(unitInterval, C)) (hg : ∀ t, g t ∈ K.O x) :
    ((b3Rest2_P ψ.1 g : ℚ) : ℝ) = K.b ψ.1 x (g 1) - K.b ψ.1 x (g 0) := by
  rw [b3Rest2_cone (chartAt E x) (convex_ball _ _) (K.ball_sub x) ψ (K.center_mem x) g
    (fun t ↦ (hg t).1) (fun t ↦ (hg t).2)]
  simp only [b, hg 1, hg 0, dite_true]
  push_cast
  rfl

/-- **On the overlap of two balls the cone values differ by a locally constant function.** -/
theorem b_sub_locallyConst
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of C)) 1)
    {x y p : C} (hpx : p ∈ K.O x) (hpy : p ∈ K.O y) :
    ∀ᶠ q in 𝓝 p, K.b ψ.1 x q - K.b ψ.1 y q = K.b ψ.1 x p - K.b ψ.1 y p := by
  set e := chartAt E y
  set V := e.target ∩ e.symm ⁻¹' (K.O x ∩ K.O y)
  have hVo : IsOpen V :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target ((K.isOpen_O x).inter (K.isOpen_O y))
  have huV : e p ∈ V := ⟨e.map_source hpy.1, by rw [mem_preimage, e.left_inv hpy.1]; exact ⟨hpx, hpy⟩⟩
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.1 hVo _ huV
  have hBt : ball (e p) δ ⊆ e.target := fun u hu ↦ (hδV hu).1
  filter_upwards [e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball |>.mem_nhds
    (show p ∈ e.source ∩ e ⁻¹' ball (e p) δ from ⟨hpy.1, mem_ball_self hδ⟩)] with q hq
  set g := b3Rest2_seg e (convex_ball (e p) δ) hBt (mem_ball_self hδ) hq.2
  have hg : ∀ t, g t ∈ K.O x ∩ K.O y := fun t ↦
    (hδV (b3Rest2_seg_mem e (convex_ball (e p) δ) hBt (mem_ball_self hδ) hq.2 t t.2)).2
  have hg0 : g 0 = p := by
    simp only [g, b3Rest2_seg_apply, Set.Icc.coe_zero, zero_smul, add_zero]
    exact e.left_inv hpy.1
  have hg1 : g 1 = q := by
    simp only [g, b3Rest2_seg_apply, Set.Icc.coe_one, one_smul, add_sub_cancel]
    exact e.left_inv hq.1
  have h1 := K.P_eq_b ψ x g fun t ↦ (hg t).1
  have h2 := K.P_eq_b ψ y g fun t ↦ (hg t).2
  rw [hg0, hg1] at h1 h2
  linarith

end b3Rest2_Cov

theorem cochain_ext_simplex_b3Rest2 {R : Type} [CommRing R] {Y : SSet.{0}} {n : ℕ}
    (φ ψ : AlgebraicTopology.Simplicial.Cochain R Y n)
    (h : ∀ σ : Y _⦋n⦌, φ (AlgebraicTopology.Simplicial.chainOfSimplex R σ) =
      ψ (AlgebraicTopology.Simplicial.chainOfSimplex R σ)) : φ = ψ := by
  have hc : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := by
    apply SSet.chainComplex_hom_ext
    intro σ
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    have hi : (Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a =
        a • AlgebraicTopology.Simplicial.chainOfSimplex R σ := by
      rw [AlgebraicTopology.Simplicial.chainOfSimplex, ← map_smul]
      simp
    change φ ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a) =
      ψ ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a)
    rw [hi, map_smul, map_smul, h]
  exact congrArg ModuleCat.Hom.hom hc

/-! ## The closed form of a cocycle -/

section Form

variable [IsManifold 𝓘(ℝ, E) ∞ C] [FiniteDimensional ℝ E] [T2Space C] [CompactSpace C]

/-- **A partition of unity subordinate to the cover, with cut-offs** equal to `1` near the
support of each function and supported in a compact part of its ball. -/
structure b3Rest2_PoU (K : b3Rest2_Cov E C) where
  ρ : SmoothPartitionOfUnity K.S 𝓘(ℝ, E) C univ
  sub : ρ.IsSubordinate fun i : K.S ↦ K.O (i : C)
  χ : K.S → C → ℝ
  χ_smooth : ∀ i : K.S, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (χ i)
  χ_one : ∀ i : K.S, ∀ᶠ p in 𝓝ˢ (tsupport (ρ i)), χ i p = 1
  χ_supp : ∀ i : K.S, ∃ L : Set C, IsCompact L ∧ L ⊆ K.O (i : C) ∧ ∀ p ∉ L, χ i p = 0

theorem b3Rest2_exists_pou (K : b3Rest2_Cov E C) : Nonempty (b3Rest2_PoU K) := by
  haveI := FiniteDimensional.proper_real E
  have : LocallyCompactSpace C := ChartedSpace.locallyCompactSpace E C
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, E)) isClosed_univ
    (fun i : K.S ↦ K.O i) (fun i ↦ K.isOpen_O i) (fun p _ ↦ by
      obtain ⟨x, hx, hp⟩ := K.cover p
      exact mem_iUnion.2 ⟨⟨x, hx⟩, hp⟩)
  have hcut : ∀ i : K.S, ∃ χ : C → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ ∧
      (∀ᶠ p in 𝓝ˢ (tsupport (ρ i)), χ p = 1) ∧
      ∃ L : Set C, IsCompact L ∧ L ⊆ K.O i ∧ ∀ p ∉ L, χ p = 0 := by
    intro i
    obtain ⟨L, hL, hsL, hLO⟩ := exists_compact_between (isClosed_tsupport _).isCompact
      (K.isOpen_O i) (hρ i)
    obtain ⟨f, hf1, hf0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, E)
      (n := (⊤ : ℕ∞)) (isClosed_tsupport (ρ i)) hsL
    exact ⟨f, f.contMDiff, hf1, L, hL, hLO, hf0⟩
  choose χ hχs hχ1 hχ0 using hcut
  exact ⟨⟨ρ, hρ, χ, hχs, hχ1, hχ0⟩⟩

namespace b3Rest2_PoU

variable {K : b3Rest2_Cov E C} (U : b3Rest2_PoU K)
  (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of C)) 1)

theorem sum_ρ (p : C) : ∑ i, U.ρ i p = 1 := by
  rw [← finsum_eq_sum_of_fintype]
  exact U.ρ.sum_eq_one (mem_univ p)

/-- The global part `G = Σ ρ_z b_z` of the cone values. -/
def G (p : C) : ℝ := ∑ z, U.ρ z p * K.b ψ.1 z p

/-- **The local primitive** `h_y = Σ ρ_z (b_y - b_z) = b_y - G`. -/
def h (y : C) (p : C) : ℝ := ∑ z, U.ρ z p * (K.b ψ.1 y p - K.b ψ.1 z p)

theorem h_eq (y p : C) : U.h ψ y p = K.b ψ.1 y p - U.G ψ p := by
  simp only [h, G, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_ρ, one_mul]

theorem h_sub_locallyConst {x y p : C} (hpx : p ∈ K.O x) (hpy : p ∈ K.O y) :
    ∀ᶠ q in 𝓝 p, U.h ψ x q - U.h ψ y q = U.h ψ x p - U.h ψ y p := by
  filter_upwards [K.b_sub_locallyConst ψ hpx hpy] with q hq
  rw [h_eq, h_eq, h_eq, h_eq]
  linarith

theorem contMDiffAt_h {y p : C} (hp : p ∈ K.O y) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (U.h ψ y) p := by
  refine ContMDiffAt.sum fun z _ ↦ ?_
  by_cases hz : p ∈ tsupport (U.ρ z)
  · have hpz : p ∈ K.O z := U.sub z hz
    refine ((U.ρ z).contMDiff.contMDiffAt.mul
      (contMDiffAt_const (c := K.b ψ.1 y p - K.b ψ.1 z p))).congr_of_eventuallyEq ?_
    filter_upwards [K.b_sub_locallyConst ψ hp hpz] with q hq
    show U.ρ z q * (K.b ψ.1 y q - K.b ψ.1 z q) = U.ρ z q * (K.b ψ.1 y p - K.b ψ.1 z p)
    rw [hq]
  · refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hz] with q hq
    rw [image_eq_zero_of_notMem_tsupport hq, zero_mul]

/-- The cut-off primitive `H_y = χ_y h_y`, a smooth function on `C`. -/
def H (y : K.S) (p : C) : ℝ := U.χ y p * U.h ψ y p

theorem contMDiff_H (y : K.S) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (U.H ψ y) := by
  intro p
  obtain ⟨L, hL, hLO, hL0⟩ := U.χ_supp y
  by_cases hp : p ∈ K.O y
  · exact ((U.χ_smooth y).contMDiffAt).mul (U.contMDiffAt_h ψ hp)
  · have hpL : p ∉ L := fun h ↦ hp (hLO h)
    refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hL.isClosed.isOpen_compl.mem_nhds hpL] with q hq
    show U.χ y q * U.h ψ y q = 0
    rw [hL0 q hq, zero_mul]

theorem isSmooth_H (y : K.S) : b3Forms_IsSmooth (b3Forms_fun (E := E) (U.H ψ y)) :=
  b3Forms_isSmooth_fun (U.contMDiff_H ψ y)

/-- **The closed form of the cocycle**, `α = Σ ρ_y dH_y`. -/
def α : C → E [⋀^Fin 1]→L[ℝ] ℝ :=
  ∑ y, b3Forms_smulFun (U.ρ y) (b3Forms_d (b3Forms_fun (E := E) (U.H ψ y)))

theorem isSmooth_α : b3Forms_IsSmooth (U.α ψ) :=
  (b3Forms_Ω E C 1).sum_mem fun y _ ↦ (U.isSmooth_H ψ y).d.smulFun (U.ρ y).contMDiff

/-- The differential of a function at a point depends only on its germ up to a constant. -/
theorem d_fun_congr {f g : C → ℝ} {q : C} {c : ℝ} (h : ∀ᶠ p in 𝓝 q, f p = g p + c) :
    b3Forms_d (b3Forms_fun (E := E) f) q = b3Forms_d (b3Forms_fun (E := E) g) q := by
  rw [b3Forms_d_fun, b3Forms_d_fun]
  congr 1
  have hq := (chartAt E q).map_source (mem_chart_source E q)
  have h' : f ∘ (chartAt E q).symm =ᶠ[𝓝 (chartAt E q q)] fun u ↦ (g ∘ (chartAt E q).symm) u + c := by
    have ht : Tendsto (chartAt E q).symm (𝓝 (chartAt E q q)) (𝓝 q) :=
      (chartAt E q).tendsto_symm (mem_chart_source E q)
    exact ht.eventually h
  rw [h'.fderiv_eq, fderiv_add_const]

/-- **Near a point of the ball `O_y`, `α` is the differential of any smooth function equal to
`h_y` near that point.** -/
theorem α_eq_d {y q : C} (hq : q ∈ K.O y) {H' : C → ℝ} (hH' : ∀ᶠ p in 𝓝 q, H' p = U.h ψ y p) :
    U.α ψ q = b3Forms_d (b3Forms_fun (E := E) H') q := by
  simp only [α, Finset.sum_apply, b3Forms_smulFun]
  have hterm : ∀ x : K.S, U.ρ x q • b3Forms_d (b3Forms_fun (E := E) (U.H ψ x)) q =
      U.ρ x q • b3Forms_d (b3Forms_fun (E := E) H') q := by
    intro x
    by_cases hx : U.ρ x q = 0
    · rw [hx, zero_smul, zero_smul]
    · have hsupp : q ∈ tsupport (U.ρ x) := subset_tsupport _ hx
      have hqx : q ∈ K.O x := U.sub x hsupp
      congr 1
      refine d_fun_congr (c := U.h ψ x q - U.h ψ y q) ?_
      filter_upwards [(U.χ_one x).filter_mono (nhds_le_nhdsSet hsupp),
        U.h_sub_locallyConst ψ hqx hq, hH'] with p hp1 hp2 hp3
      simp only [H, hp1, one_mul, hp3]
      linarith
  rw [Finset.sum_congr rfl fun x _ ↦ hterm x, ← Finset.sum_smul, sum_ρ, one_smul]

/-- A smooth function on `C` equal to `h_y` up to a constant near a point of `O_y`. -/
theorem exists_smooth_germ {y q : C} (hq : q ∈ K.O y) :
    ∃ H' : C → ℝ, b3Forms_IsSmooth (b3Forms_fun (E := E) H') ∧ ∀ᶠ p in 𝓝 q, H' p = U.h ψ y p := by
  obtain ⟨x, hx⟩ : ∃ x : K.S, U.ρ x q ≠ 0 := by
    by_contra hall
    push_neg at hall
    have := U.sum_ρ q
    simp [hall] at this
  have hsupp : q ∈ tsupport (U.ρ x) := subset_tsupport _ hx
  have hqx : q ∈ K.O x := U.sub x hsupp
  refine ⟨fun p ↦ U.H ψ x p - (U.h ψ x q - U.h ψ y q),
    (b3Forms_isSmooth_fun ((U.contMDiff_H ψ x).sub contMDiff_const)), ?_⟩
  filter_upwards [(U.χ_one x).filter_mono (nhds_le_nhdsSet hsupp),
    U.h_sub_locallyConst ψ hqx hq] with p hp1 hp2
  simp only [H, hp1, one_mul]
  linarith

/-- **`α` is closed.** -/
theorem d_α : b3Forms_d (U.α ψ) = 0 := by
  funext q
  obtain ⟨y, -, hqy⟩ := K.cover q
  obtain ⟨H', hH's, hH'⟩ := U.exists_smooth_germ ψ hqy
  have hev : U.α ψ =ᶠ[𝓝 q] b3Forms_d (b3Forms_fun (E := E) H') := by
    filter_upwards [(K.isOpen_O y).mem_nhds hqy, hH'.eventually_nhds] with p hp hp'
    exact U.α_eq_d ψ hp hp'
  have hloc : b3Forms_loc (U.α ψ) q =ᶠ[𝓝 (chartAt E q q)]
      b3Forms_loc (b3Forms_d (b3Forms_fun (E := E) H')) q := by
    have hq := (chartAt E q).map_source (mem_chart_source E q)
    have ht : Tendsto (chartAt E q).symm (𝓝 (chartAt E q q)) (𝓝 q) :=
      (chartAt E q).tendsto_symm (mem_chart_source E q)
    filter_upwards [ht.eventually hev] with u hu
    simp only [b3Forms_loc, hu]
  have h0 := congrFun (b3Forms_d_d hH's) q
  show extDeriv (b3Forms_loc (U.α ψ) q) (chartAt E q q) = 0
  rw [hloc.extDeriv_eq]
  exact h0

/-- **The fundamental theorem of calculus for `α` on a ball of the cover.** -/
theorem lineIntegral_α {y : C} {γ : ℝ → C} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) {a b : ℝ}
    (hab : ∀ t ∈ uIcc a b, γ t ∈ K.O y) :
    b3Forms_lineIntegral (U.α ψ) γ a b = U.h ψ y (γ b) - U.h ψ y (γ a) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := U.h ψ y ∘ γ) (fun t ht ↦ ?_)
    (b3Forms_intervalIntegrable_lineIntegrand (U.isSmooth_α ψ) hγ a b)
  obtain ⟨H', hH's, hH'⟩ := U.exists_smooth_germ ψ (hab t ht)
  have h1 := b3Forms_hasDerivAt_comp hH's hγ t
  rw [← U.α_eq_d ψ (hab t ht) hH'] at h1
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hγ.continuous.continuousAt.eventually hH'] with s hs
  exact hs.symm

/-- **The cocycle on a path through pieces in the balls** is the change of `h + G`, where the
pieces lie in balls. -/
theorem P_piece {y : C} (g : C(unitInterval, C)) (a b : unitInterval) (hab : (a : ℝ) ≤ b)
    (hg : ∀ t : unitInterval, (t : ℝ) ∈ Icc (a : ℝ) b → g t ∈ K.O y) :
    ((b3Rest2_P ψ.1 (b3Rest2_restr g a b) : ℚ) : ℝ) =
      (U.h ψ y (g b) + U.G ψ (g b)) - (U.h ψ y (g a) + U.G ψ (g a)) := by
  rw [K.P_eq_b ψ y _ fun t ↦ hg (b3Rest2_affI a b t) (b3Rest2_affI_mem hab t), b3Rest2_restr_apply,
    b3Rest2_restr_apply, h_eq, h_eq]
  have h1 : b3Rest2_affI a b 1 = b := by apply Subtype.ext; simp [b3Rest2_affI]
  have h0 : b3Rest2_affI a b 0 = a := by apply Subtype.ext; simp [b3Rest2_affI]
  rw [h1, h0]
  ring

/-- **The loop formula**: the value of the cocycle on the simplex of a loop is the integral of
`α` along a `C¹` loop with the same values. -/
theorem loop_formula {γ : ℝ → C} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (hper : Function.Periodic γ 1) (p : C(UnitAddCircle, C)) (hp : ∀ t, γ t = p t) :
    ((ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (loopSimplex p)) : ℚ) : ℝ) =
      b3Forms_lineIntegral (U.α ψ) γ 0 1 := by
  set g := simplexPath (loopSimplex p)
  have hg : ∀ t : unitInterval, g t = γ t := fun t ↦ by
    simp only [g, spec_simplexPath_loopSimplex_aux, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk]
    exact (hp t).symm
  rw [b3Rest2_P_simplexPath]
  obtain ⟨n, hn, hpieces⟩ := b3Rest2_exists_pieces g (fun x : K.S ↦ K.O (x : C))
    (fun x ↦ K.isOpen_O x) (fun q ↦ by
      obtain ⟨x, hx, hq⟩ := K.cover q
      exact ⟨⟨x, hx⟩, hq⟩)
  haveI : Nonempty K.S := ⟨⟨_, (K.cover (γ 0)).choose_spec.1⟩⟩
  choose! x hx using hpieces
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hfr : ∀ k ≤ n, (b3Rest2_frac n k : ℝ) = (k : ℝ) / n := fun k hk ↦ b3Rest2_frac_coe hk hn
  rw [b3Rest2_P_eq_sum ψ g hn, Rat.cast_sum]
  have hpiece : ∀ k ∈ Finset.range n,
      ((b3Rest2_P ψ.1 (b3Rest2_restr g (b3Rest2_frac n k) (b3Rest2_frac n (k + 1))) : ℚ) : ℝ) =
        b3Forms_lineIntegral (U.α ψ) γ ((k : ℝ) / n) ((k + 1 : ℝ) / n) +
          (U.G ψ (γ ((k + 1 : ℝ) / n)) - U.G ψ (γ ((k : ℝ) / n))) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hle : (k : ℝ) / n ≤ ((k + 1 : ℝ)) / n := by gcongr; linarith
    rw [U.P_piece ψ g _ _ (by rw [hfr k hk'.le, hfr (k + 1) hk']; push_cast; exact hle)
      (fun t ht ↦ hx k hk' t (by rw [hfr k hk'.le, hfr (k + 1) hk'] at ht; push_cast at ht; exact ht)),
      hg, hg, hfr k hk'.le, hfr (k + 1) hk', U.lineIntegral_α ψ hγ (y := x k) (fun t ht ↦ ?_)]
    · push_cast
      ring
    · rw [uIcc_of_le hle] at ht
      have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨le_trans (by positivity) ht.1, le_trans ht.2 (by
        rw [div_le_one hN]; exact_mod_cast hk')⟩
      have := hx k hk' ⟨t, ht01⟩ ht
      rwa [hg] at this
  have htel : ∑ k ∈ Finset.range n, (U.G ψ (γ ((k + 1 : ℝ) / n)) - U.G ψ (γ ((k : ℝ) / n))) =
      U.G ψ (γ ((n : ℝ) / n)) - U.G ψ (γ ((0 : ℕ) / n)) := by
    have := Finset.sum_range_sub (fun k : ℕ ↦ U.G ψ (γ ((k : ℝ) / n))) n
    push_cast at this ⊢
    exact this
  rw [Finset.sum_congr rfl hpiece, Finset.sum_add_distrib, htel]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ ↦ (i : ℝ) / n)
    (n := n) (f := fun t ↦ U.α ψ (γ t) (fun _ ↦ b3Forms_velocity γ t))
    (μ := MeasureTheory.volume)
    (fun i _ ↦ b3Forms_intervalIntegrable_lineIntegrand (U.isSmooth_α ψ) hγ _ _)
  simp only [Nat.cast_zero, zero_div, div_self hN.ne', Nat.cast_add, Nat.cast_one] at hsum
  have hγ1 : γ 1 = γ 0 := by simpa using hper 0
  simp only [Nat.cast_zero, zero_div, Nat.cast_add, Nat.cast_one, div_self hN.ne', hγ1, sub_self,
    add_zero]
  exact hsum

/-- If `α = dF`, then `h_y - F` is constant on the ball `O_y`. -/
theorem h_sub_F_const {F : C → ℝ} (hF : b3Forms_IsSmooth (b3Forms_fun (E := E) F))
    (hαF : U.α ψ = b3Forms_d (b3Forms_fun (E := E) F)) {y q₁ q₂ : C} (h₁ : q₁ ∈ K.O y)
    (h₂ : q₂ ∈ K.O y) : U.h ψ y q₂ - U.h ψ y q₁ = F q₂ - F q₁ := by
  have hγ := b3Forms_segPath_isTame y (convex_ball _ _) (K.ball_sub y) h₁.2 h₂.2
  have hmem : ∀ t, b3Forms_segPath y (chartAt E y q₁) (chartAt E y q₂) t ∈ K.O y := fun t ↦
    b3Forms_chart_segPath y (convex_ball _ _) (K.ball_sub y) h₁.2 h₂.2 t
  have hγ0 : b3Forms_segPath y (chartAt E y q₁) (chartAt E y q₂) 0 = q₁ := by
    rw [b3Forms_segPath_zero]; exact (chartAt E y).left_inv h₁.1
  have hγ1 : b3Forms_segPath y (chartAt E y q₁) (chartAt E y q₂) 1 = q₂ := by
    rw [b3Forms_segPath_one]; exact (chartAt E y).left_inv h₂.1
  have e1 := U.lineIntegral_α ψ hγ.1 (a := 0) (b := 1) fun t _ ↦ hmem t
  rw [hαF, b3Forms_lineIntegral_d hF hγ.1, hγ0, hγ1] at e1
  exact e1.symm

/-- If `α = dF`, the cocycle on every path is the change of `F + G`. -/
theorem P_eq_of_exact {F : C → ℝ} (hF : b3Forms_IsSmooth (b3Forms_fun (E := E) F))
    (hαF : U.α ψ = b3Forms_d (b3Forms_fun (E := E) F)) (g : C(unitInterval, C)) :
    ((b3Rest2_P ψ.1 g : ℚ) : ℝ) = (F (g 1) + U.G ψ (g 1)) - (F (g 0) + U.G ψ (g 0)) := by
  obtain ⟨n, hn, hpieces⟩ := b3Rest2_exists_pieces g (fun x : K.S ↦ K.O (x : C))
    (fun x ↦ K.isOpen_O x) (fun q ↦ by
      obtain ⟨x, hx, hq⟩ := K.cover q
      exact ⟨⟨x, hx⟩, hq⟩)
  haveI : Nonempty K.S := ⟨⟨_, (K.cover (g 0)).choose_spec.1⟩⟩
  choose! x hx using hpieces
  have hfr : ∀ k ≤ n, (b3Rest2_frac n k : ℝ) = (k : ℝ) / n := fun k hk ↦ b3Rest2_frac_coe hk hn
  rw [b3Rest2_P_eq_sum ψ g hn, Rat.cast_sum]
  set Φ : ℕ → ℝ := fun k ↦ F (g (b3Rest2_frac n k)) + U.G ψ (g (b3Rest2_frac n k))
  have hpiece : ∀ k ∈ Finset.range n,
      ((b3Rest2_P ψ.1 (b3Rest2_restr g (b3Rest2_frac n k) (b3Rest2_frac n (k + 1))) : ℚ) : ℝ) =
        Φ (k + 1) - Φ k := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hle : (b3Rest2_frac n k : ℝ) ≤ b3Rest2_frac n (k + 1) := by
      rw [hfr k hk'.le, hfr (k + 1) hk']; gcongr; push_cast; linarith
    have hin : ∀ t : unitInterval, (t : ℝ) ∈ Icc (b3Rest2_frac n k : ℝ) (b3Rest2_frac n (k + 1)) →
        g t ∈ K.O (x k) := fun t ht ↦ hx k hk' t (by
          rw [hfr k hk'.le, hfr (k + 1) hk'] at ht; push_cast at ht; exact ht)
    rw [U.P_piece ψ g _ _ hle hin]
    have hc := U.h_sub_F_const ψ hF hαF (hin _ ⟨le_rfl, hle⟩) (hin _ ⟨hle, le_rfl⟩)
    simp only [Φ]
    linarith
  rw [Finset.sum_congr rfl hpiece, Finset.sum_range_sub]
  have h0 : b3Rest2_frac n 0 = 0 := by simp [b3Rest2_frac]
  have h1 : b3Rest2_frac n n = 1 := by
    apply Subtype.ext
    rw [hfr n le_rfl, div_self (by exact_mod_cast hn.ne')]
    rfl
  simp only [Φ, h0, h1]

/-- **If the closed form of the cocycle is exact, the cocycle is a coboundary**, hence its class
vanishes. -/
theorem cohomologyClass_eq_zero_of_exact [ConnectedSpace C] {F : C → ℝ}
    (hF : b3Forms_IsSmooth (b3Forms_fun (E := E) F))
    (hαF : U.α ψ = b3Forms_d (b3Forms_fun (E := E) F)) :
    Singular.cohomologyClass (TopCat.of C) 1 ψ = 0 := by
  obtain ⟨x₀⟩ := (inferInstance : ConnectedSpace C).toNonempty
  -- paths from the base point
  have hpath : ∀ q : C, ∃ g : C(unitInterval, C), g 0 = x₀ ∧ g 1 = q := by
    intro q
    obtain ⟨γ, hγ, h0, h1⟩ := b3Forms_reachable (E := E) x₀ q
    exact ⟨⟨fun t ↦ γ t, hγ.1.continuous.comp continuous_subtype_val⟩, h0, h1⟩
  choose gp hgp0 hgp1 using hpath
  set η : AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj (TopCat.of C)) 0 :=
    simplexCochain ℚ _ 0 fun v ↦ b3Rest2_P ψ.1 (gp (TopCat.toSSetObj₀Equiv v))
  have hpt : ∀ (σ : (TopCat.toSSet.obj (TopCat.of C)) _⦋1⦌) (i : Fin 2),
      TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of C)).δ i σ) =
        simplexPath σ (if i = 0 then 1 else 0) := by
    intro σ i
    simp only [TopCat.toSSetObj₀Equiv_apply, simplexPath, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk]
    erw [TopCat.toSSetObjEquiv_δ_apply]
    congr 1
    have hd : (default : Convexity.StdSimplex ℝ (Fin 1)) = Convexity.StdSimplex.single 0 := by
      apply Convexity.StdSimplex.ext
      refine Finsupp.ext fun j ↦ ?_
      fin_cases j
      simp [Convexity.StdSimplex.weights_apply_eq_one]
    rw [hd, Convexity.StdSimplex.map_single]
    fin_cases i
    · simp only [Fin.zero_eta, ite_true, Convexity.StdSimplex.homeomorphI_symm_one]
      rfl
    · simp only [Fin.mk_one, one_ne_zero, ite_false, Convexity.StdSimplex.homeomorphI_symm_zero]
      rfl
  have hcob : ψ.1 = AlgebraicTopology.Simplicial.coboundary ℚ 0 η := by
    refine cochain_ext_simplex_b3Rest2 _ _ fun σ ↦ ?_
    rw [AlgebraicTopology.Simplicial.coboundary_chainOfSimplex, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
      neg_one_smul, η, spec_simplexCochain_chainOfSimplex_aux, hpt]
    rw [if_pos trivial, if_neg (by decide)]
    apply Rat.cast_injective (α := ℝ)
    push_cast
    rw [b3Rest2_P_simplexPath, U.P_eq_of_exact ψ hF hαF, U.P_eq_of_exact ψ hF hαF,
      U.P_eq_of_exact ψ hF hαF, hgp0, hgp1, hgp0, hgp1]
    ring
  apply (AlgebraicTopology.Singular.cohomologyEquivDualHomology ℚ (TopCat.of C) 1).injective
  rw [map_zero]
  ext z
  obtain ⟨c, rfl⟩ :=
    CategoryTheory.ShortComplex.moduleCatHomologyClass_surjective
      ((AlgebraicTopology.Singular.SingularChainComplex ℚ (TopCat.of C)).sc 1) z
  rw [cohomologyEquivDualHomology_cohomologyClass]
  show ψ.1 c.1 = 0
  rw [hcob]
  show η (AlgebraicTopology.Simplicial.boundary ℚ 0 c.1) = 0
  have hc : AlgebraicTopology.Simplicial.boundary ℚ 0 c.1 = 0 := by
    have h0 : (((TopCat.toSSet.obj (TopCat.of C)).chainComplex (ModuleCat.of ℚ ℚ)).d 1
        ((ComplexShape.down ℕ).next 1)).hom c.1 = 0 := c.2
    rw [ChainComplex.next_nat_succ] at h0
    exact h0
  rw [hc, map_zero]

end b3Rest2_PoU

end Form

end HodgeLean.Foundations.Program
