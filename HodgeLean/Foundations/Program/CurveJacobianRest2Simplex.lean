import HodgeLean.Adapters.HolomorphicPeriodsCocycleProofs

/-! # Track B3, lane Rest2: rational `1`-cocycles on paths

A path `g : [0, 1] → T` is a singular `1`-simplex (`b3Rest2_pathSimplex`), and a continuous map
from the standard `2`-simplex is a singular `2`-simplex whose faces are read off by restriction
(`b3Rest2_face`). For a singular `1`-cocycle `ψ`, `P(g) = ψ(g)`:
* `b3Rest2_cocycle_tri`: `ψ(∂₀τ) - ψ(∂₁τ) + ψ(∂₂τ) = 0` for every `2`-simplex `τ`;
* `b3Rest2_subdiv`: `P(g|[a, c]) = P(g|[a, b]) + P(g|[b, c])`, from the `2`-simplex
  `w ↦ g(w₀ a + w₁ b + w₂ c)`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory Set Convexity Filter
open scoped Simplicial Topology

namespace HodgeLean.Foundations.Program

open HodgeLean.Adapters

variable {T : Type} [TopologicalSpace T]

/-- **The singular `1`-simplex of a path** `g : [0, 1] → T`. -/
def b3Rest2_pathSimplex (g : C(unitInterval, T)) : (TopCat.toSSet.obj (TopCat.of T)) _⦋1⦌ :=
  ((TopCat.of T).toSSetObjEquiv _).symm
    (g.comp ⟨StdSimplex.homeomorphI, StdSimplex.homeomorphI.continuous⟩)

theorem b3Rest2_simplexPath_pathSimplex (g : C(unitInterval, T)) :
    simplexPath (b3Rest2_pathSimplex g) = g := by
  ext t
  simp [simplexPath, b3Rest2_pathSimplex]

theorem b3Rest2_pathSimplex_simplexPath (σ : (TopCat.toSSet.obj (TopCat.of T)) _⦋1⦌) :
    b3Rest2_pathSimplex (simplexPath σ) = σ := by
  apply ((TopCat.of T).toSSetObjEquiv _).injective
  ext w
  simp [simplexPath, b3Rest2_pathSimplex]

/-- **The singular `2`-simplex of a map from the standard `2`-simplex.** -/
def b3Rest2_triSimplex (f : C(StdSimplex ℝ (Fin 3), T)) :
    (TopCat.toSSet.obj (TopCat.of T)) _⦋2⦌ :=
  ((TopCat.of T).toSSetObjEquiv _).symm f

theorem b3Rest2_face (f : C(StdSimplex ℝ (Fin 3), T)) (i : Fin 3) (t : unitInterval) :
    simplexPath ((TopCat.toSSet.obj (TopCat.of T)).δ i (b3Rest2_triSimplex f)) t =
      f (StdSimplex.map i.succAbove (StdSimplex.homeomorphI.symm t)) := by
  simp only [simplexPath, b3Rest2_triSimplex, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  erw [TopCat.toSSetObjEquiv_δ_apply]

theorem b3Rest2_weights_one (t : unitInterval) :
    (StdSimplex.homeomorphI.symm t).weights 1 = t := by
  have := StdSimplex.homeomorphI_apply_coe (StdSimplex.homeomorphI.symm t)
  rw [Homeomorph.apply_symm_apply] at this
  exact this.symm

theorem b3Rest2_weights_zero (t : unitInterval) :
    (StdSimplex.homeomorphI.symm t).weights 0 = 1 - t := by
  have := StdSimplex.total_fin_two (StdSimplex.homeomorphI.symm t)
  rw [b3Rest2_weights_one] at this
  linarith

/-- The weights of the faces of the standard `2`-simplex at the point with parameter `t`. -/
theorem b3Rest2_face_weights (t : unitInterval) :
    ((StdSimplex.map (0 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)).weights 0 = 0 ∧
      (StdSimplex.map (0 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)).weights 1 = 1 - t ∧
      (StdSimplex.map (0 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)).weights 2 = t) ∧
    ((StdSimplex.map (1 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)).weights 0 = 1 - t ∧
      (StdSimplex.map (1 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)).weights 1 = 0 ∧
      (StdSimplex.map (1 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)).weights 2 = t) ∧
    ((StdSimplex.map (2 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)).weights 0 = 1 - t ∧
      (StdSimplex.map (2 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)).weights 1 = t ∧
      (StdSimplex.map (2 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)).weights 2 = 0) := by
  have h0 := b3Rest2_weights_zero t
  have h1 := b3Rest2_weights_one t
  have hinj : ∀ i : Fin 3, Function.Injective i.succAbove := fun i ↦ Fin.succAbove_right_injective
  have hm : ∀ (i : Fin 3) (k : Fin 2), (StdSimplex.map i.succAbove
      (StdSimplex.homeomorphI.symm t)).weights (i.succAbove k) =
        (StdSimplex.homeomorphI.symm t).weights k := fun i k ↦ by
    rw [StdSimplex.weights_map]
    exact Finsupp.mapDomain_apply_of_injective (hinj i) _ k
  have hz : ∀ i : Fin 3, (StdSimplex.map i.succAbove
      (StdSimplex.homeomorphI.symm t)).weights i = 0 := fun i ↦ by
    rw [StdSimplex.weights_map, Finsupp.mapDomain_of_notMem_range]
    rintro ⟨k, hk⟩
    exact Fin.succAbove_ne i k hk
  refine ⟨⟨hz 0, ?_, ?_⟩, ⟨?_, hz 1, ?_⟩, ⟨?_, ?_, hz 2⟩⟩
  · rw [show (1 : Fin 3) = (0 : Fin 3).succAbove 0 from rfl, hm, h0]
  · rw [show (2 : Fin 3) = (0 : Fin 3).succAbove 1 from rfl, hm, h1]
  · rw [show (0 : Fin 3) = (1 : Fin 3).succAbove 0 from rfl, hm, h0]
  · rw [show (2 : Fin 3) = (1 : Fin 3).succAbove 1 from rfl, hm, h1]
  · rw [show (0 : Fin 3) = (2 : Fin 3).succAbove 0 from rfl, hm, h0]
  · rw [show (1 : Fin 3) = (2 : Fin 3).succAbove 1 from rfl, hm, h1]

variable {R : Type} [CommRing R]

/-- **The cocycle relation on a `2`-simplex.** -/
theorem b3Rest2_cocycle_tri
    (ψ : AlgebraicTopology.Simplicial.Cocycle R (TopCat.toSSet.obj (TopCat.of T)) 1)
    (τ : (TopCat.toSSet.obj (TopCat.of T)) _⦋2⦌) :
    ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex R
        ((TopCat.toSSet.obj (TopCat.of T)).δ 0 τ)) -
      ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex R
        ((TopCat.toSSet.obj (TopCat.of T)).δ 1 τ)) +
      ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex R
        ((TopCat.toSSet.obj (TopCat.of T)).δ 2 τ)) = 0 := by
  have h := LinearMap.congr_fun (LinearMap.mem_ker.1 ψ.2)
    (AlgebraicTopology.Simplicial.chainOfSimplex R τ)
  rw [AlgebraicTopology.Simplicial.coboundary_chainOfSimplex] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, LinearMap.zero_apply] at h
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.val_zero, Fin.val_one, Fin.val_two,
    Fin.val_succ, pow_zero, pow_one, one_smul, neg_one_sq, neg_smul, add_zero] at h
  linear_combination h

/-- The value of a cochain on the simplex of a path. -/
def b3Rest2_P (ψ : AlgebraicTopology.Simplicial.Cochain R (TopCat.toSSet.obj (TopCat.of T)) 1)
    (g : C(unitInterval, T)) : R :=
  ψ (AlgebraicTopology.Simplicial.chainOfSimplex R (b3Rest2_pathSimplex g))

theorem b3Rest2_P_simplexPath
    (ψ : AlgebraicTopology.Simplicial.Cochain R (TopCat.toSSet.obj (TopCat.of T)) 1)
    (σ : (TopCat.toSSet.obj (TopCat.of T)) _⦋1⦌) :
    ψ (AlgebraicTopology.Simplicial.chainOfSimplex R σ) = b3Rest2_P ψ (simplexPath σ) := by
  rw [b3Rest2_P, b3Rest2_pathSimplex_simplexPath]

/-- **The cocycle relation for a map from the standard `2`-simplex**, through its three edge
paths. -/
theorem b3Rest2_cocycle_map
    (ψ : AlgebraicTopology.Simplicial.Cocycle R (TopCat.toSSet.obj (TopCat.of T)) 1)
    (f : C(StdSimplex ℝ (Fin 3), T)) (g₀ g₁ g₂ : C(unitInterval, T))
    (h₀ : ∀ t, f (StdSimplex.map (0 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)) = g₀ t)
    (h₁ : ∀ t, f (StdSimplex.map (1 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)) = g₁ t)
    (h₂ : ∀ t, f (StdSimplex.map (2 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)) = g₂ t) :
    b3Rest2_P ψ.1 g₀ - b3Rest2_P ψ.1 g₁ + b3Rest2_P ψ.1 g₂ = 0 := by
  have h := b3Rest2_cocycle_tri ψ (b3Rest2_triSimplex f)
  rw [b3Rest2_P_simplexPath, b3Rest2_P_simplexPath, b3Rest2_P_simplexPath] at h
  have e : ∀ i : Fin 3, ∀ g : C(unitInterval, T),
      (∀ t, f (StdSimplex.map i.succAbove (StdSimplex.homeomorphI.symm t)) = g t) →
      simplexPath ((TopCat.toSSet.obj (TopCat.of T)).δ i (b3Rest2_triSimplex f)) = g :=
    fun i g hg ↦ ContinuousMap.ext fun t ↦ (b3Rest2_face f i t).trans (hg t)
  rwa [e 0 g₀ h₀, e 1 g₁ h₁, e 2 g₂ h₂] at h

/-! ## Subdivision of paths -/

/-- The point `a + t (b - a)` of `[0, 1]`. -/
def b3Rest2_affI (a b : unitInterval) (t : unitInterval) : unitInterval :=
  ⟨(a : ℝ) + t * (b - a), by
    obtain ⟨ha0, ha1⟩ := a.2
    obtain ⟨hb0, hb1⟩ := b.2
    obtain ⟨ht0, ht1⟩ := t.2
    constructor <;> nlinarith⟩

theorem b3Rest2_continuous_affI (a b : unitInterval) : Continuous (b3Rest2_affI a b) := by
  unfold b3Rest2_affI
  fun_prop

/-- **The restriction of a path to `[a, b]`**, reparametrized by `[0, 1]`. -/
def b3Rest2_restr (g : C(unitInterval, T)) (a b : unitInterval) : C(unitInterval, T) :=
  g.comp ⟨b3Rest2_affI a b, b3Rest2_continuous_affI a b⟩

theorem b3Rest2_restr_apply (g : C(unitInterval, T)) (a b t : unitInterval) :
    b3Rest2_restr g a b t = g (b3Rest2_affI a b t) := rfl

/-- The point `w₀ a + w₁ b + w₂ c` of `[0, 1]`. -/
def b3Rest2_bary (a b c : unitInterval) (w : StdSimplex ℝ (Fin 3)) : unitInterval :=
  ⟨w.weights 0 * a + w.weights 1 * b + w.weights 2 * c, by
    have hs := w.total_of_fintype
    rw [Fin.sum_univ_three] at hs
    have h0 := w.weights_nonneg 0
    have h1 := w.weights_nonneg 1
    have h2 := w.weights_nonneg 2
    obtain ⟨ha0, ha1⟩ := a.2
    obtain ⟨hb0, hb1⟩ := b.2
    obtain ⟨hc0, hc1⟩ := c.2
    constructor <;> nlinarith⟩

theorem b3Rest2_continuous_bary (a b c : unitInterval) : Continuous (b3Rest2_bary a b c) := by
  unfold b3Rest2_bary
  have h0 := StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 0
  have h1 := StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 1
  have h2 := StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 2
  fun_prop

/-- **Subdivision**: `P(g|[a, c]) = P(g|[a, b]) + P(g|[b, c])`. -/
theorem b3Rest2_subdiv
    (ψ : AlgebraicTopology.Simplicial.Cocycle R (TopCat.toSSet.obj (TopCat.of T)) 1)
    (g : C(unitInterval, T)) (a b c : unitInterval) :
    b3Rest2_P ψ.1 (b3Rest2_restr g a c) =
      b3Rest2_P ψ.1 (b3Rest2_restr g a b) + b3Rest2_P ψ.1 (b3Rest2_restr g b c) := by
  have h := b3Rest2_cocycle_map ψ (g.comp ⟨b3Rest2_bary a b c, b3Rest2_continuous_bary a b c⟩)
    (b3Rest2_restr g b c) (b3Rest2_restr g a c) (b3Rest2_restr g a b) ?_ ?_ ?_
  · linear_combination -h
  all_goals
    intro t
    obtain ⟨⟨w00, w01, w02⟩, ⟨w10, w11, w12⟩, ⟨w20, w21, w22⟩⟩ := b3Rest2_face_weights t
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, b3Rest2_restr_apply]
    congr 1
    apply Subtype.ext
    simp only [b3Rest2_bary, b3Rest2_affI, w00, w01, w02, w10, w11, w12, w20, w21, w22]
    ring

/-! ## Cones in a convex chart region -/

section Cone

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem b3Rest2_continuous_cone {X : Type*} [TopologicalSpace X] {a b : X → ℝ}
    (ha : Continuous a) (hb : Continuous b) (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x)
    {V : unitInterval → E} (hV : Continuous V) :
    Continuous (fun x ↦ (a x + b x) • V (Set.projIcc 0 1 zero_le_one (b x / (a x + b x)))) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases h : a x + b x = 0
  · obtain ⟨M, hM⟩ := (isCompact_univ.image hV).isBounded.exists_norm_le
    have hM' : ∀ t, ‖V t‖ ≤ M := fun t ↦ hM _ ⟨t, trivial, rfl⟩
    show Tendsto _ (𝓝 x) (𝓝 _)
    beta_reduce
    rw [h, zero_smul]
    refine squeeze_zero_norm (a := fun y ↦ (a y + b y) * M) (fun y ↦ ?_) ?_
    · rw [norm_smul, Real.norm_of_nonneg (add_nonneg (ha0 y) (hb0 y))]
      exact mul_le_mul_of_nonneg_left (hM' _) (add_nonneg (ha0 y) (hb0 y))
    · have : Tendsto (fun y ↦ (a y + b y) * M) (𝓝 x) (𝓝 ((a x + b x) * M)) :=
        ((ha.add hb).mul continuous_const).continuousAt
      rwa [h, zero_mul] at this
  · exact ((ha.add hb).continuousAt).smul (hV.continuousAt.comp
      (continuous_projIcc.continuousAt.comp (hb.continuousAt.div (ha.add hb).continuousAt h)))

variable (e : OpenPartialHomeomorph T E) {U : Set E} (hU : Convex ℝ U) (hUt : U ⊆ e.target)
include hU hUt

theorem b3Rest2_seg_mem {u v : E} (hu : u ∈ U) (hv : v ∈ U) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    u + s • (v - u) ∈ U :=
  hU.add_smul_sub_mem hu hv hs

/-- **The chart segment** from `u` to `v` in a convex region of the chart image. -/
def b3Rest2_seg {u v : E} (hu : u ∈ U) (hv : v ∈ U) : C(unitInterval, T) :=
  ⟨fun t ↦ e.symm (u + (t : ℝ) • (v - u)), by
    refine e.continuousOn_symm.comp_continuous (by fun_prop) fun t ↦ hUt ?_
    exact b3Rest2_seg_mem e hU hUt hu hv t t.2⟩

theorem b3Rest2_seg_apply {u v : E} (hu : u ∈ U) (hv : v ∈ U) (t : unitInterval) :
    b3Rest2_seg e hU hUt hu hv t = e.symm (u + (t : ℝ) • (v - u)) := rfl

/-- **The cone identity**: for a path `g` in a convex chart region and a centre `u` of the
region, `P(g) = P([u, g 1]) - P([u, g 0])` for the chart segments from `u`. -/
theorem b3Rest2_cone
    (ψ : AlgebraicTopology.Simplicial.Cocycle R (TopCat.toSSet.obj (TopCat.of T)) 1)
    {u : E} (hu : u ∈ U) (g : C(unitInterval, T)) (hgs : ∀ t, g t ∈ e.source)
    (hgU : ∀ t, e (g t) ∈ U) :
    b3Rest2_P ψ.1 g = b3Rest2_P ψ.1 (b3Rest2_seg e hU hUt hu (hgU 1)) -
      b3Rest2_P ψ.1 (b3Rest2_seg e hU hUt hu (hgU 0)) := by
  set V : unitInterval → E := fun t ↦ e (g t) - u
  have hV : Continuous V :=
    (e.continuousOn.comp_continuous g.continuous hgs).sub continuous_const
  set w1 : StdSimplex ℝ (Fin 3) → ℝ := fun w ↦ w.weights 1
  set w2 : StdSimplex ℝ (Fin 3) → ℝ := fun w ↦ w.weights 2
  have hw1 : Continuous w1 := StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 1
  have hw2 : Continuous w2 := StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 2
  set Φ : StdSimplex ℝ (Fin 3) → E := fun w ↦
    (w1 w + w2 w) • V (Set.projIcc 0 1 zero_le_one (w2 w / (w1 w + w2 w)))
  have hΦ : Continuous Φ := b3Rest2_continuous_cone hw1 hw2 (fun w ↦ w.weights_nonneg 1)
    (fun w ↦ w.weights_nonneg 2) hV
  have hmem : ∀ w : StdSimplex ℝ (Fin 3), u + Φ w ∈ U := by
    intro w
    have hs := w.total_of_fintype
    rw [Fin.sum_univ_three] at hs
    have h12 : w1 w + w2 w ∈ Icc (0 : ℝ) 1 :=
      ⟨add_nonneg (w.weights_nonneg 1) (w.weights_nonneg 2), by
        have := w.weights_nonneg 0; simp only [w1, w2]; linarith⟩
    exact hU.add_smul_sub_mem hu (hgU _) h12
  let f : C(StdSimplex ℝ (Fin 3), T) :=
    ⟨fun w ↦ e.symm (u + Φ w), e.continuousOn_symm.comp_continuous (continuous_const.add hΦ)
      fun w ↦ hUt (hmem w)⟩
  have h := b3Rest2_cocycle_map ψ f g (b3Rest2_seg e hU hUt hu (hgU 1))
    (b3Rest2_seg e hU hUt hu (hgU 0)) ?_ ?_ ?_
  · linear_combination h
  all_goals
    intro t
    obtain ⟨⟨w00, w01, w02⟩, ⟨w10, w11, w12⟩, ⟨w20, w21, w22⟩⟩ := b3Rest2_face_weights t
    simp only [f, ContinuousMap.coe_mk, Φ, w1, w2, V, b3Rest2_seg_apply]
  · rw [w01, w02, sub_add_cancel, div_one, one_smul, Set.projIcc_of_mem _ t.2]
    rw [show (⟨(t : ℝ), t.2⟩ : Icc (0 : ℝ) 1) = t from rfl, add_sub_cancel, e.left_inv (hgs t)]
  · rw [w11, w12, zero_add]
    by_cases ht : (t : ℝ) = 0
    · rw [ht, zero_smul, zero_smul]
    · rw [div_self ht, Set.projIcc_right]
      rfl
  · rw [w21, w22, add_zero, zero_div, Set.projIcc_left]
    rfl

end Cone

/-! ## Subdivision into many pieces -/

/-- The point `k / n` of `[0, 1]` (clamped). -/
def b3Rest2_frac (n k : ℕ) : unitInterval := Set.projIcc 0 1 zero_le_one ((k : ℝ) / n)

theorem b3Rest2_frac_coe {n k : ℕ} (hk : k ≤ n) (hn : 0 < n) :
    (b3Rest2_frac n k : ℝ) = (k : ℝ) / n := by
  rw [b3Rest2_frac, Set.projIcc_of_mem]
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by exact_mod_cast hn)]
  exact_mod_cast hk

theorem b3Rest2_P_restr_self
    (ψ : AlgebraicTopology.Simplicial.Cocycle R (TopCat.toSSet.obj (TopCat.of T)) 1)
    (g : C(unitInterval, T)) (a : unitInterval) : b3Rest2_P ψ.1 (b3Rest2_restr g a a) = 0 := by
  have := b3Rest2_subdiv ψ g a a a
  linear_combination -this

theorem b3Rest2_restr_zero_one (g : C(unitInterval, T)) : b3Rest2_restr g 0 1 = g := by
  ext t
  simp only [b3Rest2_restr_apply]
  congr 1
  apply Subtype.ext
  simp [b3Rest2_affI]

/-- **The value on a path is the sum of the values on `n` consecutive pieces.** -/
theorem b3Rest2_P_eq_sum
    (ψ : AlgebraicTopology.Simplicial.Cocycle R (TopCat.toSSet.obj (TopCat.of T)) 1)
    (g : C(unitInterval, T)) {n : ℕ} (hn : 0 < n) :
    b3Rest2_P ψ.1 g = ∑ k ∈ Finset.range n,
      b3Rest2_P ψ.1 (b3Rest2_restr g (b3Rest2_frac n k) (b3Rest2_frac n (k + 1))) := by
  have key : ∀ m ≤ n, b3Rest2_P ψ.1 (b3Rest2_restr g 0 (b3Rest2_frac n m)) = ∑ k ∈ Finset.range m,
      b3Rest2_P ψ.1 (b3Rest2_restr g (b3Rest2_frac n k) (b3Rest2_frac n (k + 1))) := by
    intro m hm
    induction m with
    | zero =>
      have h0 : b3Rest2_frac n 0 = 0 := by simp [b3Rest2_frac]
      rw [h0, b3Rest2_P_restr_self, Finset.sum_range_zero]
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih (by omega), ← b3Rest2_subdiv]
  have h := key n le_rfl
  have h1 : b3Rest2_frac n n = 1 := by
    apply Subtype.ext
    rw [b3Rest2_frac_coe le_rfl hn, div_self (by exact_mod_cast hn.ne')]
    rfl
  rwa [h1, b3Rest2_restr_zero_one] at h

theorem b3Rest2_affI_mem {a b : unitInterval} (hab : (a : ℝ) ≤ b) (t : unitInterval) :
    (b3Rest2_affI a b t : ℝ) ∈ Set.Icc (a : ℝ) b := by
  simp only [b3Rest2_affI]
  obtain ⟨ht0, ht1⟩ := t.2
  constructor <;> nlinarith

/-- **A Lebesgue number for a path and an open cover.** -/
theorem b3Rest2_exists_pieces {ι : Type*} (g : C(unitInterval, T)) (U : ι → Set T)
    (hU : ∀ i, IsOpen (U i)) (hcov : ∀ p, ∃ i, p ∈ U i) :
    ∃ n : ℕ, 0 < n ∧ ∀ k < n, ∃ i, ∀ t : unitInterval,
      (t : ℝ) ∈ Set.Icc ((k : ℝ) / n) ((k + 1 : ℝ) / n) → g t ∈ U i := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun i ↦ (hU i).preimage g.continuous) (fun t _ ↦ mem_iUnion.2 (hcov (g t)))
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n + 1, by omega, fun k hk ↦ ?_⟩
  have hk' : (k : ℝ) / (n + 1 : ℕ) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    exact_mod_cast hk.le
  obtain ⟨i, hi⟩ := hball ⟨_, hk'⟩ trivial
  refine ⟨i, fun t ht ↦ hi ?_⟩
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
  have hN : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have h1 : ((k + 1 : ℝ) / (n + 1 : ℕ)) - (k : ℝ) / (n + 1 : ℕ) = 1 / (n + 1 : ℕ) := by
    field_simp; ring
  have h2 : (1 : ℝ) / (n + 1 : ℕ) ≤ 1 / (n + 1) := by push_cast; rfl
  rw [abs_of_nonneg (by simp only; linarith [ht.1])]
  simp only
  linarith [ht.2]

end HodgeLean.Foundations.Program
