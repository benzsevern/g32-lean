import HodgeLean.Foundations.Program.RelativeFrameGate
import HodgeLean.Foundations.Program.CurveJacobianDefs

/-! # The full-overlap operator: definitions for stage C
The root map and sector coefficients of the plumbing description, the explicit sector operator
between fixed bounded holomorphic spaces, the outer data of a plumbed surface (a finite piece
cover containing one annulus piece per disc), the operator `δ_ε` on the full overlap, the
plumbing datum of one fibre (disc coordinates glued to the annulus pieces by the root map), and
the gluing of overlap data into a function on the tangent bundle.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program
local instance rf4_decidableDefs (p : Prop) : Decidable p := Classical.propDecidable p

/-! ## Coordinates of the plumbing description -/

/-- The gluing map `Φ_ε(u) = u (1 − ε u⁻ⁿ)^{1/n}`, principal branch. On the annulus
`A_n = {r < |u|ⁿ < 2r}` with `|ε| < r` it is the moving root `w_t` in terms of the base root `u`.
Source: `docs/specs/RelativeFrame.md`, §4.1 item 3; Ahlfors, *Complex Analysis*, 3rd ed.,
Ch. 3, §4 (principal branch of the power). -/
def rf4_rootMap (n : ℕ) (ε u : ℂ) : ℂ :=
  u * (1 - ε * u ^ (-(n : ℤ))) ^ ((n : ℂ)⁻¹)

example (n : ℕ) (u : ℂ) : rf4_rootMap n 0 u = u := by simp [rf4_rootMap]

/-- The sector exponent `s_j = (j + 1)/n − 1`, which lies in `(−1, 0]` for `j < n`.
Source: `docs/specs/RelativeFrame.md`, §4.2 (sector map). -/
def rf4_sectorExp (n : ℕ) (j : Fin n) : ℂ :=
  ((j : ℂ) + 1) / n - 1

example : rf4_sectorExp 2 1 = 0 := by norm_num [rf4_sectorExp]

/-- The `w`-coefficient `n Σ_{j<n} wʲ g_j(τ + wⁿ)` of the sector form `B_{t,x} g` on the moving
disc, with `τ = t_i` the moving branch value.
Source: `docs/specs/RelativeFrame.md`, §4.2 (sector map); Forster, *Lectures on Riemann
Surfaces*, §9. -/
def rf4_sectorCoeff (n : ℕ) (g : Fin n → ℂ → ℂ) (τ w : ℂ) : ℂ :=
  n * ∑ j : Fin n, w ^ (j : ℕ) * g j (τ + w ^ n)

example (g : Fin 1 → ℂ → ℂ) (τ w : ℂ) : rf4_sectorCoeff 1 g τ w = g 0 (τ + w) := by
  simp [rf4_sectorCoeff]

/-- The moving disc `D_w(ε) = {w : |wⁿ + ε| < 2r}`, the image of the inner piece `Δ_x` under the
moving root coordinate. It is invariant under `w ↦ ζw` for `ζⁿ = 1`.
Source: `docs/specs/RelativeFrame.md`, §4.1 item 2 (B8f) and §4.2 (kernel). -/
def rf4_innerDisc (n : ℕ) (r : ℝ) (ε : ℂ) : Set ℂ :=
  {w | ‖w ^ n + ε‖ < 2 * r}

example : (0 : ℂ) ∈ rf4_innerDisc 2 1 (1 / 2) := by
  norm_num [rf4_innerDisc, Complex.norm_div]

/-- The parameter polydisc `{ε : |ε_x| < r for every disc x}` of the moving branch values.
Source: `docs/specs/RelativeFrame.md`, §4.1 (notation, `|ε_i| < r`); `b6t_polydisc`. -/
def rf4_polydisc (m : ℕ) (r : ℝ) : Set (Fin m → ℂ) :=
  {ε | ∀ x, ‖ε x‖ < r}

example : (0 : Fin 3 → ℂ) ∈ rf4_polydisc 3 1 := fun _ ↦ by simp

/-- The closed annulus `{r ≤ |u|ⁿ ≤ 2r}`, on which the multipliers of the sector operator are
continuous.
Source: `docs/specs/RelativeFrame.md`, §4.2 (boundedness). -/
def rf4_closedAnnulus (n : ℕ) (r : ℝ) : Set ℂ :=
  {u | r ≤ ‖u‖ ^ n ∧ ‖u‖ ^ n ≤ 2 * r}

example : (1 : ℂ) ∈ rf4_closedAnnulus 2 1 := by norm_num [rf4_closedAnnulus]

/-- Zero extension to `ℂ` of a bounded holomorphic function on `U`.
Source: `b63r_bddHol`; RelativeFrame §4.2. -/
def rf4_extendBdd {U : Set ℂ} (f : b63r_bddHol U) (z : ℂ) : ℂ :=
  if h : z ∈ U then (f : U →ᵇ ℂ) ⟨z, h⟩ else 0

example {U : Set ℂ} (f : b63r_bddHol U) (z : U) : rf4_extendBdd f z = (f : U →ᵇ ℂ) z := by
  simp [rf4_extendBdd, z.2]

/-! ## Bounded holomorphic multipliers -/

/-- The closed annulus is compact for `n ≥ 1`. -/
theorem rf4_closedAnnulus_isCompact {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    IsCompact (rf4_closedAnnulus n r) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_le continuous_const (continuous_norm.pow n)).inter
      (isClosed_le (continuous_norm.pow n) continuous_const)
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨max 1 (2 * r), fun u hu ↦ ?_⟩
    by_cases h1 : ‖u‖ ≤ 1
    · exact h1.trans (le_max_left _ _)
    · push Not at h1
      have : ‖u‖ ≤ ‖u‖ ^ n := by
        calc ‖u‖ = ‖u‖ ^ 1 := (pow_one _).symm
          _ ≤ ‖u‖ ^ n := pow_le_pow_right₀ h1.le hn
      exact (this.trans hu.2).trans (le_max_right _ _)

/-- The open annulus lies in the closed one. -/
theorem rf4_annulus_subset_closed (n : ℕ) (r : ℝ) :
    b63r_annulus n r ⊆ rf4_closedAnnulus n r :=
  fun _ hu ↦ ⟨hu.1.le, hu.2.le⟩

/-- The annulus is open. -/
theorem rf4_annulus_isOpen (n : ℕ) (r : ℝ) : IsOpen (b63r_annulus n r) :=
  (isOpen_lt continuous_const (continuous_norm.pow n)).inter
    (isOpen_lt (continuous_norm.pow n) continuous_const)

/-- The closed annulus avoids `0` for `n ≥ 1` and `r > 0`. -/
theorem rf4_closedAnnulus_ne_zero {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) {u : ℂ}
    (hu : u ∈ rf4_closedAnnulus n r) : u ≠ 0 := by
  rintro rfl
  have := hu.1
  rw [norm_zero, zero_pow (by omega)] at this
  linarith

/-- On the closed annulus, `1 − εu⁻ⁿ` lies in the slit plane when `|ε| < r`. -/
theorem rf4_slit {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) {ε : ℂ} (hε : ‖ε‖ < r) {u : ℂ}
    (hu : u ∈ rf4_closedAnnulus n r) : 1 - ε * u ^ (-(n : ℤ)) ∈ Complex.slitPlane := by
  have hu0 := rf4_closedAnnulus_ne_zero hn hr hu
  have hpos : 0 < ‖u‖ ^ n := pow_pos (norm_pos_iff.mpr hu0) n
  have hnorm : ‖-(ε * u ^ (-(n : ℤ)))‖ < 1 := by
    rw [norm_neg, norm_mul, norm_zpow, zpow_neg, zpow_natCast, ← div_eq_mul_inv,
      div_lt_one hpos]
    exact hε.trans_le hu.1
  simpa [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hnorm

/-- The sector multiplier `u ↦ uʲ (1 − ε u⁻ⁿ)^{s_j}`, principal branch.
Source: `docs/specs/RelativeFrame.md`, §4.2 (differential pullback, `S_x(ε)`). -/
def rf4_multiplierFun (n : ℕ) (ε : ℂ) (j : Fin n) (u : ℂ) : ℂ :=
  u ^ (j : ℕ) * (1 - ε * u ^ (-(n : ℤ))) ^ rf4_sectorExp n j

example (u : ℂ) : rf4_multiplierFun 1 0 0 u = 1 := by
  simp [rf4_multiplierFun, rf4_sectorExp]

/-- The sector multiplier is holomorphic near the closed annulus. -/
theorem rf4_multiplierFun_differentiableAt {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) {ε : ℂ}
    (hε : ‖ε‖ < r) (j : Fin n) {u : ℂ} (hu : u ∈ rf4_closedAnnulus n r) :
    DifferentiableAt ℂ (rf4_multiplierFun n ε j) u := by
  have hu0 := rf4_closedAnnulus_ne_zero hn hr hu
  unfold rf4_multiplierFun
  exact (differentiableAt_pow _).mul (((differentiableAt_const _).sub
    ((differentiableAt_const _).mul (differentiableAt_zpow.mpr (Or.inl hu0)))).cpow_const
      (rf4_slit hn hr hε hu))

/-- A function continuous on a compact `K ⊇ U` and holomorphic on `U`, as a bounded holomorphic
function on `U`.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Ch. 17; a continuous function on a
compact set is bounded. -/
def rf4_bddOn {U K : Set ℂ} (hK : IsCompact K) (hUK : U ⊆ K) (f : ℂ → ℂ)
    (hf : ContinuousOn f K) (hd : DifferentiableOn ℂ f U) : b63r_bddHol U :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroup (fun z : U ↦ f z) ((hf.mono hUK).domRestrict)
    (Classical.choose (hK.exists_bound_of_continuousOn hf))
    (fun z ↦ Classical.choose_spec (hK.exists_bound_of_continuousOn hf) z (hUK z.2)),
    ⟨f, hd, fun _ ↦ rfl⟩⟩

example : ((rf4_bddOn (isCompact_closedBall (0 : ℂ) 1) Metric.ball_subset_closedBall (fun _ ↦ 1)
    continuousOn_const (differentiableOn_const 1) : b63r_bddHol (Metric.ball (0 : ℂ) 1)) :
      Metric.ball (0 : ℂ) 1 →ᵇ ℂ) ⟨0, by simp⟩ = 1 := rfl

/-- The sector multiplier `uʲ (1 − ε u⁻ⁿ)^{s_j}` as a bounded holomorphic function on `A_n`,
for `|ε| < r`.
Source: `docs/specs/RelativeFrame.md`, §4.2 (differential pullback, `S_x(ε)`); Ahlfors,
*Complex Analysis*, 3rd ed., Ch. 3, §4. -/
def rf4_multiplier (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) (ε : ℂ) (hε : ‖ε‖ < r)
    (j : Fin n) : b63r_bddHol (b63r_annulus n r) :=
  rf4_bddOn (rf4_closedAnnulus_isCompact hn r) (rf4_annulus_subset_closed n r)
    (rf4_multiplierFun n ε j)
    (fun _ hu ↦ (rf4_multiplierFun_differentiableAt hn hr hε j hu).continuousAt.continuousWithinAt)
    (fun _ hu ↦ (rf4_multiplierFun_differentiableAt hn hr hε j
      (rf4_annulus_subset_closed n r hu)).differentiableWithinAt)

example (u : b63r_annulus 2 1) :
    ((rf4_multiplier 2 (by norm_num) 1 one_pos 0 (by simp) 1 : b63r_bddHol (b63r_annulus 2 1)) :
      b63r_annulus 2 1 →ᵇ ℂ) u = (u : ℂ) := by
  change rf4_multiplierFun 2 0 1 u = u
  simp [rf4_multiplierFun, rf4_sectorExp]

/-- `u ↦ c + uⁿ` maps `A_n` into `D(c, 2r)`. -/
theorem rf4_powMap_mapsTo (n : ℕ) (r : ℝ) (c : ℂ) :
    MapsTo (fun u : ℂ ↦ c + u ^ n) (b63r_annulus n r) (Metric.ball c (2 * r)) := by
  intro u hu
  simpa [Metric.mem_ball, dist_eq_norm, norm_pow] using hu.2

/-- The sector operator `S(ε) g = n Σ_{j<n} uʲ (1 − ε u⁻ⁿ)^{s_j} g_j(c + uⁿ)` from `n`-tuples of
bounded holomorphic functions on `D(c, 2r)` to bounded holomorphic functions on `A_n`, for
`|ε| < r`, and zero otherwise. The argument `c + uⁿ` of `g_j` is the fixed base coordinate.
Source: `docs/specs/RelativeFrame.md`, §4.2 (differential pullback, `S_x(ε)`); stage A
`b63r_bddHol_comp`, `b63r_bddHol_mul`. -/
def rf4_sectorOp (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) (c ε : ℂ) :
    (Fin n → b63r_bddHol (Metric.ball c (2 * r))) →L[ℂ] b63r_bddHol (b63r_annulus n r) :=
  if hε : ‖ε‖ < r then
    ∑ j : Fin n, (n : ℂ) • ((b63r_bddHol_mul (rf4_multiplier n hn r hr ε hε j)).comp
      ((b63r_bddHol_comp (fun u : ℂ ↦ c + u ^ n)
        ((differentiable_const c).add (differentiable_pow n)).differentiableOn
        (rf4_powMap_mapsTo n r c)).comp (ContinuousLinearMap.proj j)))
  else 0

/-- The value of the sector operator at a point of the annulus, for `|ε| < r`.
Source: the definition `rf4_sectorOp`; `docs/specs/RelativeFrame.md`, §4.2. -/
theorem rf4_sectorOp_apply (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) (c ε : ℂ) (hε : ‖ε‖ < r)
    (g : Fin n → b63r_bddHol (Metric.ball c (2 * r))) (u : b63r_annulus n r) :
    ((rf4_sectorOp n hn r hr c ε g : b63r_bddHol (b63r_annulus n r)) : b63r_annulus n r →ᵇ ℂ) u =
      n * ∑ j : Fin n, rf4_multiplierFun n ε j u * rf4_extendBdd (g j) (c + (u : ℂ) ^ n) := by
  simp only [rf4_sectorOp, hε, ↓reduceDIte]
  simp [Finset.mul_sum, b63r_bddHol_mul, b63r_bddHol_comp, b63r_restrictMap, rf4_multiplier,
    rf4_bddOn, rf4_extendBdd, (rf4_powMap_mapsTo n r c) u.2]
  rfl

example (n : ℕ) (hn : 1 ≤ n) (c : ℂ) : rf4_sectorOp n hn 1 one_pos c 2 = 0 := by
  rw [rf4_sectorOp, dite_eq_right (by norm_num)]

/-! ## Outer data and the operator -/

/-- Outer data of a plumbed surface: a finite piece cover of the outer region `O`, a radius `r`,
and `m` discs, each with a degree `n_x ≥ 1`, a base branch value `c_x`, and one piece of the
cover equal to the annulus `A_{n_x} = {r < |u|ⁿ < 2r}` in its chart `u`.
Source: `docs/specs/RelativeFrame.md`, §4.1 (outer piece, annuli) and §4.2 (`E_O`, `G_x`,
`F_x`); stage A′ `rf2_PieceCover`. -/
structure rf4_OuterData (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (O : Set C) where
  P : rf2_PieceCover C O
  r : ℝ
  hr : 0 < r
  m : ℕ
  deg : Fin m → ℕ
  hdeg : ∀ x, 1 ≤ deg x
  c : Fin m → ℂ
  ann : Fin m → Fin P.n
  hann : ∀ x, P.piece (ann x) = b63r_annulus (deg x) r

/-- The disc data `∏ₓ G_x`, `G_x = (b63r_bddHol (D(c_x, 2r)))^{n_x}`, with the maximum norm.
Source: `docs/specs/RelativeFrame.md`, §4.2. -/
abbrev rf4_Disc {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} (D : rf4_OuterData C O) :=
  (x : Fin D.m) → Fin (D.deg x) → b63r_bddHol (Metric.ball (D.c x) (2 * D.r))

/-- The source `E_O × ∏ₓ G_x` of the full-overlap operator.
Source: `docs/specs/RelativeFrame.md`, §4.2. -/
abbrev rf4_Src {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} (D : rf4_OuterData C O) :=
  rf2_bddForm D.P × rf4_Disc D

/-- The target `∏ₓ F_x`, `F_x = b63r_bddHol (A_{n_x})`: data on the full overlaps.
Source: `docs/specs/RelativeFrame.md`, §4.2 and §4.3. -/
abbrev rf4_Tgt {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} (D : rf4_OuterData C O) :=
  (x : Fin D.m) → b63r_bddHol (b63r_annulus (D.deg x) D.r)

/-- Bounded holomorphic functions on a disc form a Banach space.
Source: stage A, A6 (`docs/specs/RelativeFrame.md`, §5). -/
instance rf4_ball_banach (c : ℂ) (ρ : ℝ) : CompleteSpace (b63r_bddHol (Metric.ball c ρ)) :=
  b63r_bddHol_completeSpace Metric.isOpen_ball

/-- Bounded holomorphic functions on an annulus form a Banach space.
Source: stage A, A6 (`docs/specs/RelativeFrame.md`, §5). -/
instance rf4_annulus_banach (n : ℕ) (r : ℝ) : CompleteSpace (b63r_bddHol (b63r_annulus n r)) :=
  b63r_bddHol_completeSpace (rf4_annulus_isOpen n r)

/-- Bounded chart forms form a Banach space.
Source: `rf2_bddForm_banach`. -/
instance rf4_bddForm_banachInst {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (P : rf2_PieceCover C O) :
    CompleteSpace (rf2_bddForm P) :=
  (rf2_bddForm_banach P).2

example {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} (D : rf4_OuterData C O) : CompleteSpace (rf4_Src D) ∧ CompleteSpace (rf4_Tgt D) :=
  ⟨inferInstance, inferInstance⟩

/-- The full-overlap operator `δ_ε(α, g)_x = α_x − S_x(ε_x) g_x`, where `α_x` is the coefficient of
`α` on the annulus piece of disc `x`.
Source: `docs/specs/RelativeFrame.md`, §4.2 (`δ_t`) and §5, C4. -/
def rf4_delta {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} (D : rf4_OuterData C O) (ε : Fin D.m → ℂ) : rf4_Src D →L[ℂ] rf4_Tgt D :=
  ContinuousLinearMap.pi fun x ↦
    (b63r_bddHol_restrict (D.hann x).ge).comp
        ((rf2_bddForm_coeff D.P (D.ann x)).comp (ContinuousLinearMap.fst ℂ _ _)) -
      (rf4_sectorOp (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x)).comp
        ((ContinuousLinearMap.proj x).comp (ContinuousLinearMap.snd ℂ _ _))

example {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} (D : rf4_OuterData C O) (ε : Fin D.m → ℂ) (g : rf4_Disc D) (x : Fin D.m) :
    rf4_delta D ε (0, g) x =
      -rf4_sectorOp (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x) (g x) := by
  simp [rf4_delta]

/-! ## The plumbing datum of one fibre -/

/-- The plumbing datum of a fibre `X` over outer data `D` on a base surface `C` and moving values
`ε`: an identification `h : C ≃ₜ X` under which every outer piece chart is a chart of `X`
(stationary coordinates); for each disc `x` a chart `w_x` of `X` whose target contains the closure
of `D_w(ε_x)`; the inner pieces `Δ_x = w_x⁻¹(D_w(ε_x))`, pairwise disjoint, covering `X` together
with `O`, meeting `O` exactly in the annulus piece; and on that annulus `w_x = Φ_{ε_x}(u)`.
These are the geometric fields of the plumbing description; nothing analytic about forms,
cohomology or operators is among them.
Source: `docs/specs/RelativeFrame.md`, §4.1 (outer piece, discs, annuli, root coordinates,
gluing; stage B items B5, B6, B7f, B8f, B9, B10). -/
structure rf4_Plumbing {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (D : rf4_OuterData C O) (ε : Fin D.m → ℂ)
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] where
  h : C ≃ₜ X
  stationary : ∀ i, h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i ∈
    IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X
  small : ∀ x, ‖ε x‖ < D.r
  w : Fin D.m → OpenPartialHomeomorph X ℂ
  w_mem : ∀ x, w x ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X
  w_target : ∀ x, closure (rf4_innerDisc (D.deg x) D.r (ε x)) ⊆ (w x).target
  cover : ∀ p : X, h.symm p ∈ O ∨ ∃ x, p ∈ (w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x)
  disjoint : Pairwise fun x y ↦ Disjoint ((w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x))
    ((w y).symm '' rf4_innerDisc (D.deg y) D.r (ε y))
  overlap : ∀ x, h '' O ∩ (w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x) =
    h '' ((D.P.chart (D.ann x)).symm '' b63r_annulus (D.deg x) D.r)
  glue : ∀ x, ∀ u ∈ b63r_annulus (D.deg x) D.r,
    h ((D.P.chart (D.ann x)).symm u) ∈ (w x).source ∧
      w x (h ((D.P.chart (D.ann x)).symm u)) = rf4_rootMap (D.deg x) (ε x) u

/-- Gluing of source data into a function on the tangent bundle of the fibre: on `O`, the
coefficient of `α` in a piece containing the point times the chart differential; on an inner
piece, the sector coefficient `n Σ wʲ g_j(c + ε + wⁿ)` times `dw`; zero elsewhere.
Source: `docs/specs/RelativeFrame.md`, §4.2 (kernel: the two parts glue to a form on `X_t`);
Forster, *Lectures on Riemann Surfaces*, §9. -/
def rf4_glue {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (k : rf4_Src D) : TangentBundle 𝓘(ℂ, ℂ) X → ℂ := fun q ↦
  if hO : ∃ i, S.h.symm q.1 ∈ (D.P.chart i).source ∧ D.P.chart i (S.h.symm q.1) ∈ D.P.piece i then
    rf4_extendBdd (k.1.val (Classical.choose hO)) (D.P.chart (Classical.choose hO) (S.h.symm q.1)) *
      (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (fun p : X ↦ D.P.chart (Classical.choose hO) (S.h.symm p)) q.1 q.2)
  else if hD : ∃ x, q.1 ∈ (S.w x).source ∧ S.w x q.1 ∈ rf4_innerDisc (D.deg x) D.r (ε x) then
    rf4_sectorCoeff (D.deg (Classical.choose hD))
        (fun j ↦ rf4_extendBdd (k.2 (Classical.choose hD) j))
        (D.c (Classical.choose hD) + ε (Classical.choose hD)) (S.w (Classical.choose hD) q.1) *
      (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w (Classical.choose hD)) q.1 q.2)
  else 0

example {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) : rf4_glue S 0 = 0 := by
  funext q
  simp only [rf4_glue, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
  split_ifs <;> simp [rf4_extendBdd, rf4_sectorCoeff] <;> exact zero_mul _

end HodgeLean.Foundations.Program
