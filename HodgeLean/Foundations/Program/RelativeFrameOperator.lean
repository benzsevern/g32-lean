import HodgeLean.Foundations.Program.RelativeFrameOperatorProofs
import HodgeLean.Foundations.Program.PrymVariationFramesDefs

/-! # The full-overlap operator, its Fredholm property and its kernel: statement draft
Implications, for the explicit operator `δ_ε` on the full overlaps of a plumbed surface: from the
radius to operator-norm analyticity of `ε ↦ δ_ε` on the polydisc `|ε_x| < r`; from a degree
`n ≥ 1` and `|ε| < r` to injectivity of the sector map and to the sector splitting of bounded
holomorphic coefficients on the moving disc; and from a plumbing datum of a fibre `X` (stationary
outer charts, disc charts, cover, disjointness, exact overlaps, gluing by the root map) to the
identification of `ker δ_ε` with `b3_HolForm ℂ X` through the explicit gluing map, to the cutoff
obstruction map into the `(1,1)` Dolbeault quotient of the C8 gate with kernel inside the range
(C9), to finite algebraic codimension of the range, to the Fredholm property, and to
non-surjectivity when there is at least one disc.

Not claimed: any statement about the B6-2b total space or its fibres. The plumbing datum
`rf4_Plumbing` is the generic geometric structure of a plumbed fibre; its construction for the
B6-2b fibres is stage B (`docs/specs/RelativeFrame.md`, B5–B10) and is not supplied or assumed
here. Nothing is claimed about relative forms (C12), kernel frames of the family, or the restated
targets of stage D. HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

/-- Operator-norm holomorphy (C5): `ε ↦ δ_ε` is analytic on the polydisc `|ε_x| < r`. Each disc
contributes the sector operator, whose multipliers `uʲ (1 − εu⁻ⁿ)^{s_j}` are the norm-convergent
binomial series `Σ_k binom(s_j, k) (−ε)ᵏ u^{j − nk}` with `sup_{A_n} |u^{−nk}| = r^{−k}`.
Source: `docs/specs/RelativeFrame.md`, §4.2 (analyticity in `t`); `b63r_mulSeries_analytic`,
`b63r_binomial_multiplier`; Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Ch. III,
§3.1. -/
theorem rf4_delta_analytic {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (D : rf4_OuterData C O) :
    AnalyticOnNhd ℂ (rf4_delta D) (rf4_polydisc D.m D.r) :=
  rf4_delta_analytic_aux D

example := @rf4_delta_analytic

/-- Sector injectivity (C2, first half): the sector coefficient `n Σ_{j<n} wʲ g_j(c + ε + wⁿ)`
vanishes on the moving disc `D_w(ε)` only for `g = 0`. The disc is invariant under `w ↦ ζw`,
`ζⁿ = 1`, which separates the sectors. The map `wⁿ + ε` covers `D(0, 2r)`, and
`c + ε + wⁿ` covers `D(c, 2r)`.
Source: `docs/specs/RelativeFrame.md`, §4.2 (kernel, sector splitting); Ahlfors, *Complex
Analysis*, 3rd ed., Ch. 5, §1 (power series and roots of unity). -/
theorem rf4_sector_injective (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) (c ε : ℂ)
    (hε : ‖ε‖ < r) (g : Fin n → b63r_bddHol (Metric.ball c (2 * r)))
    (hg : ∀ w ∈ rf4_innerDisc n r ε,
      rf4_sectorCoeff n (fun j ↦ rf4_extendBdd (g j)) (c + ε) w = 0) :
    g = 0 :=
  rf4_sector_injective_aux n hn r hr c ε hε g hg

example := @rf4_sector_injective

/-- Sector splitting (C2, second half): a bounded holomorphic coefficient on the moving disc
`D_w(ε)` is the sector coefficient of bounded holomorphic `g_j` on `D(c, 2r)`. Its sectors
`c_j(w) = wʲ G_j(wⁿ)` have `G_j` holomorphic on `{y : |y + ε| < 2r}` (local inversion of `wⁿ` off
`0`, the power series at `0`) and bounded; put `g_j(z) = G_j(z − c − ε)/n`.
Source: `docs/specs/RelativeFrame.md`, §4.2 (kernel); Ahlfors, *Complex Analysis*, 3rd ed.,
Ch. 4, §3 (local inversion) and Ch. 5, §1. -/
theorem rf4_sector_surjective (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) (c ε : ℂ)
    (hε : ‖ε‖ < r) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (rf4_innerDisc n r ε))
    (hb : BddAbove ((fun w ↦ ‖f w‖) '' rf4_innerDisc n r ε)) :
    ∃ g : Fin n → b63r_bddHol (Metric.ball c (2 * r)), ∀ w ∈ rf4_innerDisc n r ε,
      f w = rf4_sectorCoeff n (fun j ↦ rf4_extendBdd (g j)) (c + ε) w :=
  rf4_sector_surjective_aux n hn r hr c ε hε f hf hb

example := @rf4_sector_surjective

/-- Kernel identification (C6–C7): on a plumbed fibre, the gluing map is a linear equivalence
from `ker δ_ε` onto the holomorphic forms of `X`. A kernel element agrees with its sector form
on each annulus by the differential pullback along `Φ_ε`, so the two parts glue; conversely a
form restricts to bounded coefficients on the relatively compact pieces and splits into sectors
on each inner piece.
Source: `docs/specs/RelativeFrame.md`, §4.2 (kernel) and §5, C6–C7; Forster, *Lectures on
Riemann Surfaces*, §9; identity theorem on the connected annuli. -/
theorem rf4_kernel_equiv {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) :
    ∃ e : (rf4_delta D ε).ker ≃ₗ[ℂ] b3_HolForm ℂ X,
      ∀ k : (rf4_delta D ε).ker, (e k : TangentBundle 𝓘(ℂ, ℂ) X → ℂ) = rf4_glue S k :=
  rf4_kernel_equiv_aux S

example := @rf4_kernel_equiv

/-- Kernel dimension (C7, C11): on a compact connected plumbed fibre, `ker δ_ε` is
finite-dimensional of dimension `g = dim b3_HolForm ℂ X`.
Source: `docs/specs/RelativeFrame.md`, §4.3 (the kernel has dimension `g`);
`b3_holForm_finiteDimensional`; Forster, *Lectures on Riemann Surfaces*, §§14, 17. -/
theorem rf4_ker_finrank {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] (S : rf4_Plumbing D ε X) :
    FiniteDimensional ℂ (rf4_delta D ε).ker ∧
      Module.finrank ℂ (rf4_delta D ε).ker = Module.finrank ℂ (b3_HolForm ℂ X) :=
  rf4_ker_finrank_aux S

example := @rf4_ker_finrank

/-- The cutoff obstruction map (C9): there is a linear map `τ` from the full-overlap data to the
`(1,1)` Dolbeault quotient of the C8 gate, represented by smooth forms supported in the union of
the annuli, whose kernel lies in the range of `δ_ε`. With cutoffs `λ_x`, `τ(φ) = [Σₓ φ_x ∂̄λ_x]`;
if `∂̄v = τ(φ)`, then `α = λφ − v` on `O` and `β = (λ − 1)φ − v` on the inner pieces are
holomorphic and bounded, `β` splits into sectors, and `δ_ε(α, g) = φ`.
Source: `docs/specs/RelativeFrame.md`, §4.3; `docs/specs/RelativeFrameGate.md` (review: the
full-overlap cutoff map and the kernel-to-range comparison); Forster, *Lectures on Riemann
Surfaces*, §15. -/
theorem rf4_cutoff_obstruction {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] (S : rf4_Plumbing D ε X) :
    ∃ τ : rf4_Tgt D →ₗ[ℂ] (rf2_smoothForms X 1 1 ⧸ rf2_boundaries X),
      LinearMap.ker τ ≤ (rf4_delta D ε).range ∧
        ∀ φ : rf4_Tgt D, ∃ σ : rf2_smoothForms X 1 1, Submodule.Quotient.mk σ = τ φ ∧
          ∀ (y : X) (z : (chartAt ℂ y).target),
            (chartAt ℂ y).symm z ∉
                ⋃ x, S.h '' ((D.P.chart (D.ann x)).symm '' b63r_annulus (D.deg x) D.r) →
              σ.val y z = 0 :=
  rf4_cutoff_obstruction_aux S

example := @rf4_cutoff_obstruction

/-- Finite algebraic codimension (C9): the range of `δ_ε` has finite algebraic codimension, at
most the dimension of the `(1,1)` Dolbeault quotient, which `rf2_dbar_forms` bounds.
Source: `docs/specs/RelativeFrame.md`, §4.3 and §5, C9; `rf2_dbar_forms`,
`b4c_exists_meroForm`. -/
theorem rf4_delta_range_cofg {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] (S : rf4_Plumbing D ε X) :
    (rf4_delta D ε).range.CoFG :=
  rf4_delta_range_cofg_aux S

example := @rf4_delta_range_cofg

/-- The Fredholm property (C10): on a compact connected plumbed fibre, `δ_ε` is Fredholm, by
Kato's criterion from the finite-dimensional kernel and the range of finite codimension.
Source: `docs/specs/RelativeFrame.md`, §4.3 and §5, C10; `b63r_isFredholm_of_finite`. -/
theorem rf4_delta_isFredholm {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] (S : rf4_Plumbing D ε X) :
    (rf4_delta D ε).IsFredholm :=
  rf4_delta_isFredholm_aux S

example := @rf4_delta_isFredholm

/-- A genuine cokernel: with at least one disc, `δ_ε` is not surjective. For `φ` in the range,
`Σₓ ∮_{|u|=ρ} φ_x du = 0`: the outer part by Stokes on `O` minus collars, each sector part by
Cauchy in `w`. So `du/u` on one annulus and `0` elsewhere is not in the range.
Source: `docs/specs/RelativeFrame.md`, §4.3 (the operator really has a cokernel); Forster,
*Lectures on Riemann Surfaces*, §10 (Stokes) and Ahlfors, *Complex Analysis*, Ch. 4, §1. -/
theorem rf4_delta_not_surjective {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] (S : rf4_Plumbing D ε X) (hm : 0 < D.m) :
    ¬ Function.Surjective (rf4_delta D ε) :=
  rf4_delta_not_surjective_aux S hm

example := @rf4_delta_not_surjective

/-! ## Satisfiable instances, non-degenerate

Every check below uses only definitions and checked repository results, never a statement of
this file. -/

/-- One annulus piece `A_2 = {1 < |u|² < 2}` in the identity chart of the plane.
Source: RelativeFrame §4.2; the identity atlas on `ℂ`. -/
def rf4_testCover : rf2_PieceCover ℂ (b63r_annulus 2 1) where
  n := 1
  chart := fun _ ↦ OpenPartialHomeomorph.refl ℂ
  analytic := fun _ ↦ IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ, ℂ)) (n := ω) (0 : ℂ)
  piece := fun _ ↦ b63r_annulus 2 1
  isOpen := fun _ ↦ rf4_annulus_isOpen 2 1
  compact := fun _ ↦ (rf4_closedAnnulus_isCompact (by norm_num) 1).of_isClosed_subset
    isClosed_closure (closure_minimal (rf4_annulus_subset_closed 2 1)
      (rf4_closedAnnulus_isCompact (by norm_num) 1).isClosed)
  contained := by intro i z hz; trivial
  covers := by simpa using (iUnion_const _).symm

/-- Outer data with one disc of degree two over the annulus piece.
Source: RelativeFrame §4.2. -/
def rf4_testOuter : rf4_OuterData ℂ (b63r_annulus 2 1) where
  P := rf4_testCover
  r := 1
  hr := one_pos
  m := 1
  deg := fun _ ↦ 2
  hdeg := fun _ ↦ by norm_num
  c := fun _ ↦ 0
  ann := fun _ ↦ ⟨0, Nat.one_pos⟩
  hann := fun _ ↦ rfl

/-- The form `du` on the annulus piece.
Source: Forster, §9. -/
def rf4_testForm : rf2_bddForm rf4_testCover :=
  ⟨fun _ ↦ ⟨BoundedContinuousFunction.const _ 1,
    ⟨fun _ ↦ 1, differentiableOn_const 1, fun _ ↦ rfl⟩⟩, by
    intro i j z w h
    change (1 : ℂ) = 1 * deriv ((id : ℂ → ℂ) ∘ id) (z : ℂ)
    simp only [Function.comp_id, deriv_id, mul_one]⟩

/-- A point of the test annulus. -/
theorem rf4_test_mem : (6 / 5 : ℂ) ∈ b63r_annulus 2 1 := by
  constructor <;> norm_num [Complex.norm_div]

/-- The operator acts between nonzero spaces, with one disc of degree two and a moving value
`ε = 1/2 ≠ 0`, and is not the zero operator. -/
example : rf4_testOuter.m = 1 ∧ rf4_testOuter.deg ⟨0, Nat.one_pos⟩ = 2 ∧ (fun _ ↦ (1 / 2 : ℂ)) ∈
    rf4_polydisc rf4_testOuter.m rf4_testOuter.r ∧ (1 / 2 : ℂ) ≠ 0 ∧
    rf4_delta rf4_testOuter (fun _ ↦ 1 / 2) (rf4_testForm, 0) ≠ 0 := by
  refine ⟨rfl, rfl, fun _ ↦ by norm_num [rf4_testOuter], by norm_num, fun h ↦ ?_⟩
  have := congrArg (fun f : rf4_Tgt rf4_testOuter ↦
    ((f ⟨0, Nat.one_pos⟩ : b63r_bddHol (b63r_annulus 2 1)).val : b63r_annulus 2 1 →ᵇ ℂ)
      ⟨6 / 5, rf4_test_mem⟩) h
  simp [rf4_delta, rf4_testForm, b63r_bddHol_restrict, b63r_bddHol_comp, rf2_bddForm_coeff,
    b63r_restrictMap] at this
  exact one_ne_zero this

/-- Sector data `g_0 = 1`, `g_1 = 0` on the disc `D(0, 2)`.
Source: RelativeFrame §4.2 (sector map). -/
def rf4_testSectors : Fin 2 → b63r_bddHol (Metric.ball (0 : ℂ) (2 * 1)) := fun j ↦
  if (j : ℕ) = 0 then ⟨BoundedContinuousFunction.const _ 1,
    ⟨fun _ ↦ 1, differentiableOn_const 1, fun _ ↦ rfl⟩⟩ else 0

/-- The same sector data as disc data of the test outer data.
Source: RelativeFrame §4.2. -/
def rf4_testDisc : rf4_Disc rf4_testOuter := fun _ ↦ rf4_testSectors

/-- The sector part is nonzero at the moving value `ε = 1/2`: with `g_0 = 1` and `g_1 = 0`, the
value of `δ_ε(0, g)` at `u = 6/5` is `−2 (1 − ε u⁻²)^{−1/2} ≠ 0`. -/
example : rf4_delta rf4_testOuter (fun _ ↦ 1 / 2) (0, rf4_testDisc) ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : rf4_Tgt rf4_testOuter ↦
    ((f ⟨0, Nat.one_pos⟩ : b63r_bddHol (b63r_annulus 2 1)).val : b63r_annulus 2 1 →ᵇ ℂ)
      ⟨6 / 5, rf4_test_mem⟩) h
  have h2 : rf4_delta rf4_testOuter (fun _ ↦ 1 / 2) (0, rf4_testDisc) ⟨0, Nat.one_pos⟩ =
      -rf4_sectorOp 2 (by norm_num) 1 one_pos 0 (1 / 2) rf4_testSectors := by
    simp [rf4_delta]
    rfl
  simp only [h2, Pi.zero_apply] at h1
  have key : ((rf4_sectorOp 2 (by norm_num) 1 one_pos 0 (1 / 2) rf4_testSectors :
      b63r_bddHol (b63r_annulus 2 1)) : b63r_annulus 2 1 →ᵇ ℂ) ⟨6 / 5, rf4_test_mem⟩ = 0 :=
    neg_eq_zero.mp h1
  rw [rf4_sectorOp_apply 2 (by norm_num) 1 one_pos 0 (1 / 2) (by norm_num)] at key
  simp [Fin.sum_univ_two, rf4_testSectors, rf4_extendBdd, rf4_multiplierFun, rf4_sectorExp,
    Metric.mem_ball] at key
  norm_num at key

section Sphere

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The two charts `z` and `1/z` of the sphere.
Source: `b4cov_sphChartedSpace`. -/
def rf4_sphereCharts : Fin 2 → OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  ![b4cov_chart0, b4cov_chartInf]

example : rf4_sphereCharts 0 = b4cov_chart0 := rfl

/-- The annulus `A_n = {1 < |z|ⁿ < 2}` in `z` and the unit disc in `1/z`.
Source: RelativeFrame §4.1 (annuli). -/
def rf4_spherePieces (n : ℕ) : Fin 2 → Set ℂ :=
  ![b63r_annulus n 1, Metric.ball 0 1]

example (n : ℕ) : rf4_spherePieces n 0 = b63r_annulus n 1 := rfl

/-- The outer region `{|z|ⁿ > 1} ∪ {∞}` of the sphere.
Source: RelativeFrame §4.1 (outer piece). -/
def rf4_sphereO (n : ℕ) : Set (OnePoint ℂ) :=
  ⋃ i, (rf4_sphereCharts i).symm '' rf4_spherePieces n i

example (n : ℕ) : rf4_sphereO n =
    ⋃ i, (rf4_sphereCharts i).symm '' rf4_spherePieces n i := rfl

/-- The chart `1/z` has full target. -/
theorem rf4_chartInf_target : b4cov_chartInf.target = univ := by
  simp [b4cov_chartInf, b4cov_chart0_target]

/-- The outer region as a two-piece cover, the annulus in `z` and a disc around `∞` in `1/z`.
Source: RelativeFrame §5, A13; `b4cov_sphChartedSpace`. -/
def rf4_sphereCover (n : ℕ) (hn : 1 ≤ n) : rf2_PieceCover (OnePoint ℂ) (rf4_sphereO n) where
  n := 2
  chart := rf4_sphereCharts
  analytic := by
    intro i
    apply IsManifold.subset_maximalAtlas
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  piece := rf4_spherePieces n
  isOpen := by
    intro i
    fin_cases i
    · exact rf4_annulus_isOpen n 1
    · exact Metric.isOpen_ball
  compact := by
    intro i
    fin_cases i
    · exact (rf4_closedAnnulus_isCompact hn 1).of_isClosed_subset isClosed_closure
        (closure_minimal (rf4_annulus_subset_closed n 1) (rf4_closedAnnulus_isCompact hn 1).isClosed)
    · change IsCompact (closure (Metric.ball (0 : ℂ) 1))
      rw [closure_ball _ one_ne_zero]
      exact isCompact_closedBall _ _
  contained := by
    intro i
    fin_cases i
    · change _ ⊆ b4cov_chart0.target
      rw [b4cov_chart0_target]
      exact subset_univ _
    · change _ ⊆ b4cov_chartInf.target
      rw [rf4_chartInf_target]
      exact subset_univ _
  covers := rfl

example (n : ℕ) (hn : 1 ≤ n) : (rf4_sphereCover n hn).n = 2 := rfl

/-- `∞` lies in the outer region. -/
theorem rf4_sphere_infty_mem (n : ℕ) : (OnePoint.infty : OnePoint ℂ) ∈ rf4_sphereO n := by
  refine mem_iUnion.mpr ⟨1, 0, by simp [rf4_spherePieces], ?_⟩
  change b4cov_chartInf.symm 0 = _
  rw [b4cov_chartInf_symm, b4cov_sphInv_zero]

/-- A finite point lies in the outer region exactly when `|z|ⁿ > 1`. -/
theorem rf4_sphere_coe_mem (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    (z : OnePoint ℂ) ∈ rf4_sphereO n ↔ 1 < ‖z‖ ^ n := by
  constructor
  · intro hz
    obtain ⟨i, v, hv, hvz⟩ := mem_iUnion.mp hz
    fin_cases i
    · change b4cov_chart0.symm v = _ at hvz
      rw [b4cov_chart0_symm] at hvz
      cases OnePoint.coe_injective hvz
      exact hv.1
    · change b4cov_chartInf.symm v = _ at hvz
      change v ∈ Metric.ball (0 : ℂ) 1 at hv
      rw [b4cov_chartInf_symm] at hvz
      by_cases hv0 : v = 0
      · subst hv0
        rw [b4cov_sphInv_zero] at hvz
        exact absurd hvz (OnePoint.coe_ne_infty z).symm
      · rw [b4cov_sphInv_coe hv0] at hvz
        cases OnePoint.coe_injective hvz
        have hv1 : ‖v‖ < 1 := by simpa using hv
        have : 1 < ‖v⁻¹‖ := by
          rw [norm_inv]
          exact one_lt_inv₀ (norm_pos_iff.mpr hv0) |>.mpr hv1
        exact one_lt_pow₀ this (by omega)
  · intro h
    by_cases h2 : ‖z‖ ^ n < 2
    · exact mem_iUnion.mpr ⟨0, z, ⟨h, by linarith⟩, b4cov_chart0_symm z⟩
    · have hz1 : 1 < ‖z‖ := by
        by_contra hc
        push Not at hc
        have := pow_le_one₀ (norm_nonneg z) hc (n := n)
        linarith
      have hz0 : z ≠ 0 := norm_pos_iff.mp (one_pos.trans hz1)
      refine mem_iUnion.mpr ⟨1, z⁻¹, ?_, ?_⟩
      · change z⁻¹ ∈ Metric.ball (0 : ℂ) 1
        rw [mem_ball_zero_iff, norm_inv]
        exact inv_lt_one_of_one_lt₀ hz1
      · change b4cov_chartInf.symm z⁻¹ = _
        rw [b4cov_chartInf_symm, b4cov_sphInv_coe (inv_ne_zero hz0), inv_inv]

/-- The disc chart `w = z − ε` of the sphere.
Source: `b4cov_chart0`; RelativeFrame §4.1 item 2. -/
def rf4_sphereDisc (ε : ℂ) : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  b4cov_chart0.trans (Homeomorph.addRight (-ε)).toOpenPartialHomeomorph

example (ε : ℂ) : rf4_sphereDisc ε =
    b4cov_chart0.trans (Homeomorph.addRight (-ε)).toOpenPartialHomeomorph := rfl

/-- The disc chart has full target. -/
theorem rf4_sphereDisc_target (ε : ℂ) : (rf4_sphereDisc ε).target = univ := by
  simp [rf4_sphereDisc, b4cov_chart0_target]

/-- The disc chart has the source of `z`. -/
theorem rf4_sphereDisc_source (ε : ℂ) : (rf4_sphereDisc ε).source = b4cov_chart0.source := by
  simp [rf4_sphereDisc]

/-- The disc chart is `z − ε`. -/
theorem rf4_sphereDisc_coe (ε z : ℂ) : rf4_sphereDisc ε z = z - ε := by
  simp [rf4_sphereDisc, b4cov_chart0_coe, sub_eq_add_neg]

/-- The inverse disc chart is `w + ε`. -/
theorem rf4_sphereDisc_symm (ε v : ℂ) : (rf4_sphereDisc ε).symm v = ((v + ε : ℂ) : OnePoint ℂ) := by
  simp only [rf4_sphereDisc, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.coe_trans, Function.comp_apply, b4cov_chart0_symm,
    Homeomorph.toOpenPartialHomeomorph_symm_apply]
  congr 1
  change v - -ε = v + ε
  ring

/-- The disc chart is a chart of the sphere. -/
theorem rf4_sphereDisc_mem (ε : ℂ) :
    rf4_sphereDisc ε ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω (OnePoint ℂ) := by
  have h0 : b4cov_chart0 ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω (OnePoint ℂ) :=
    IsManifold.subset_maximalAtlas (Or.inl rfl)
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
  constructor
  · rw [rf4_sphereDisc_source]
    have ht : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : ℂ ↦ x + -ε) :=
      (contDiff_id.add contDiff_const).contMDiff
    exact ht.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas h0)
  · rw [rf4_sphereDisc_target]
    have ht : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun v : ℂ ↦ v + ε) :=
      (contDiff_id.add contDiff_const).contMDiff
    have hs := contMDiffOn_symm_of_mem_maximalAtlas h0
    rw [b4cov_chart0_target] at hs
    have : (rf4_sphereDisc ε).symm = b4cov_chart0.symm ∘ fun v : ℂ ↦ v + ε := by
      funext v
      rw [rf4_sphereDisc_symm, Function.comp_apply, b4cov_chart0_symm]
    rw [this]
    exact hs.comp ht.contMDiffOn (mapsTo_univ _ _)

/-- For `n = 1` or `ε = 0`, `vⁿ + ε = (v + ε)ⁿ`. -/
theorem rf4_sphere_key {n : ℕ} {ε : ℂ} (hnε : n = 1 ∨ ε = 0) (v : ℂ) :
    v ^ n + ε = (v + ε) ^ n := by
  rcases hnε with rfl | rfl <;> simp

/-- The inner piece is `{|z|ⁿ < 2}`. -/
theorem rf4_sphereDisc_image {n : ℕ} {ε : ℂ} (hnε : n = 1 ∨ ε = 0) :
    (rf4_sphereDisc ε).symm '' rf4_innerDisc n 1 ε =
      (fun z : ℂ ↦ (z : OnePoint ℂ)) '' {z | ‖z‖ ^ n < 2} := by
  ext p
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v + ε, ?_, (rf4_sphereDisc_symm ε v).symm⟩
    change ‖v ^ n + ε‖ < 2 * 1 at hv
    rw [rf4_sphere_key hnε] at hv
    simpa [norm_pow] using hv
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z - ε, ?_, ?_⟩
    · change ‖(z - ε) ^ n + ε‖ < 2 * 1
      rw [rf4_sphere_key hnε, sub_add_cancel, norm_pow]
      simpa using hz
    · rw [rf4_sphereDisc_symm, sub_add_cancel]

/-- For `n = 1` or `ε = 0`, the root map is `u − ε`. -/
theorem rf4_sphere_rootMap {n : ℕ} {ε : ℂ} (hnε : n = 1 ∨ ε = 0) {u : ℂ} (hu : u ≠ 0) :
    rf4_rootMap n ε u = u - ε := by
  rcases hnε with rfl | rfl
  · simp [rf4_rootMap, mul_sub]
    field_simp
  · simp [rf4_rootMap]

/-- Outer data on the sphere: one disc of degree `n` over the annulus piece, radius one.
Source: RelativeFrame §4.1–4.2. -/
def rf4_sphereOuter (n : ℕ) (hn : 1 ≤ n) : rf4_OuterData (OnePoint ℂ) (rf4_sphereO n) where
  P := rf4_sphereCover n hn
  r := 1
  hr := one_pos
  m := 1
  deg := fun _ ↦ n
  hdeg := fun _ ↦ hn
  c := fun _ ↦ 0
  ann := fun _ ↦ ⟨0, Nat.zero_lt_two⟩
  hann := fun _ ↦ rfl

/-- A plumbing datum on the sphere, for degree `n` with `ε = 0`, or degree one with any
`|ε| < 1`: the disc chart is `w = z − ε`, glued to the annulus coordinate `u = z` by `Φ_ε`.
Source: `b4cov_sphChartedSpace`; `docs/specs/RelativeFrame.md`, §4.1 items 2–3. -/
def rf4_spherePlumbing (n : ℕ) (hn : 1 ≤ n) (ε : ℂ) (hε : ‖ε‖ < 1) (hnε : n = 1 ∨ ε = 0) :
    rf4_Plumbing (rf4_sphereOuter n hn) (fun _ ↦ ε) (OnePoint ℂ) where
  h := Homeomorph.refl _
  stationary := fun i ↦ by
    change (OpenPartialHomeomorph.refl _).trans _ ∈ _
    rw [OpenPartialHomeomorph.refl_trans]
    exact (rf4_sphereCover n hn).analytic i
  small := fun _ ↦ hε
  w := fun _ ↦ rf4_sphereDisc ε
  w_mem := fun _ ↦ rf4_sphereDisc_mem ε
  w_target := fun _ ↦ by
    rw [rf4_sphereDisc_target]
    exact subset_univ _
  cover := by
    intro p
    induction p using OnePoint.rec with
    | infty => exact Or.inl (rf4_sphere_infty_mem n)
    | coe z =>
      by_cases h : 1 < ‖z‖ ^ n
      · exact Or.inl ((rf4_sphere_coe_mem n hn z).2 h)
      · refine Or.inr ⟨⟨0, Nat.one_pos⟩, ?_⟩
        change _ ∈ (rf4_sphereDisc ε).symm '' rf4_innerDisc n 1 ε
        rw [rf4_sphereDisc_image hnε]
        exact ⟨z, by push Not at h; change ‖z‖ ^ n < 2; linarith, rfl⟩
  disjoint := fun x y hxy ↦ (hxy (Subsingleton.elim (α := Fin 1) x y)).elim
  overlap := by
    intro x
    change (Homeomorph.refl _) '' rf4_sphereO n ∩ (rf4_sphereDisc ε).symm '' rf4_innerDisc n 1 ε =
      (Homeomorph.refl _) '' (b4cov_chart0.symm '' b63r_annulus n 1)
    have e1 : ∀ s : Set (OnePoint ℂ), (Homeomorph.refl (OnePoint ℂ)) '' s = s := image_id
    rw [e1, e1, rf4_sphereDisc_image hnε]
    ext p
    constructor
    · rintro ⟨hp, z, hz, rfl⟩
      exact ⟨z, ⟨(rf4_sphere_coe_mem n hn z).1 hp, by simpa using hz⟩, b4cov_chart0_symm z⟩
    · rintro ⟨z, hz, rfl⟩
      rw [b4cov_chart0_symm]
      exact ⟨(rf4_sphere_coe_mem n hn z).2 hz.1, z, by simpa using hz.2, rfl⟩
  glue := by
    intro x u hu
    change u ∈ b63r_annulus n 1 at hu
    change b4cov_chart0.symm u ∈ (rf4_sphereDisc ε).source ∧
      rf4_sphereDisc ε (b4cov_chart0.symm u) = rf4_rootMap n ε u
    have hu0 : u ≠ 0 := rf4_closedAnnulus_ne_zero hn one_pos (rf4_annulus_subset_closed n 1 hu)
    rw [b4cov_chart0_symm, rf4_sphereDisc_source, b4cov_chart0_source, rf4_sphereDisc_coe,
      rf4_sphere_rootMap hnε hu0]
    exact ⟨mem_range_self u, rfl⟩

/-- The plumbing premise is satisfiable on a compact connected surface with one branched disc
(degree two). -/
example : Nonempty (rf4_Plumbing (rf4_sphereOuter 2 (by norm_num)) (fun _ ↦ 0) (OnePoint ℂ)) ∧
    (rf4_sphereOuter 2 (by norm_num)).m = 1 ∧ (rf4_sphereOuter 2 (by norm_num)).deg ⟨0, by decide⟩ = 2 :=
  ⟨⟨rf4_spherePlumbing 2 (by norm_num) 0 (by simp) (Or.inr rfl)⟩, rfl, rfl⟩

/-- The plumbing premise is satisfiable with a moving value `ε = 1/2 ≠ 0`, where the gluing
`Φ_ε(u) = u − ε` is not the identity. -/
example : Nonempty (rf4_Plumbing (rf4_sphereOuter 1 le_rfl) (fun _ ↦ 1 / 2) (OnePoint ℂ)) ∧
    (1 / 2 : ℂ) ≠ 0 ∧ rf4_rootMap 1 (1 / 2) (3 / 2) ≠ 3 / 2 := by
  refine ⟨⟨rf4_spherePlumbing 1 le_rfl (1 / 2) (by norm_num) (Or.inl rfl)⟩, by norm_num, ?_⟩
  rw [rf4_sphere_rootMap (Or.inl rfl) (by norm_num)]
  norm_num

/-- The sphere is a compact connected Hausdorff surface, so the compact statements apply. -/
example : T2Space (OnePoint ℂ) ∧ CompactSpace (OnePoint ℂ) ∧ ConnectedSpace (OnePoint ℂ) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end Sphere

/-! ## Chain check

The stage served is the kernel frame of `b63r_analytic_kernel_frame` (stage A3), which C12 and D1
turn into elements of `b63e_relForm` (`PrymVariationFramesDefs.lean:25`). Over a parameter set
`W` with an analytic moving value `ε(t)` in the polydisc and a plumbing datum of each fibre `X t`
of constant genus `d`, C5, C10 and C7 supply exactly the premises of A3: an analytic operator
family, Fredholm at `t₀`, with kernels of constant dimension `d`. The frame vectors then glue,
fibre by fibre, to holomorphic forms on `X t` through `rf4_kernel_equiv`. -/

example {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} (D : rf4_OuterData C O) {k d : ℕ} (W : Set (Fin k → ℂ)) (hW : IsOpen W)
    (ε : (Fin k → ℂ) → Fin D.m → ℂ) (hε : AnalyticOnNhd ℂ ε W)
    (hεW : MapsTo ε W (rf4_polydisc D.m D.r))
    (X : (Fin k → ℂ) → Type) [∀ t, TopologicalSpace (X t)] [∀ t, ChartedSpace ℂ (X t)]
    [∀ t, IsManifold 𝓘(ℂ, ℂ) ω (X t)] [∀ t, T2Space (X t)] [∀ t, CompactSpace (X t)]
    [∀ t, ConnectedSpace (X t)] (S : ∀ t ∈ W, rf4_Plumbing D (ε t) (X t))
    (hg : ∀ t ∈ W, Module.finrank ℂ (b3_HolForm ℂ (X t)) = d) (t₀ : Fin k → ℂ) (ht₀ : t₀ ∈ W) :
    ∃ W' : Set (Fin k → ℂ), IsOpen W' ∧ t₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ e : Fin d → (Fin k → ℂ) → rf4_Src D, (∀ i, AnalyticOnNhd ℂ (e i) W') ∧
        ∀ t ∈ W', LinearIndependent ℂ (fun i ↦ e i t) ∧
          Submodule.span ℂ (Set.range fun i ↦ e i t) = (rf4_delta D (ε t)).ker :=
  b63r_analytic_kernel_frame W hW (fun t ↦ rf4_delta D (ε t))
    ((rf4_delta_analytic D).comp hε hεW) t₀ ht₀ (rf4_delta_isFredholm (S t₀ ht₀))
    (fun t ht ↦ (rf4_ker_finrank (S t ht)).2.trans (hg t ht))

/-- Each kernel vector glues to a holomorphic form on its fibre, the fibre value of the future
relative form. -/
example {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (k : rf4_Src D) (hk : k ∈ (rf4_delta D ε).ker) :
    rf4_glue S k ∈ b3_HolForm ℂ X := by
  obtain ⟨e, he⟩ := rf4_kernel_equiv S
  rw [← he ⟨k, hk⟩]
  exact (e ⟨k, hk⟩).2

#check @b63e_relForm

#print axioms rf4_testOuter
#print axioms rf4_testForm
#print axioms rf4_testSectors
#print axioms rf4_sphereOuter
#print axioms rf4_spherePlumbing
#print axioms rf4_delta
#print axioms rf4_glue
#print axioms rf4_sectorOp_apply

end HodgeLean.Foundations.Program
