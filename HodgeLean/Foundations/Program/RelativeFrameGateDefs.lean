import HodgeLean.Foundations.Mathlib.FredholmAnalytic
import HodgeLean.Foundations.Program.RiemannRoch
import HodgeLean.Foundations.DolbeaultCurve2Defs

/-! # Chart coefficients for the relative-frame gate
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program
local instance rf2_decidableDefs (p : Prop) : Decidable p := Classical.propDecidable p

/-- Finite chart pieces, with compact containment in the coordinate target.
Source: Forster, *Lectures on Riemann Surfaces*, §2; RelativeFrame §5, A13. -/
structure rf2_PieceCover (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (O : Set C) where
  n : ℕ
  chart : Fin n → OpenPartialHomeomorph C ℂ
  analytic : ∀ i, chart i ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C
  piece : Fin n → Set ℂ
  isOpen : ∀ i, IsOpen (piece i)
  compact : ∀ i, IsCompact (closure (piece i))
  contained : ∀ i, closure (piece i) ⊆ (chart i).target
  covers : O = ⋃ i, (chart i).symm '' piece i

/-- Compatible bounded holomorphic coefficient tuples; the inherited finite-product norm is
 the maximum of the piece norms.
Source: Forster, *Lectures on Riemann Surfaces*, §9; RelativeFrame §5, A14. -/
def rf2_bddForm {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (P : rf2_PieceCover C O) :
    Submodule ℂ (∀ i, b63r_bddHol (P.piece i)) where
  carrier := {f | ∀ i j (z : P.piece i) (w : P.piece j),
    (P.chart i).symm z = (P.chart j).symm w →
    (f i : P.piece i →ᵇ ℂ) z = (f j : P.piece j →ᵇ ℂ) w *
      deriv (P.chart j ∘ (P.chart i).symm) z}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg i j z w h
    change (f i : P.piece i →ᵇ ℂ) z + (g i : P.piece i →ᵇ ℂ) z = _
    rw [hf i j z w h, hg i j z w h]
    change _ = ((f j : P.piece j →ᵇ ℂ) w + (g j : P.piece j →ᵇ ℂ) w) * _
    ring
  smul_mem' := by
    intro a f hf i j z w h
    change a * (f i : P.piece i →ᵇ ℂ) z =
      (a * (f j : P.piece j →ᵇ ℂ) w) * _
    rw [hf i j z w h]
    ring

example {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (P : rf2_PieceCover C O) :
    (0 : ∀ i, b63r_bddHol (P.piece i)) ∈ rf2_bddForm P := (rf2_bddForm P).zero_mem

/-- Projection to a chart coefficient.
Source: RelativeFrame §5, A17; the sup norm on a finite product. -/
def rf2_bddForm_coeff {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (P : rf2_PieceCover C O) (i : Fin P.n) :
    rf2_bddForm P →L[ℂ] b63r_bddHol (P.piece i) :=
  (ContinuousLinearMap.proj i).comp (rf2_bddForm P).subtypeL

example {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (P : rf2_PieceCover C O)
    (i : Fin P.n) (f : rf2_bddForm P) : rf2_bddForm_coeff P i f = f.val i := rfl

/-- Coefficient families on the targets of the chosen surface charts.
Source: Forster, *Lectures on Riemann Surfaces*, §15. -/
abbrev rf2_Coeff (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] :=
  ∀ x : C, (chartAt ℂ x).target → ℂ

section Surface
variable (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C]

/-- Smooth `(p,q)` coefficient families with the tensor transition law. Only bidegrees
`(1,0)`, `(0,1)` and `(1,1)` are used here.
Source: Forster, *Lectures on Riemann Surfaces*, §15. -/
def rf2_smoothForms (p q : ℕ) : Submodule ℂ (rf2_Coeff C) where
  carrier := {f | (∀ x, ∃ g : ℂ → ℂ, ContDiffOn ℝ ∞ g (chartAt ℂ x).target ∧
      ∀ z, f x z = g z) ∧
    ∀ x y (z : (chartAt ℂ x).target) (w : (chartAt ℂ y).target),
      (chartAt ℂ x).symm z = (chartAt ℂ y).symm w →
      f x z = f y w * (deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) z) ^ p *
        (star (deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) z)) ^ q}
  zero_mem' := ⟨fun _ ↦ ⟨0, contDiffOn_const, fun _ ↦ rfl⟩, by simp⟩
  add_mem' := by
    rintro f g ⟨hf, hft⟩ ⟨hg, hgt⟩
    constructor
    · intro x
      obtain ⟨a, ha, hfa⟩ := hf x
      obtain ⟨b, hb, hgb⟩ := hg x
      exact ⟨a + b, ha.add hb, fun z ↦ by simp only [Pi.add_apply, hfa, hgb]⟩
    · intro x y z w h
      simp only [Pi.add_apply, hft x y z w h, hgt x y z w h]
      ring
  smul_mem' := by
    rintro a f ⟨hf, hft⟩
    constructor
    · intro x
      obtain ⟨g, hg, hfg⟩ := hf x
      exact ⟨a • g, hg.const_smul a, fun z ↦ by simp only [Pi.smul_apply, hfg]⟩
    · intro x y z w h
      simp only [Pi.smul_apply, smul_eq_mul, hft x y z w h]
      ring

example (p q : ℕ) : (0 : rf2_Coeff C) ∈ rf2_smoothForms C p q :=
  (rf2_smoothForms C p q).zero_mem

/-- Zero extension of a chart coefficient, used only for derivatives inside its open target.
Source: RelativeFrame §4.5, C8a--C8c. -/
def rf2_extend (f : rf2_Coeff C) (x : C) (z : ℂ) : ℂ :=
  if h : z ∈ (chartAt ℂ x).target then f x ⟨z, h⟩ else 0

example (f : rf2_Coeff C) (x : C) (z : (chartAt ℂ x).target) :
    rf2_extend C f x z = f x z := by unfold rf2_extend; exact dite_eq_left z.2

/-- The coefficient of `∂̄(v dz)` is `-∂v/∂z̄`, fixing the wedge sign.
Source: RelativeFrame §4.5, step 1; Forster, §15. -/
def rf2_dbar10 (f : rf2_Coeff C) : rf2_Coeff C :=
  fun x z ↦ -wirtingerDbar (rf2_extend C f x) z

example (f : rf2_Coeff C) (x : C) (z : (chartAt ℂ x).target) :
    rf2_dbar10 C f x z = -wirtingerDbar (rf2_extend C f x) z := rfl

/-- Smooth `(1,1)` boundaries, as a subspace of smooth `(1,1)` forms.
Source: Forster, §15; RelativeFrame §4.5. -/
def rf2_boundaries : Submodule ℂ (rf2_smoothForms C 1 1) :=
  (Submodule.span ℂ (rf2_dbar10 C '' (rf2_smoothForms C 1 0 : Set (rf2_Coeff C)))).comap
    (rf2_smoothForms C 1 1).subtype

example : (0 : rf2_smoothForms C 1 1) ∈ rf2_boundaries C := (rf2_boundaries C).zero_mem

/-- Forms vanishing on an open neighbourhood, represented on every chart.
Source: RelativeFrame §4.5, the spaces `A_N` and `Θ_N`. -/
def rf2_vanishing (p q : ℕ) (N : Set C) : Submodule ℂ (rf2_smoothForms C p q) where
  carrier := {f | ∀ x (z : (chartAt ℂ x).target), (chartAt ℂ x).symm z ∈ N → f.val x z = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg x z hz; change f.val x z + g.val x z = 0; rw [hf x z hz, hg x z hz, add_zero]
  smul_mem' := by intro a f hf x z hz; change a * f.val x z = 0; rw [hf x z hz, mul_zero]

example (p q : ℕ) (N : Set C) : (0 : rf2_smoothForms C p q) ∈ rf2_vanishing C p q N :=
  (rf2_vanishing C p q N).zero_mem

/-- Coefficient of the normalized meromorphic differential in an uncentred chosen chart.
Source: Forster, §14; `b4c_residue_normalizedForm` repairs removable point values. -/
def rf2_meroCoeff (w : b4c_MeroForm ℂ C (Module.finrank_self ℂ)) : rf2_Coeff C :=
  fun x z ↦ b4c_residue_normalizedForm (Module.finrank_self ℂ) w ⟨(chartAt ℂ x).symm z,
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ x).symm z (1 : ℂ)⟩

example (w : b4c_MeroForm ℂ C (Module.finrank_self ℂ)) (x : C) (z : (chartAt ℂ x).target) :
    rf2_meroCoeff C w x z = b4c_residue_normalizedForm (Module.finrank_self ℂ) w
      ⟨(chartAt ℂ x).symm z,
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ x).symm z (1 : ℂ)⟩ := rfl

/-- Coefficients of the scalar Dolbeault differential.
Source: Forster, §15; RelativeFrame §4.5, step 3. -/
def rf2_dbar00 (h : C → ℂ) : rf2_Coeff C :=
  fun x z ↦ wirtingerDbar (h ∘ (chartAt ℂ x).symm) z

example (h : C → ℂ) (x : C) (z : (chartAt ℂ x).target) :
    rf2_dbar00 C h x z = wirtingerDbar (h ∘ (chartAt ℂ x).symm) z := rfl

/-- Scalar boundaries in the chart model of smooth `(0,1)` forms.
Source: Forster, §15; `b4c_Dolbeault01`. -/
def rf2_boundaries01 : Submodule ℂ (rf2_smoothForms C 0 1) :=
  (Submodule.span ℂ (rf2_dbar00 C '' (b4c_SmoothFun ℂ C : Set (C → ℂ)))).comap
    (rf2_smoothForms C 0 1).subtype

example : (0 : rf2_smoothForms C 0 1) ∈ rf2_boundaries01 C :=
  (rf2_boundaries01 C).zero_mem

/-- Exact `(0,1)` forms vanishing on `N`.
Source: RelativeFrame §4.5, the space `K`. -/
def rf2_exactAway (N : Set C) : Submodule ℂ (rf2_smoothForms C 0 1) :=
  rf2_boundaries01 C ⊓ rf2_vanishing C 0 1 N

example (N : Set C) : (0 : rf2_smoothForms C 0 1) ∈ rf2_exactAway C N :=
  (rf2_exactAway C N).zero_mem

/-- Total pole multiplicity of a meromorphic differential.
Source: Forster, §14; RelativeFrame §4.5, step 6. -/
def rf2_poleBudget (w : b4c_MeroForm ℂ C (Module.finrank_self ℂ)) : ℕ :=
  (b4c_divForm (hE := Module.finrank_self ℂ) w).sum fun _ n ↦ (-n).toNat

example (w : b4c_MeroForm ℂ C (Module.finrank_self ℂ)) :
    rf2_poleBudget C w =
      (b4c_divForm (hE := Module.finrank_self ℂ) w).sum (fun _ n ↦ (-n).toNat) := rfl

end Surface

/-- Finite principal parts of `z⁻ᵐ c(z)h(z) dz` from the Taylor jets of `c` and `h`.
Index `k` is the coefficient of `z^(k-m)`.
Source: RelativeFrame §4.5, step 5; Forster, §14. -/
def rf2_principalPart (m : ℕ) (c : Fin m → ℂ) : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ) where
  toFun h k := ∑ j : Fin m, if j.val ≤ k.val then c ⟨k.val - j.val, by omega⟩ * h j else 0
  map_add' := by
    intro h k
    ext i
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp_all [mul_add]
  map_smul' := by intros; ext; simp [Finset.mul_sum, mul_comm, mul_assoc]

example (m : ℕ) (c : Fin m → ℂ) : rf2_principalPart m c 0 = 0 := map_zero _

example : rf2_principalPart 1 (fun _ ↦ 1) (fun _ ↦ 2) = (fun _ ↦ 2) := by
  ext i
  fin_cases i
  norm_num [rf2_principalPart, Fin.sum_univ_one]

/-- Two overlapping coordinate discs on the complex plane for instance checks.
Source: RelativeFrame §5, A13; the identity atlas on `ℂ`. -/
def rf2_testCover : rf2_PieceCover ℂ (⋃ i : Fin 2, Metric.ball (if i.val = 0 then (0 : ℂ) else 1) 1) where
  n := 2
  chart := fun _ ↦ OpenPartialHomeomorph.refl ℂ
  analytic := fun _ ↦ IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ, ℂ)) (n := ω) (0 : ℂ)
  piece := fun i ↦ Metric.ball (if i.val = 0 then (0 : ℂ) else 1) 1
  isOpen := fun _ ↦ Metric.isOpen_ball
  compact := fun _ ↦ (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure
    (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  contained := by intro i z hz; trivial
  covers := by simp

example : rf2_testCover.n = 2 := rfl

/-- The differential `dz` on the two overlapping pieces, with nonzero coefficients.
Source: Forster, §9; RelativeFrame §5, A14. -/
def rf2_testForm : rf2_bddForm rf2_testCover :=
  ⟨fun _ ↦ ⟨BoundedContinuousFunction.const _ 1,
    ⟨fun _ ↦ 1, differentiableOn_const 1, fun _ ↦ rfl⟩⟩, by
    intro i j z w h
    change (1 : ℂ) = 1 * deriv ((id : ℂ → ℂ) ∘ id) (z : ℂ)
    simp only [Function.comp_id, deriv_id, mul_one]⟩

example : rf2_testForm ≠ 0 := by
  intro h
  have hh := congrArg (fun f : rf2_bddForm rf2_testCover ↦
    (f.val (0 : Fin 2) : rf2_testCover.piece (0 : Fin 2) →ᵇ ℂ)
      ⟨0, by change (0 : ℂ) ∈ Metric.ball 0 1; norm_num⟩) h
  exact one_ne_zero hh

example : (1 / 2 : ℂ) ∈ rf2_testCover.piece (0 : Fin 2) ∩ rf2_testCover.piece (1 : Fin 2) := by
  change (1 / 2 : ℂ) ∈ Metric.ball 0 1 ∧ (1 / 2 : ℂ) ∈ Metric.ball 1 1
  norm_num [Metric.mem_ball, dist_eq_norm, Complex.norm_def]

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- A meromorphic test differential with a genuine double pole.
Source: Forster, §14; `b4c_sphere_dz` and `b4c_dz_sphere_mem`. -/
def rf2_testMero : b4c_MeroForm ℂ (OnePoint ℂ) (Module.finrank_self ℂ) :=
  ⟨b4c_dz_sphere, b4c_dz_sphere_mem⟩

example : (rf2_testMero : TangentBundle 𝓘(ℂ, ℂ) (OnePoint ℂ) → ℂ) ≠ 0 := by
  intro h
  have hh := congrFun h ⟨((0 : ℂ) : OnePoint ℂ), (1 : ℂ)⟩
  apply (one_ne_zero : (1 : ℂ) ≠ 0)
  simpa only [rf2_testMero, b4c_dz_sphere, OnePoint.coe_ne_infty, ite_false, Pi.zero_apply]
    using hh

example : rf2_poleBudget (OnePoint ℂ) rf2_testMero = 2 := by
  change Finsupp.sum (b4c_divForm (hE := Module.finrank_self ℂ) b4c_dz_sphere) _ = 2
  rw [b4c_sphere_dz.1]
  rw [Finsupp.smul_single]
  change (Finsupp.single (OnePoint.infty : OnePoint ℂ) (-2 : ℤ)).sum _ = 2
  rw [Finsupp.sum_single_index]
  · norm_num
  · simp

example : ∃ x : OnePoint ℂ,
    meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) rf2_testMero x) 0 ≠ ⊤ := by
  refine ⟨((0 : ℂ) : OnePoint ℂ), ?_⟩
  change meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ)
    b4c_dz_sphere ((0 : ℂ) : OnePoint ℂ)) 0 ≠ ⊤
  rw [meromorphicOrderAt_congr
    ((b4c_dz_sphere_loc_coe_eventuallyEq (0 : ℂ)).filter_mono nhdsWithin_le_nhds)]
  have hn : b4cov_lineEquiv (E := ℂ) (Module.finrank_self ℂ) 1 ≠ 0 := by
    intro h
    apply (one_ne_zero : (1 : ℂ) ≠ 0)
    exact (b4cov_lineEquiv (Module.finrank_self ℂ)).injective
      (h.trans (map_zero _).symm)
  rw [meromorphicOrderAt_const]
  simp only [hn, ite_false, ne_eq, WithTop.zero_ne_top, not_false_eq_true]

#print axioms rf2_testCover
#print axioms rf2_testForm
#print axioms rf2_testMero
#print axioms rf2_meroCoeff
#print axioms rf2_principalPart

end HodgeLean.Foundations.Program
