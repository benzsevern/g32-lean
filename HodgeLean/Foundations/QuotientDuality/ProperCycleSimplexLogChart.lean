import HodgeLean.Foundations.QuotientDuality.ProperCycleBarycentricProduct
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Actual vector-space coordinates on positive simplices -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual positive part of a finite barycentric simplex.
Source: Munkres, Elements of Algebraic Topology, section 2, simplex interiors.
HC no distance; AV milestone no distance. -/
abbrev ProperCyclePositiveSimplex (ι : Type) [Fintype ι] :=
  {p : stdSimplex ℝ ι | ∀ i, 0 < p.val i}

/-- The vector-space coordinates fix the logarithm of the distinguished coordinate at zero.
Source: Munkres, Elements of Algebraic Topology, section 2, simplex interiors and affine coordinates.
HC no distance; AV milestone no distance. -/
def properCycle_log_tangent (j : ι) : Submodule ℝ (ι → ℝ) :=
  LinearMap.ker (LinearMap.proj j)

/-- The denominator in the normalized exponential coordinate map is positive.
Source: Rudin, Principles of Mathematical Analysis, third edition, chapter 8, exponential function.
HC no distance; AV milestone no distance. -/
lemma properCycle_exp_sum_pos (j : ι) (v : ι → ℝ) : 0 < ∑ i, Real.exp (v i) := by
  exact Finset.sum_pos' (fun i _ => (Real.exp_pos (v i)).le)
    ⟨j, Finset.mem_univ j, Real.exp_pos (v j)⟩

/-- Normalized exponentials give actual positive barycentric coordinates.
Source: Rudin, Principles of Mathematical Analysis, third edition, chapter 8, exponential function.
HC no distance; AV milestone no distance. -/
def properCycle_simplex_exp (j : ι) (v : ι → ℝ) : ProperCyclePositiveSimplex ι :=
  ⟨⟨fun i => Real.exp (v i) / (∑ k, Real.exp (v k)), by
      constructor
      · intro i
        exact div_nonneg (Real.exp_pos _).le (properCycle_exp_sum_pos j v).le
      · rw [← Finset.sum_div]
        exact div_self (ne_of_gt (properCycle_exp_sum_pos j v))⟩,
    fun i => div_pos (Real.exp_pos _) (properCycle_exp_sum_pos j v)⟩

/-- Logarithmic ratios land in the actual distinguished-coordinate kernel.
Source: Rudin, Principles of Mathematical Analysis, third edition, chapter 8, logarithm and exponential.
HC no distance; AV milestone no distance. -/
def properCycle_simplex_log (j : ι) (p : ProperCyclePositiveSimplex ι) : properCycle_log_tangent j :=
  ⟨fun i => Real.log (p.val.val i) - Real.log (p.val.val j), by
    change Real.log (p.val.val j) - Real.log (p.val.val j) = 0
    exact sub_self _⟩

/-- The normalized exponential coordinate map is continuous into the actual positive simplex.
Source: Rudin, Principles of Mathematical Analysis, third edition, chapter 8, continuity of exponential.
HC no distance; AV milestone no distance. -/
lemma properCycle_simplex_exp_continuous (j : ι) : Continuous (properCycle_simplex_exp j) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (Real.continuous_exp.comp (continuous_apply i)).div
    (continuous_finsetSum Finset.univ (fun k _ => Real.continuous_exp.comp (continuous_apply k)))
    (fun v => ne_of_gt (properCycle_exp_sum_pos j v))

/-- Logarithmic coordinates vary continuously on the actual positive simplex.
Source: Rudin, Principles of Mathematical Analysis, third edition, chapter 8, continuity of logarithm.
HC no distance; AV milestone no distance. -/
lemma properCycle_simplex_log_continuous (j : ι) : Continuous (properCycle_simplex_log j) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  have hc (k : ι) : Continuous (fun p : ProperCyclePositiveSimplex ι => p.val.val k) :=
    (continuous_apply k).comp (continuous_subtype_val.comp continuous_subtype_val)
  exact ((hc i).log (fun p => ne_of_gt (p.property i))).sub
    ((hc j).log (fun p => ne_of_gt (p.property j)))

/-- Positive barycentric simplices are explicitly homeomorphic to the actual vector-space kernel.
Source: Munkres, Elements of Algebraic Topology, section 2; Rudin, Principles of Mathematical Analysis,
third edition, chapter 8, logarithmic ratios and normalized exponentials.
HC no distance; AV milestone no distance. -/
def properCycle_positive_simplex_log_homeomorph (j : ι) :
    ProperCyclePositiveSimplex ι ≃ₜ properCycle_log_tangent j where
  toFun := properCycle_simplex_log j
  invFun v := properCycle_simplex_exp j v.val
  left_inv := by
    intro p
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change Real.exp (Real.log (p.val.val i) - Real.log (p.val.val j)) /
      (∑ k, Real.exp (Real.log (p.val.val k) - Real.log (p.val.val j))) = p.val.val i
    have he (k : ι) : Real.exp (Real.log (p.val.val k) - Real.log (p.val.val j)) =
        p.val.val k / p.val.val j := by
      rw [Real.exp_sub, Real.exp_log (p.property k), Real.exp_log (p.property j)]
    simp_rw [he]
    rw [← Finset.sum_div, p.val.property.2]
    field_simp [ne_of_gt (p.property j)]
  right_inv := by
    intro v
    apply Subtype.ext
    funext i
    change Real.log (Real.exp (v.val i) / (∑ k, Real.exp (v.val k))) -
      Real.log (Real.exp (v.val j) / (∑ k, Real.exp (v.val k))) = v.val i
    have hz : (∑ k, Real.exp (v.val k)) ≠ 0 := ne_of_gt (properCycle_exp_sum_pos j v.val)
    have hj : v.val j = 0 := v.property
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) hz,
      Real.log_div (ne_of_gt (Real.exp_pos _)) hz, Real.log_exp, Real.log_exp, hj]
    ring
  continuous_toFun := properCycle_simplex_log_continuous j
  continuous_invFun := (properCycle_simplex_exp_continuous j).comp continuous_subtype_val

end HodgeLean.Foundations.QuotientDuality
