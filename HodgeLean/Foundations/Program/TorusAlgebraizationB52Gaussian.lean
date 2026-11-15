import HodgeLean.Foundations.Program.TorusAlgebraizationB52Periodization
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

noncomputable section
open Filter Topology
namespace HodgeLean.Foundations.Program

theorem b52_summable_lattice_gaussian {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {c : ℝ} (hc : 0 < c) (B : ℝ) :
    Summable (fun l : L ↦ Real.exp (-c * ‖(l : E)‖ ^ 2 + B * ‖(l : E)‖)) := by
  let r : ℝ := -(Module.finrank ℤ L : ℝ) - 1
  have hr : r < -(Module.finrank ℤ L : ℝ) := by dsimp [r]; linarith
  have hclosed : IsClosed (L : Set E) := L.toAddSubgroup.isClosed_of_discreteTopology
  have hnorm : Tendsto (fun l : L ↦ ‖(l : E)‖) cofinite atTop :=
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding hclosed.isClosedEmbedding_subtypeVal
  have hdecay := (rexp_neg_quadratic_isLittleO_rpow_atTop (neg_neg_of_pos hc) B r).bound
    (show (0 : ℝ) < 1 by norm_num)
  apply (ZLattice.summable_norm_rpow L r hr).of_norm_bounded_eventually
  filter_upwards [hnorm.eventually hdecay] with l hl
  convert! hl using 1 <;>
    simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (l : E)) r)]

#print axioms b52_summable_lattice_gaussian

theorem b52_quadratic_lower_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (q : E → ℝ)
    (hq : Continuous q) (hscale : ∀ (a : ℝ) (x : E), q (a • x) = a ^ 2 * q x)
    (hpos : ∀ x, x ≠ 0 → 0 < q x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ q x := by
  have hzero : q 0 = 0 := by simpa using hscale 0 0
  cases subsingleton_or_nontrivial E
  · refine ⟨1, zero_lt_one, fun x ↦ ?_⟩
    rw [Subsingleton.elim x 0, norm_zero, hzero]
    norm_num
  obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hq.continuousOn
  have hvnorm : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp hv
  have hv0 : v ≠ 0 := by intro h; simpa [h] using hvnorm
  refine ⟨q v, hpos v hv0, fun x ↦ ?_⟩
  by_cases hx : x = 0
  · simp only [hx, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, hzero, le_refl]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg x),
      inv_mul_cancel₀ hn]
  calc
    q v * ‖x‖ ^ 2 ≤ q ((‖x‖⁻¹ : ℝ) • x) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hmin (mem_sphere_zero_iff_norm.mpr hunit)) (sq_nonneg _)
    _ = q x := by rw [hscale]; field_simp

#print axioms b52_quadratic_lower_bound

theorem b52_summable_positive_quadratic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (q : E → ℝ)
    (hq : Continuous q) (hscale : ∀ (a : ℝ) (x : E), q (a • x) = a ^ 2 * q x)
    (hpos : ∀ x, x ≠ 0 → 0 < q x) (p : E → ℝ) (B : ℝ)
    (hp : ∀ x, p x ≤ B * ‖x‖) :
    Summable (fun l : L ↦ Real.exp (-q l + p l)) := by
  obtain ⟨c, hc, hbound⟩ := b52_quadratic_lower_bound q hq hscale hpos
  apply (b52_summable_lattice_gaussian L hc B).of_norm_bounded
  intro l
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hq' := hbound l
  have hp' := hp l
  nlinarith

#print axioms b52_summable_positive_quadratic

end HodgeLean.Foundations.Program
