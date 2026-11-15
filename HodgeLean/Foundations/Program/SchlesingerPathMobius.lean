import HodgeLean.Foundations.Program.SchlesingerPathDefs
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.MetricSpace.Bounded

noncomputable section
open Set Metric Filter Bornology
open scoped Topology
namespace HodgeLean.Foundations.Program

def b65p_sphereInv (w : OnePoint ℂ) : OnePoint ℂ :=
  w.elim ((0 : ℂ) : OnePoint ℂ)
    (fun z ↦ if z = 0 then OnePoint.infty else ((z⁻¹ : ℂ) : OnePoint ℂ))

theorem b65p_sphereInv_involutive : Function.Involutive b65p_sphereInv := by
  intro w
  induction w using OnePoint.rec with
  | infty => simp [b65p_sphereInv]
  | coe z =>
    by_cases hz : z = 0
    · simp [b65p_sphereInv, hz]
    · simp [b65p_sphereInv, hz, inv_ne_zero hz]

theorem b65p_sphereInv_continuous : Continuous b65p_sphereInv := by
  have hfilters : coclosedCompact ℂ = cobounded ℂ := by
    rw [coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact]
  apply (OnePoint.continuous_iff _).mpr
  constructor
  · have hlim := OnePoint.continuous_coe.continuousAt.tendsto.comp
      (tendsto_inv₀_cobounded (α := ℂ))
    rw [← hfilters] at hlim
    apply hlim.congr'
    have hz : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ≠ 0 := by
      rw [coclosedCompact_eq_cocompact]
      exact (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
    filter_upwards [hz] with z hz
    simp [b65p_sphereInv, hz]
  · apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z = 0
    · subst z
      change ContinuousAt (fun z : ℂ ↦ if z = 0 then OnePoint.infty else
        ((z⁻¹ : ℂ) : OnePoint ℂ)) 0
      have heq : (fun z : ℂ ↦ if z = 0 then OnePoint.infty else
          ((z⁻¹ : ℂ) : OnePoint ℂ)) =
          Function.update (fun z : ℂ ↦ ((z⁻¹ : ℂ) : OnePoint ℂ)) 0 OnePoint.infty := by
        funext z
        by_cases hz : z = 0 <;> simp [Function.update, hz]
      rw [heq, continuousAt_update_same]
      exact OnePoint.tendsto_coe_infty.comp (hfilters ▸ tendsto_inv₀_nhdsNE_zero)
    · have hc := OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)
      apply hc.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with x hx
      simp [b65p_sphereInv, hx]

def b65p_sphereInvHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ where
  toFun := b65p_sphereInv
  invFun := b65p_sphereInv
  left_inv := b65p_sphereInv_involutive
  right_inv := b65p_sphereInv_involutive
  continuous_toFun := b65p_sphereInv_continuous
  continuous_invFun := b65p_sphereInv_continuous

def b65p_mobiusHomeomorph (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : b - a ≠ 0) : OnePoint ℂ ≃ₜ OnePoint ℂ :=
  b65p_sphereInvHomeomorph.trans
    (((Homeomorph.mulLeft₀ (-a * b / (b - a))
      (div_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha) hb) hab)).trans
        (Homeomorph.addLeft (b / (b - a)))).onePointCongr)

theorem b65p_mobiusHomeomorph_apply (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : b - a ≠ 0) : ⇑(b65p_mobiusHomeomorph a b ha hb hab) = b65p_mobius a b := by
  funext w
  change OnePoint.map (fun t : ℂ ↦ b / (b - a) + (-a * b / (b - a)) * t)
    (b65p_sphereInv w) = b65p_mobius a b w
  induction w using OnePoint.rec with
  | infty =>
    change ((b / (b - a) + (-a * b / (b - a)) * 0 : ℂ) : OnePoint ℂ) = _
    simp [b65p_mobius]
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp [b65p_sphereInv, b65p_mobius, OnePoint.map]
      rfl
    · change OnePoint.map (fun t : ℂ ↦ b / (b - a) + (-a * b / (b - a)) * t)
        (if z = 0 then OnePoint.infty else ((z⁻¹ : ℂ) : OnePoint ℂ)) =
        if z = 0 then OnePoint.infty else ((b65s_normalize a b z : ℂ) : OnePoint ℂ)
      simp only [ite_eq_right hz]
      change ((b / (b - a) + (-a * b / (b - a)) * z⁻¹ : ℂ) : OnePoint ℂ) = _
      congr 1
      unfold b65s_normalize
      field_simp
      ring

theorem b65p_mobius_labels (q : Fin 12 → ℂ) (hne : ∀ j, q j ≠ 0)
    (hab : q 11 - q 10 ≠ 0) (k : Fin 13) :
    b65p_mobius (q 10) (q 11)
      (Fin.append (fun i : Fin 10 ↦ ((q (Fin.castLE (by norm_num) i) : ℂ) : OnePoint ℂ))
        ![((q 10 : ℂ) : OnePoint ℂ), ((q 11 : ℂ) : OnePoint ℂ), ((0 : ℂ) : OnePoint ℂ)] k) =
      b6_branch (b65p_chartPoint q) k := by
  fin_cases k <;>
    simp [Fin.append, Fin.addCases, b65p_mobius, b65p_chartPoint, b6_branch, hne,
      b65s_normalize, hab, mul_comm]

end HodgeLean.Foundations.Program
