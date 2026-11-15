import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathMarking
import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathComposite

/-! # The affine correction between the two rational normalizations -/
noncomputable section
open Set Topology
namespace HodgeLean.Foundations.Program

/-- The change between rational normalizations has an infinity-fixing ambient motion.
Source: `b65x_mob`; `b65p_mobius`; `rtc_affine_isotopy`. -/
theorem rtc_mobius_correction_isotopy (a b : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : b - a ≠ 0) :
    ∃ D : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ D (t, z))) ∧
      (∀ z, D (0, z) = z) ∧
      (∀ z, D (1, z) = b65p_mobius a b (b65x_mob.symm z)) ∧
      (∀ t, D (t, OnePoint.infty) = OnePoint.infty) := by
  let β : ℂ := -a * b / (b - a)
  let α : ℂ := b / (b - a)
  let c : ℂ := β / b65x_beta
  let d : ℂ := α - c * b65x_alpha
  have hβ : β ≠ 0 := div_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha) hb) hab
  have hc : c ≠ 0 := div_ne_zero hβ b65x_beta_ne
  have hform (w : OnePoint ℂ) :
      OnePoint.map (fun z ↦ c * z + d) (b65x_mob w) = b65p_mobius a b w := by
    induction w using OnePoint.rec with
    | infty =>
      rw [b65x_mob_infty, OnePoint.map_some]
      change ((c * b65x_alpha + d : ℂ) : OnePoint ℂ) = ((α : ℂ) : OnePoint ℂ)
      congr 1
      dsimp [d]
      ring
    | coe z =>
      by_cases hz : z = 0
      · subst z
        rw [b65x_mob_zero]
        simp [b65p_mobius]
      · rw [b65x_mob_coe hz, OnePoint.map_some]
        change ((c * b65s_normalize b65x_ma b65x_mb z + d : ℂ) : OnePoint ℂ) = _
        rw [show b65p_mobius a b (z : OnePoint ℂ) =
          ((b65s_normalize a b z : ℂ) : OnePoint ℂ) by simp [b65p_mobius, hz]]
        congr 1
        dsimp [c, d, α, β, b65x_alpha, b65x_beta, b65s_normalize]
        field_simp [hz, hab, b65x_ma_ne, b65x_mb_ne, b65x_mab_ne]
        <;> ring
  obtain ⟨D, hD, hD0, hD1, hDI⟩ := rtc_affine_isotopy c d hc
  refine ⟨D, hD, hD0, fun z ↦ ?_, hDI⟩
  rw [hD1, ← hform (b65x_mob.symm z), b65x_mob.apply_symm_apply]

end HodgeLean.Foundations.Program
