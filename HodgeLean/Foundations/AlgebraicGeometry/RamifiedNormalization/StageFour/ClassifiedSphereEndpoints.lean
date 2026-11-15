import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- An exhaustive finite power chart determines the zero and infinity endpoints of its global labelled sphere coordinate. -/
theorem classified_sphere_endpoints
    {X TA I : Type*} (U : Set X) (H : TA ≃ U) (E : TA ≃ I × ℂ)
    (G : X ≃ I × OnePoint ℂ) (v : X → OnePoint ℂ)
    (k : I → ℂ) (hk : ∀ i, k i ≠ 0) (n : ℕ) (hn : 0 < n)
    (hG : ∀ a, G (H a).val = ((E a).1, ((E a).2 : OnePoint ℂ)))
    (hU : ∀ x, x ∈ U ↔ v x ≠ ∞)
    (hv : ∀ a, v (H a).val = ((k (E a).1 * (E a).2 ^ n : ℂ) : OnePoint ℂ)) :
    ∀ x, (v x = ((0 : ℂ) : OnePoint ℂ) ↔ (G x).2 = ((0 : ℂ) : OnePoint ℂ)) ∧
      (v x = ∞ ↔ (G x).2 = ∞) := by
  intro x
  obtain ⟨i, z, hx'⟩ : ∃ i z, G x = (i, z) := ⟨(G x).1, (G x).2, rfl⟩
  cases z with
  | coe z =>
    let a := E.symm (i, z)
    have ha : E a = (i, z) := E.apply_symm_apply (i, z)
    have he : (H a).val = x := by
      apply G.injective
      rw [hG, ha, hx']
    rw [← he, hG, hv]
    constructor
    · simp only [OnePoint.coe_injective.eq_iff, mul_eq_zero, (hk (E a).1), false_or,
        pow_eq_zero_iff (Nat.ne_of_gt hn)]
    · simp only [OnePoint.coe_ne_infty]
  | infty =>
    have hxU : x ∉ U := by
      intro hxU
      obtain ⟨a, ha⟩ := H.surjective ⟨x, hxU⟩
      have he := hG a
      have hvv : (H a).val = x := congrArg Subtype.val ha
      rw [hvv, hx'] at he
      have hh := congrArg Prod.snd he
      exact OnePoint.infty_ne_coe _ hh
    have hvx : v x = ∞ := Classical.not_not.mp (fun hvx => hxU ((hU x).mpr hvx))
    rw [hvx, hx']
    simp only [OnePoint.infty_ne_coe, iff_self, and_self]

end AlgebraicGeometry.RamifiedNormalization.StageFour
