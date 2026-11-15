import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ClassifiedSphereEndpoints

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- An exhaustive finite chart and its specified infinity complement retain the literal power projection on the entire labelled sphere. -/
theorem classified_sphere_power_projection
    {X TA I : Type*} (U : Set X) (H : TA ≃ U) (E : TA ≃ I × ℂ)
    (G : X ≃ I × OnePoint ℂ) (v : X → OnePoint ℂ) (k : I → ℂ) (n : ℕ)
    (hG : ∀ a, G (H a).val = ((E a).1, ((E a).2 : OnePoint ℂ)))
    (hU : ∀ x, x ∈ U ↔ v x ≠ ∞)
    (hv : ∀ a, v (H a).val = ((k (E a).1 * (E a).2 ^ n : ℂ) : OnePoint ℂ)) :
    ∀ x, v x = Option.map (fun z : ℂ => k (G x).1 * z ^ n) (G x).2 := by
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
    rfl
  | infty =>
    have hxU : x ∉ U := by
      intro hxU
      obtain ⟨a, ha⟩ := H.surjective ⟨x, hxU⟩
      have he := hG a
      have hvv : (H a).val = x := congrArg Subtype.val ha
      rw [hvv, hx'] at he
      exact OnePoint.infty_ne_coe _ (congrArg Prod.snd he)
    have hvx : v x = ∞ := Classical.not_not.mp (fun hvx => hxU ((hU x).mpr hvx))
    rw [hvx, hx']
    rfl

end AlgebraicGeometry.RamifiedNormalization.StageFour
