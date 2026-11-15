import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RootLabelEvaluation

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Continuous selector and parameter evaluations give continuous gcd-labelled coordinates with their exact equality test. -/
theorem continuous_binomial_root_coordinates
    {X : Type*} [TopologicalSpace X]
    (g : ℕ) (hg : 0 < g) (κ ζ : ℂ) (hκ : κ ≠ 0) (hζ : IsPrimitiveRoot ζ g)
    (Q T : X → ℂ) (hQ : ∀ x, Q x ^ g = κ ^ g)
    (hQc : Continuous Q) (hTc : Continuous T) :
    ∃ f : X → ZMod g × ℂ, Continuous f ∧
      (∀ x, Q x = κ * ζ ^ (f x).1.val ∧ T x = (f x).2) ∧
      ∀ x y, f x = f y ↔ Q x = Q y ∧ T x = T y := by
  let H := binomialRootHomeomorph g hg κ ζ hκ hζ
  let f : X → ZMod g × ℂ := fun x => (H ⟨Q x, hQ x⟩, T x)
  have hf : Continuous f :=
    (H.continuous.comp (hQc.subtype_mk hQ)).prodMk hTc
  refine ⟨f, hf, ?_, ?_⟩
  · intro x
    refine ⟨?_, rfl⟩
    have h := congrArg Subtype.val (H.symm_apply_apply ⟨Q x, hQ x⟩)
    rw [binomialRootHomeomorph_symm_value] at h
    exact h.symm
  · intro x y
    constructor
    · intro h
      have hfst := congrArg Prod.fst h
      have hsnd := congrArg Prod.snd h
      have hxy : (⟨Q x, hQ x⟩ : {z : ℂ // z ^ g = κ ^ g}) = ⟨Q y, hQ y⟩ :=
        H.injective hfst
      exact ⟨congrArg Subtype.val hxy, hsnd⟩
    · rintro ⟨hQxy, hTxy⟩
      apply Prod.ext
      · exact congrArg H (Subtype.ext hQxy)
      · exact hTxy

end AlgebraicGeometry.RamifiedNormalization.StageFour
