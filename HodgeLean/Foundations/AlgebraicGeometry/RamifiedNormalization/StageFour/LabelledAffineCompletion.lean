import Mathlib.Topology.Compactification.OnePoint.Basic

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- An exhaustive labelled affine chart and one uniquely labelled point at infinity retain all labels in the one-point coordinate. -/
theorem labelled_affine_completion
    {X I A C : Type*} (U : Set X) (q : X → C) (r : X → OnePoint A)
    (b : I → C) (hb : Function.Injective b)
    (E : U ≃ I × A)
    (hU : ∀ x, x ∈ U ↔ r x ≠ ∞)
    (hq : ∀ x : U, q x.val = b (E x).1)
    (hr : ∀ x : U, r x.val = ((E x).2 : OnePoint A))
    (hlabels : ∀ x, ∃ i, q x = b i)
    (hinfty : ∀ i, ∃! x, q x = b i ∧ r x = ∞) :
    ∃ F : X ≃ I × OnePoint A, ∀ x, q x = b (F x).1 ∧ r x = (F x).2 := by
  let l : X → I := fun x => Classical.choose (hlabels x)
  have hl (x : X) : q x = b (l x) := Classical.choose_spec (hlabels x)
  have hlabel (x : U) : l x.val = (E x).1 := hb ((hl x.val).symm.trans (hq x))
  let f : X → I × OnePoint A := fun x => (l x, r x)
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      have he₁ : l x = l y := congrArg Prod.fst he
      have he₂ : r x = r y := congrArg Prod.snd he
      by_cases hx : r x = ∞
      · obtain ⟨z, hz, huniq⟩ := hinfty (l x)
        exact (huniq x ⟨hl x, hx⟩).trans (huniq y
          ⟨(hl y).trans (congrArg b he₁.symm), he₂.symm.trans hx⟩).symm
      · have hy : r y ≠ ∞ := fun hy => hx (he₂.trans hy)
        let xU : U := ⟨x, (hU x).mpr hx⟩
        let yU : U := ⟨y, (hU y).mpr hy⟩
        have hpair : E xU = E yU := by
          apply Prod.ext
          · exact (hlabel xU).symm.trans (he₁.trans (hlabel yU))
          · apply OnePoint.coe_injective
            exact (hr xU).symm.trans (he₂.trans (hr yU))
        exact congrArg Subtype.val (E.injective hpair)
    · rintro ⟨i, z⟩
      cases z with
      | infty =>
        obtain ⟨x, hx, _⟩ := hinfty i
        refine ⟨x, Prod.ext ?_ hx.2⟩
        exact hb ((hl x).symm.trans hx.1)
      | coe a =>
        let x := E.symm (i, a)
        have hx := E.apply_symm_apply (i, a)
        refine ⟨x.val, Prod.ext ?_ ?_⟩
        · exact (hlabel x).trans (congrArg Prod.fst hx)
        · exact (hr x).trans (congrArg (fun z : I × A => (z.2 : OnePoint A)) hx)
  exact ⟨Equiv.ofBijective f hf, fun x => ⟨hl x, rfl⟩⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
