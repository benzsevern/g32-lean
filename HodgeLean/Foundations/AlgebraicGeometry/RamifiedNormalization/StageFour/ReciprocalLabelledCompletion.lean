import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.LabelledAffineCompletion

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A reciprocal chart supplies precisely one point at infinity for each retained finite-chart selector label. -/
theorem reciprocal_labelled_completion
    {X I J A C : Type*} [Zero A]
    (U : Set X) (q : X → C) (r : X → OnePoint A)
    (b : I → C) (b' : J → C) (hb : Function.Injective b) (hb' : Function.Injective b')
    (e : I ≃ J) (he : ∀ i, b' (e i) = b i)
    (E : U ≃ I × A)
    (hU : ∀ x, x ∈ U ↔ r x ≠ ∞)
    (hq : ∀ x : U, q x.val = b (E x).1)
    (hr : ∀ x : U, r x.val = ((E x).2 : OnePoint A))
    (c : J × A → X) (hc : Function.Injective c)
    (hqc : ∀ j a, q (c (j, a)) = b' j)
    (hrc : ∀ j a, r (c (j, a)) = ∞ ↔ a = 0)
    (hcover : ∀ x, r x = ∞ → x ∈ Set.range c) :
    ∃ F : X ≃ I × OnePoint A, ∀ x, q x = b (F x).1 ∧ r x = (F x).2 := by
  have hlabels : ∀ x, ∃ i, q x = b i := by
    intro x
    by_cases hx : r x = ∞
    · obtain ⟨⟨j, a⟩, rfl⟩ := hcover x hx
      exact ⟨e.symm j, (hqc j a).trans (by rw [← he, e.apply_symm_apply])⟩
    · exact ⟨(E ⟨x, (hU x).mpr hx⟩).1, hq ⟨x, (hU x).mpr hx⟩⟩
  have hinfty : ∀ i, ∃! x, q x = b i ∧ r x = ∞ := by
    intro i
    refine ⟨c (e i, 0), ⟨(hqc _ _).trans (he i), (hrc _ _).mpr rfl⟩, ?_⟩
    intro x hx
    obtain ⟨⟨j, a⟩, rfl⟩ := hcover x hx.2
    have ha : a = 0 := (hrc j a).mp hx.2
    have hj : j = e i := hb' ((hqc j a).symm.trans (hx.1.trans (he i).symm))
    exact congrArg c (Prod.ext hj ha)
  exact labelled_affine_completion U q r b hb E hU hq hr hlabels hinfty

end AlgebraicGeometry.RamifiedNormalization.StageFour
