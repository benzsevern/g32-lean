import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Exhaustive labelled affine evaluations determine the action on every finite point of the actual global component parametrizations. -/
theorem classified_affine_deck
    {X TA I : Type*} [Add I] [One I]
    (U : Set X) (H : TA ≃ U) (E : TA ≃ I × ℂ)
    (G : X ≃ I × OnePoint ℂ) (j : I → OnePoint ℂ → X)
    (hG : ∀ a, G (H a).val = ((E a).1, ((E a).2 : OnePoint ℂ)))
    (hj : ∀ i z, G (j i z) = (i, z))
    (D : X → X) (d : TA → TA) (c : ℂ)
    (hD : ∀ a, (H (d a)).val = D (H a).val)
    (hd : ∀ a, E (d a) = ((E a).1 + 1, c * (E a).2)) :
    ∀ i (z : ℂ), D (j i (z : OnePoint ℂ)) = j (i + 1) ((c * z : ℂ) : OnePoint ℂ) := by
  intro i z
  let a := E.symm (i, z)
  have ha : E a = (i, z) := E.apply_symm_apply _
  have hja : j i (z : OnePoint ℂ) = (H a).val := by
    apply G.injective
    rw [hj, hG, ha]
  rw [hja, ← hD]
  apply G.injective
  rw [hG, hd, ha, hj]

end AlgebraicGeometry.RamifiedNormalization.StageFour
