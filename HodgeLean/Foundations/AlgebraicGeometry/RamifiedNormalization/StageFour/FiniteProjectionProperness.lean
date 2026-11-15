import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.FiniteSphereCoordinate
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RestrictedProperProjection
import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A proper surjective sphere projection retains properness, surjectivity and its literal coordinate after removing infinity. -/
theorem proper_finite_sphere_projection
    {X : Type*} [TopologicalSpace X] (P : X → OnePoint ℂ)
    (hP : IsProperMap P) (hPs : Function.Surjective P) :
    ∃ p : {x : X // P x ≠ ∞} → ℂ, IsProperMap p ∧ Function.Surjective p ∧
      ∀ x, (p x : OnePoint ℂ) = P x.val := by
  let H := onePointFiniteHomeomorph (A := ℂ)
  let S : Set (OnePoint ℂ) := {z | z ≠ ∞}
  let p : {x : X // P x ≠ ∞} → ℂ := fun x => H ⟨P x.val, x.property⟩
  have hp : IsProperMap p := H.isProperMap.comp (proper_projection_restrict_preimage P hP S)
  have hcoord (x : {x : X // P x ≠ ∞}) : (p x : OnePoint ℂ) = P x.val :=
    congrArg Subtype.val (H.symm_apply_apply ⟨P x.val, x.property⟩)
  refine ⟨p, hp, ?_, hcoord⟩
  intro z
  obtain ⟨x, hx⟩ := hPs (z : OnePoint ℂ)
  have hxf : P x ≠ ∞ := by rw [hx]; exact OnePoint.coe_ne_infty z
  refine ⟨⟨x, hxf⟩, OnePoint.coe_injective ?_⟩
  exact (hcoord ⟨x, hxf⟩).trans hx

end AlgebraicGeometry.RamifiedNormalization.StageFour
