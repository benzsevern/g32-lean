import Mathlib.SetTheory.Cardinal.Finite

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- An injective coordinate map exhausts each finite target fibre when the fibre cardinalities agree. -/
theorem fibre_coordinates_bijective_of_card
    {X Y B : Type*} (f : X → Y) (p : X → B) (q : Y → B)
    (hf : Function.Injective f) (hpq : ∀ x, q (f x) = p x)
    [∀ b, Finite {y : Y // q y = b}]
    (hcard : ∀ b, Nat.card {x : X // p x = b} = Nat.card {y : Y // q y = b}) :
    Function.Bijective f := by
  refine ⟨hf, ?_⟩
  intro y
  let b := q y
  let F : {x : X // p x = b} → {z : Y // q z = b} :=
    fun x => ⟨f x.val, (hpq x.val).trans x.property⟩
  have hF : Function.Injective F := by
    intro x x' h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  have hbij : Function.Bijective F :=
    (Nat.bijective_iff_injective_and_card F).mpr ⟨hF, hcard b⟩
  obtain ⟨x, hx⟩ := hbij.surjective ⟨y, rfl⟩
  exact ⟨x.val, congrArg Subtype.val hx⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
