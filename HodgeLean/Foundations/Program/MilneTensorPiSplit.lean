import HodgeLean.Foundations.Program.MilneTensorNormOneTransport

noncomputable section
namespace HodgeLean.Foundations.Program

variable {ι : Type*} (A : ι → Type*) [∀ i, Ring (A i)] [∀ i, Algebra ℂ (A i)]

def m1b_piSplitAlgEquiv (p : ι → Prop) [DecidablePred p] :
    ((i : ι) → A i) ≃ₐ[ℂ]
      (((i : {i // p i}) → A i.val) × ((i : {i // ¬p i}) → A i.val)) :=
  { Equiv.piEquivPiSubtypeProd p A with
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl
    commutes' := fun _ => rfl }

def m1b_piId (p : ι → Prop) [DecidablePred p] : (i : ι) → A i :=
  fun i => if p i then 1 else 0

theorem m1b_piSplit_left_id (p : ι → Prop) [DecidablePred p] :
    m1b_piSplitAlgEquiv A p (m1b_piId A p) = (1, 0) := by
  apply Prod.ext
  · funext i
    change (if p i.val then (1 : A i.val) else 0) = 1
    rw [if_pos i.property]
  · funext i
    change (if p i.val then (1 : A i.val) else 0) = 0
    rw [if_neg i.property]

end HodgeLean.Foundations.Program
