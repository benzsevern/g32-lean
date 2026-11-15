import HodgeLean.Foundations.Program.MilneTensorPiRepresentation
import HodgeLean.Foundations.Program.MilneTensorPiSplit

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} {R M : ι → Type*}
    [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

def m1b_piSplitModuleEquiv (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (p : ι → Prop) [DecidablePred p] :
    ((i : ι) → M i) ≃ₗ[ℂ]
      (((i : {i // p i}) → M i.val) × ((i : {i // ¬p i}) → M i.val)) :=
  { Equiv.piEquivPiSubtypeProd p M with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem m1b_piRepresentation_split_conj
    (ρ : (i : ι) → R i →ₐ[ℂ] Module.End ℂ (M i))
    (p : ι → Prop) [DecidablePred p] (X : (i : ι) → R i) :
    (m1b_piSplitModuleEquiv M p).conj (m1b_piRepresentation ρ X) =
      (m1b_piRepresentation (fun i : {i // p i} => ρ i.val) (fun i => X i.val)).prodMap
        (m1b_piRepresentation (fun i : {i // ¬p i} => ρ i.val) (fun i => X i.val)) := by
  let E := m1b_piSplitModuleEquiv M p
  have hnat (v : (i : ι) → M i) :
      E (m1b_piRepresentation ρ X v) =
        ((m1b_piRepresentation (fun i : {i // p i} => ρ i.val) (fun i => X i.val)).prodMap
          (m1b_piRepresentation (fun i : {i // ¬p i} => ρ i.val) (fun i => X i.val))) (E v) := rfl
  apply LinearMap.ext
  intro w
  simpa only [LinearEquiv.conj_apply_apply, E.apply_symm_apply] using hnat (E.symm w)

end HodgeLean.Foundations.Program
