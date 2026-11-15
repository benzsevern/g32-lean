import HodgeLean.Foundations.Program.RigidStartingSystemDefs

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

def b65r_homAction {n : ℕ} (S T : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    Module.End ℂ (Matrix (Fin n) (Fin n) ℂ) where
  toFun X := S.val * X * (T⁻¹).val
  map_add' X Y := by simp only [mul_add, add_mul]
  map_smul' c X := by simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc]

def b65r_homActionHom (n : ℕ) :
    ((Matrix (Fin n) (Fin n) ℂ)ˣ × (Matrix (Fin n) (Fin n) ℂ)ˣ) →*
      Module.End ℂ (Matrix (Fin n) (Fin n) ℂ) where
  toFun p := b65r_homAction p.1 p.2
  map_one' := by ext X; simp [b65r_homAction]
  map_mul' p q := by
    ext X
    simp [b65r_homAction, Module.End.mul_apply, mul_assoc]

theorem b65r_homAction_prod {n r : ℕ}
    (T S : Fin r → (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hT : (List.ofFn T).prod = 1) (hS : (List.ofFn S).prod = 1) :
    (List.ofFn (fun i ↦ b65r_homAction (S i) (T i))).prod = 1 := by
  let xs := List.ofFn (fun i ↦ (S i, T i))
  have hp : xs.prod = (1,1) := by
    apply Prod.ext
    · have he := (MonoidHom.fst _ _).map_list_prod xs
      simpa [xs, List.map_ofFn, Function.comp_def, hS] using he
    · have he := (MonoidHom.snd _ _).map_list_prod xs
      simpa [xs, List.map_ofFn, Function.comp_def, hT] using he
  have he := (b65r_homActionHom n).map_list_prod xs
  rw [hp] at he
  change (b65r_homActionHom n) 1 = _ at he
  rw [map_one] at he
  simpa [xs, List.map_ofFn, Function.comp_def, b65r_homActionHom] using he.symm

end HodgeLean.Foundations.Program
