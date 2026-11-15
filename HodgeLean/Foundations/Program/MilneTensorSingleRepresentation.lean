import HodgeLean.Foundations.Program.MilneTensorMatrix

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_matrix_single_coordinates {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (d : ℕ) (hd : 0 < d)
    (ρ : Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ V) :
    ∃ (a : ℕ) (E : V ≃ₗ[ℂ] (Fin a → Fin d → ℂ)),
      ∀ X v j, E (ρ X v) j = X.mulVec (E v j) := by
  let D : Fin 1 → ℕ := fun _ => d
  let ρ' := ρ.comp (Pi.evalAlgHom ℂ (fun _ : Fin 1 => Matrix (Fin d) (Fin d) ℂ) 0)
  let z : (i : Fin 1) → Fin (D i) := fun _ => ⟨0, hd⟩
  let m : Fin 1 → ℕ := fun i => Module.finrank ℂ (m1b_matrixMultiplicity D ρ' z i)
  let F : ((i : Fin 1) → Fin (m i) → Fin d → ℂ) ≃ₗ[ℂ] (Fin (m 0) → Fin d → ℂ) :=
    { Equiv.piUnique (fun i : Fin 1 => Fin (m i) → Fin d → ℂ) with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨m 0, (m1b_matrixScalarCoordinates D ρ' z).trans F, ?_⟩
  intro X v j
  exact m1b_matrixScalarCoordinates_action D ρ' z (fun _ => X) v 0 j

end HodgeLean.Foundations.Program
