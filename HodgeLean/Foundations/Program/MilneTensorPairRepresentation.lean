import HodgeLean.Foundations.Program.MilneTensorExchangeAction
import HodgeLean.Foundations.Program.MilneTensorMatrix
import Mathlib.Algebra.Ring.Fin

noncomputable section
namespace HodgeLean.Foundations.Program

def m1b_matrixPairPi (d : ℕ) :
    (Fin 2 → Matrix (Fin d) (Fin d) ℂ) ≃ₐ[ℂ]
      (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.piFinTwo (fun _ => Matrix (Fin d) (Fin d) ℂ))
    (fun _ => rfl)

theorem m1b_matrix_pair_coordinates {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (d : ℕ) (hd : 0 < d)
    (ρ : (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ) →ₐ[ℂ] Module.End ℂ V) :
    ∃ (a b : ℕ) (E : V ≃ₗ[ℂ] ((Fin a → Fin d → ℂ) × (Fin b → Fin d → ℂ))),
      ∀ X v, E (ρ X v) = m1b_exchangeMultiplicityAction d a b X (E v) := by
  let D : Fin 2 → ℕ := fun _ => d
  let ρ' := ρ.comp (m1b_matrixPairPi d).toAlgHom
  let z : (i : Fin 2) → Fin (D i) := fun _ => ⟨0, hd⟩
  let m : Fin 2 → ℕ := fun i => Module.finrank ℂ (m1b_matrixMultiplicity D ρ' z i)
  let E := (m1b_matrixScalarCoordinates D ρ' z).trans
    (LinearEquiv.piFinTwo ℂ (fun i => Fin (m i) → Fin d → ℂ))
  refine ⟨m 0, m 1, E, ?_⟩
  intro X v
  have hρ : ρ' ((m1b_matrixPairPi d).symm X) = ρ X := by
    change ρ (m1b_matrixPairPi d ((m1b_matrixPairPi d).symm X)) = ρ X
    rw [AlgEquiv.apply_symm_apply]
  apply Prod.ext
  · funext j
    have h := m1b_matrixScalarCoordinates_action D ρ' z ((m1b_matrixPairPi d).symm X) v 0 j
    rw [hρ] at h
    exact h
  · funext j
    have h := m1b_matrixScalarCoordinates_action D ρ' z ((m1b_matrixPairPi d).symm X) v 1 j
    rw [hρ] at h
    exact h

end HodgeLean.Foundations.Program
