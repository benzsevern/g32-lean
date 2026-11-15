import HodgeLean.Foundations.Program.MilneTensorSymmetricSuccessor
import HodgeLean.Foundations.Program.MilneTensorStandardReindex
import HodgeLean.Foundations.Program.MilneTensorLinePolynomial

noncomputable section
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem m1b_standard_symmetric_orbit_polynomial (d r n : ℕ)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → Fin d → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries (1 : Matrix (Fin d) (Fin d) ℂ).toBilin', ∀ v,
      f (fun t => m1b_copies r u (v t)) = f v) :
    ∃ P : MvPolynomial ((Fin d × Fin d) ⊕ (Fin n × (Fin r × Fin d))) ℂ,
      ∀ (e : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)) (v : Fin n → Fin r → Fin d → ℂ),
        MvPolynomial.eval (Sum.elim
          (fun ij => m1b_formTransport (1 : Matrix (Fin d) (Fin d) ℂ).toBilin' e
            (Pi.single ij.1 1) (Pi.single ij.2 1))
          (fun tc => v tc.1 tc.2.1 tc.2.2)) P = f (fun t c => e.symm (v t c)) := by
  induction d generalizing n with
  | zero => exact m1b_zero_form_polynomial _ f
  | succ d ih =>
    cases d with
    | zero =>
      letI : Unique (Fin 1) := { default := 0, uniq := fun x => Subsingleton.elim _ _ }
      obtain ⟨P, hP⟩ := m1b_orthogonal_line_orbit_polynomial f hf
      exact ⟨P, m1b_matrix_polynomial_linearEquiv _ f P (fun M _ v => hP M v)⟩
    | succ d =>
      let e : Fin (d + 1 + 1) ≃ Unit ⊕ Fin (d + 1) :=
        Fintype.equivOfCardEq (by simp [Nat.add_comm])
      apply m1b_standard_polynomial_extension_reindex e _ f hf
      intro g hg
      exact m1b_standard_symmetric_successor (Nat.succ_pos d) g hg
        (fun m a ha => ih m a ha)

end HodgeLean.Foundations.Program
