import HodgeLean.Foundations.Program.MilneTensorAlternatingSuccessor
import HodgeLean.Foundations.Program.MilneTensorSymplecticCoordinates
import HodgeLean.Foundations.Program.MilneTensorPolynomialReindex

noncomputable section
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem m1b_standard_symplectic_orbit_polynomial (k r n : ℕ)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → Fin k ⊕ Fin k → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries (m1b_J k).toBilin', ∀ v,
      f (fun t => m1b_copies r u (v t)) = f v) :
    ∃ P : MvPolynomial (((Fin k ⊕ Fin k) × (Fin k ⊕ Fin k)) ⊕
      (Fin n × (Fin r × (Fin k ⊕ Fin k)))) ℂ,
      ∀ (e : (Fin k ⊕ Fin k → ℂ) ≃ₗ[ℂ] (Fin k ⊕ Fin k → ℂ))
        (v : Fin n → Fin r → Fin k ⊕ Fin k → ℂ),
          MvPolynomial.eval (Sum.elim
            (fun ij => m1b_formTransport (m1b_J k).toBilin' e
              (Pi.single ij.1 1) (Pi.single ij.2 1))
            (fun tc => v tc.1 tc.2.1 tc.2.2)) P = f (fun t c => e.symm (v t c)) := by
  induction k generalizing n with
  | zero =>
    refine ⟨MvPolynomial.C (f 0), ?_⟩
    intro e v
    rw [MvPolynomial.eval_C]
    exact congrArg f (Subsingleton.elim _ _)
  | succ k ih =>
    cases k with
    | zero => exact m1b_symplectic_plane_polynomial f hf
    | succ j =>
      let k := j + 1
      let e : Fin (k + k) ≃ Fin k ⊕ Fin k := finSumFinEquiv.symm
      let B := m1b_symplecticComplementForm k e
      have hB : B.Nondegenerate := m1b_nondegenerate_transport
        (LinearEquiv.funCongrLeft ℂ ℂ e) (m1b_J k).toBilin'
        (m1b_standard_symplectic_nondegenerate k)
      have haB (x) : B x x = 0 := m1b_standard_symplectic_alternating k
        ((LinearEquiv.funCongrLeft ℂ ℂ e).symm x)
      let Br := (m1b_prodBilin m1b_pairForm B).compl₁₂
        (m1b_pairCoordinates (k + k)).toLinearMap (m1b_pairCoordinates (k + k)).toLinearMap
      let eb := m1b_symplecticSplitReindex k e
      have hform : Br.compl₁₂ (LinearEquiv.funCongrLeft ℂ ℂ eb).symm.toLinearMap
          (LinearEquiv.funCongrLeft ℂ ℂ eb).symm.toLinearMap = (m1b_J (k + 1)).toBilin' :=
        m1b_symplectic_split_reindexed_form k e
      have h := m1b_polynomial_extension_reindex eb Br (by
        intro g hg
        apply m1b_alternating_pair_successor (show 0 < k + k by dsimp [k]; omega) B hB haB g hg
        intro m a ha
        exact m1b_polynomial_extension_reindex e (m1b_J k).toBilin'
          (fun b hb => ih m b hb) a ha) f (by rw [hform]; exact hf)
      simpa only [hform] using h

end HodgeLean.Foundations.Program
