import HodgeLean.Foundations.Program.SchoenCycleAdicRenamedInvariants
import HodgeLean.Foundations.Program.SchoenCycleMixedPointStabilizerEquiv
import HodgeLean.Foundations.Program.SchoenCycleMixedRootInvariantAlgebra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Mixed coefficient coordinates identify with the actual tuple-stabilizer invariants of formal root coordinates, with the geometric inverse convention.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
def s2e_mixed_formal_stabilizer_coordinates
    (X : Over (Spec ↧ℂ)) (n b : ℕ) (x : ComplexPoint (g3_power X n))
    (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint X) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj X n (ι ⟨a, i⟩)) x = p a) :
    let P := AdicCompletion (idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ)
    let H := s2e_powerPointStabilizer X n x
    let α (σ : H) : P →ₐ[ℂ] P := s2e_adic_algebra_map _ _ (rename σ.val.symm)
      (s2e_rename_preserves_origin_powers σ.val.symm)
    AdicCompletion (idealOfVars (Σ a, Fin (m a)) ℂ) (MvPolynomial (Σ a, Fin (m a)) ℂ) ≃ₐ[ℂ]
      (⨅ σ : H, AlgHom.equalizer (α σ) (AlgHom.id ℂ P) : Subalgebra ℂ P) := by
  dsimp only
  let G := (a : Fin b) → Equiv.Perm (Fin (m a))
  let E := s2e_mixed_point_stabilizer_equiv X n b x m ι p hp hx
  let t : G ≃ s2e_powerPointStabilizer X n x := (Equiv.inv G).trans E.toEquiv
  let C := s2e_adic_renamed_reindexed_invariants (R := ℂ) ι t
    (fun ρ : G => Equiv.Perm.sigmaCongrRight ρ)
    (fun σ : s2e_powerPointStabilizer X n x => σ.val.symm) (by
      intro ρ
      change ι.permCongr (Equiv.Perm.sigmaCongrRight ρ) =
        (ι.permCongr (Equiv.Perm.sigmaCongrRight (ρ⁻¹))).symm
      apply Equiv.ext
      intro i
      rfl)
  exact (s2e_mixed_root_complex_invariant_coordinates b m).trans C

#print axioms s2e_mixed_formal_stabilizer_coordinates
end HodgeLean.Foundations.Program
