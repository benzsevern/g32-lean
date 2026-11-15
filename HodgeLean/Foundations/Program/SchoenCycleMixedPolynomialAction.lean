import HodgeLean.Foundations.Program.SchoenCycleMixedPolynomialCoordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Independent block permutations act on the actual mixed root polynomial algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
def s2e_mixed_polynomial_action
    (R : Type*) [CommRing R] (b : ℕ) (m : Fin b → ℕ) :
    ((a : Fin b) → Equiv.Perm (Fin (m a))) →*
      (MvPolynomial (Σ a, Fin (m a)) R ≃ₐ[R] MvPolynomial (Σ a, Fin (m a)) R) := by
  refine { toFun := fun ρ => renameEquiv R (Equiv.Perm.sigmaCongrRight ρ)
           map_one' := ?_
           map_mul' := ?_ }
  · apply AlgEquiv.ext
    intro p
    have hσ := (Equiv.Perm.sigmaCongrRightHom (fun a : Fin b => Fin (m a))).map_one
    change rename (Equiv.Perm.sigmaCongrRight (1 : (a : Fin b) → Equiv.Perm (Fin (m a)))) p = p
    change Equiv.Perm.sigmaCongrRight (1 : (a : Fin b) → Equiv.Perm (Fin (m a))) = 1 at hσ
    rw [hσ]
    exact rename_id_apply p
  · intro ρ τ
    apply AlgEquiv.ext
    intro p
    change rename (Equiv.Perm.sigmaCongrRight (ρ * τ)) p =
      rename (Equiv.Perm.sigmaCongrRight ρ) (rename (Equiv.Perm.sigmaCongrRight τ) p)
    rw [rename_rename]
    apply congrArg (fun f : (Σ a, Fin (m a)) → (Σ a, Fin (m a)) => rename f p)
    funext v
    rfl

end HodgeLean.Foundations.Program
