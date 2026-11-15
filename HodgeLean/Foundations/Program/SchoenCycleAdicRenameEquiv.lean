import HodgeLean.Foundations.Program.SchoenCycleRenameOriginIdeal
import HodgeLean.Foundations.Program.SchoenCycleAdicMapBijective

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Bijective root reindexing induces the actual origin-adic algebra map in both coordinate systems.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
def s2e_adic_rename_equiv {R σ τ : Type*} [CommRing R] (e : σ ≃ τ) :
    AdicCompletion (idealOfVars σ R) (MvPolynomial σ R) ≃ₐ[R]
      AdicCompletion (idealOfVars τ R) (MvPolynomial τ R) := by
  apply AlgEquiv.ofBijective (s2e_adic_algebra_map _ _ (rename e)
    (s2e_rename_preserves_origin_powers e))
  apply s2e_adic_algebra_map_bijective
  intro n
  have h : (idealOfVars σ R ^ n).map (renameEquiv R e).toRingHom =
      idealOfVars τ R ^ n := by
    rw [Ideal.map_pow]
    exact congrArg (fun I : Ideal (MvPolynomial τ R) => I ^ n) (s2e_rename_origin_ideal e)
  refine ⟨Ideal.quotientEquivAlg _ _ (renameEquiv R e) h.symm, ?_⟩
  intro p
  rfl

#print axioms s2e_adic_rename_equiv
end HodgeLean.Foundations.Program
