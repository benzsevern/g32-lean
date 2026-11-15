import HodgeLean.Foundations.Program.SchoenCycleSumElementaryInvariants
import HodgeLean.Foundations.Program.SchoenCycleSymmetricCoordinateValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The block coordinate comparison rejoins the original variables after the actual symmetric coefficient evaluation.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_sum_elementary_invariant_value
    {R σ τ G : Type*} [CommRing R] [Group G] [Fintype σ]
    (t : G →* Equiv.Perm τ)
    (q : MvPolynomial (Fin (Fintype.card σ))
      (⨅ g, AlgHom.equalizer (rename (t g)) (AlgHom.id R (MvPolynomial τ R)) :
        Subalgebra R (MvPolynomial τ R))) :
    (s2e_sum_elementary_invariant_equiv (σ := σ) t q).val =
      (sumAlgEquiv R σ τ).symm
        (s2e_symmetric_coefficient_invariant_equiv (σ := σ) (fun g => rename (t g)) q).val := rfl

end HodgeLean.Foundations.Program
