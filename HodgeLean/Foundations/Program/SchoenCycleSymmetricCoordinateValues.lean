import HodgeLean.Foundations.Program.SchoenCycleSymmetricCoefficientInvariants

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The invariant symmetric coordinate equivalence evaluates the same elementary polynomial over the invariant coefficient ring.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_symmetric_coefficient_invariant_value
    {k S G σ : Type*} [CommRing k] [CommRing S] [Algebra k S] [Fintype σ]
    (α : G → S →ₐ[k] S)
    (q : MvPolynomial (Fin (Fintype.card σ))
      (⨅ g, AlgHom.equalizer (α g) (AlgHom.id k S) : Subalgebra k S)) :
    let F : Subalgebra k S := ⨅ g, AlgHom.equalizer (α g) (AlgHom.id k S)
    (s2e_symmetric_coefficient_invariant_equiv (σ := σ) α q).val =
      map F.val.toRingHom (aeval (fun j : Fin (Fintype.card σ) => esymm σ F (j.val + 1)) q) := by
  dsimp only
  let F : Subalgebra k S := ⨅ g, AlgHom.equalizer (α g) (AlgHom.id k S)
  change map F.val.toRingHom ((esymmAlgHom σ F (Fintype.card σ) q).val) = _
  rw [esymmAlgHom_apply]

end HodgeLean.Foundations.Program
