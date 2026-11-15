import HodgeLean.Foundations.Program.SchoenCycleMixedPolynomialCoordinates
import HodgeLean.Foundations.Program.SchoenCycleRenamedInvariantValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The mixed coordinate induction retains the exact head elementary evaluation and the exact tail coefficient map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_mixed_polynomial_successor_value
    {R : Type*} [CommRing R] (b : ℕ) (m : Fin (b + 1) → ℕ)
    (p : MvPolynomial (Σ a, Fin (m a)) R) :
    let e := s2e_sigma_head_tail (fun a => Fin (m a))
    let T := Σ a : Fin b, Fin (m a.succ)
    let t := Equiv.Perm.sigmaCongrRightHom (fun a : Fin b => Fin (m a.succ))
    let q := map (s2e_mixed_polynomial_invariant_coordinates R b (fun a => m a.succ)).toRingHom
      (sumAlgEquiv R (Fin (m 0)) T (rename e p))
    (s2e_mixed_polynomial_invariant_coordinates R (b + 1) m p).val =
      rename e.symm (s2e_sum_elementary_invariant_equiv (R := R) (σ := Fin (m 0)) t
        (rename (finCongr (Fintype.card_fin (m 0)).symm) q)).val := by
  dsimp only
  let β := fun a : Fin (b + 1) => Fin (m a)
  let e := s2e_sigma_head_tail β
  let T := Σ a : Fin b, Fin (m a.succ)
  let t := Equiv.Perm.sigmaCongrRightHom (fun a : Fin b => Fin (m a.succ))
  let D := s2e_renamed_reindexed_invariant_equiv (R := R) e
    (s2e_block_family_head_tail β).toEquiv
    (fun ρ => Equiv.Perm.sigmaCongrRight ρ)
    (fun v => Equiv.sumCongr v.1 (t v.2)) (s2e_sigma_head_tail_permutation β)
  let q := map (s2e_mixed_polynomial_invariant_coordinates R b (fun a => m a.succ)).toRingHom
    (sumAlgEquiv R (Fin (m 0)) T (rename e p))
  change (D.symm (s2e_sum_elementary_invariant_equiv (R := R) (σ := Fin (m 0)) t
    (rename (finCongr (Fintype.card_fin (m 0)).symm) q))).val = _
  exact s2e_renamed_invariant_symm_apply e (s2e_block_family_head_tail β).toEquiv
    (fun ρ => Equiv.Perm.sigmaCongrRight ρ) (fun v => Equiv.sumCongr v.1 (t v.2))
    (s2e_sigma_head_tail_permutation β) _

end HodgeLean.Foundations.Program
