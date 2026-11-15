import HodgeLean.Foundations.Program.SchoenCycleFormalCoefficientInverse
import HodgeLean.Foundations.Program.SchoenCycleLocalAdicCotangent
import HodgeLean.Foundations.Program.SchoenCycleLocalCotangentEquiv

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- In an actual local algebra with a coefficient formal model, every represented cotangent basis is a formal coordinate system with exactly those actual adic germs.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 2, 7 and 10. -/
theorem s2e_formal_local_coordinates_of_cotangent_basis
    (k R σ : Type*) [Field k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra k R] [Finite σ]
    (E : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[k]
      AdicCompletion (idealOfVars σ k) (MvPolynomial σ k))
    (c : σ → IsLocalRing.maximalIdeal R)
    (b : Module.Basis σ k (IsLocalRing.maximalIdeal R).Cotangent)
    (hb : ∀ i, b i = (IsLocalRing.maximalIdeal R).toCotangent (c i)) :
    ∃ F : AdicCompletion (idealOfVars σ k) (MvPolynomial σ k) ≃ₐ[k]
        AdicCompletion (IsLocalRing.maximalIdeal R) R,
      ∀ i, F (AdicCompletion.of (idealOfVars σ k) (MvPolynomial σ k) (X i)) =
        AdicCompletion.of (IsLocalRing.maximalIdeal R) R (c i).val := by
  let I := idealOfVars σ k
  let D := AdicCompletion I (MvPolynomial σ k)
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  letI : I.IsMaximal := s2e_coefficient_origin_isMaximal k σ
  letI : IsLocalRing D := s2e_maximal_adic_isLocalRing I (idealOfVars_fg σ k)
  let T₁ := s2e_local_adic_cotangent_equiv (k := k) (R := R)
  let T₂ := s2e_local_algebra_cotangent_equiv E
  let B := b.map (T₁.trans T₂)
  choose hA hAc using fun i => s2e_local_adic_cotangent_toCotangent (k := k) (c i)
  choose hD hDc using fun i => s2e_local_algebra_cotangent_toCotangent E
    ⟨AdicCompletion.of (IsLocalRing.maximalIdeal R) R (c i).val, hA i⟩
  have hB (i : σ) : B i = (IsLocalRing.maximalIdeal D).toCotangent
      ⟨E (AdicCompletion.of (IsLocalRing.maximalIdeal R) R (c i).val), hD i⟩ := by
    change T₂ (T₁ (b i)) = _
    rw [hb, hAc]
    exact hDc i
  obtain ⟨H, hH⟩ := s2e_formal_coefficient_inverse k σ
    (fun i => E (AdicCompletion.of (IsLocalRing.maximalIdeal R) R (c i).val)) hD B hB
  refine ⟨H.trans E.symm, ?_⟩
  intro i
  rw [AlgEquiv.trans_apply, hH, AlgEquiv.symm_apply_apply]

#print axioms s2e_formal_local_coordinates_of_cotangent_basis
end HodgeLean.Foundations.Program
