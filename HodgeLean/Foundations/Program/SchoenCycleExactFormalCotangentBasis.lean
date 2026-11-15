import HodgeLean.Foundations.Program.SchoenCycleFormalCoefficientCotangent
import HodgeLean.Foundations.Program.SchoenCycleLocalCotangentEquiv
import HodgeLean.Foundations.Program.SchoenCycleLocalAdicCotangent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Actual functions with the exact formal coefficient-variable values represent a basis of the actual local cotangent module.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_exact_formal_coordinate_cotangent_basis
    {k R σ : Type*} [Field k] [CommRing R] [Algebra k R]
    [IsLocalRing R] [IsNoetherianRing R] [Fintype σ]
    (D : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[k]
      AdicCompletion (idealOfVars σ k) (MvPolynomial σ k))
    (c : σ → R) (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal R)
    (hD : ∀ i, D (AdicCompletion.of (IsLocalRing.maximalIdeal R) R (c i)) =
      AdicCompletion.of (idealOfVars σ k) (MvPolynomial σ k) (X i)) :
    ∃ B : Module.Basis σ k (IsLocalRing.maximalIdeal R).Cotangent,
      ∀ i, B i = (IsLocalRing.maximalIdeal R).toCotangent ⟨c i, hc i⟩ := by
  let I := idealOfVars σ k
  let A := AdicCompletion I (MvPolynomial σ k)
  letI : I.IsMaximal := s2e_coefficient_origin_isMaximal k σ
  letI : IsLocalRing A := s2e_maximal_adic_isLocalRing I (idealOfVars_fg σ k)
  obtain ⟨B0, hB0⟩ := s2e_formal_coefficient_cotangent_basis k σ
  let E := s2e_local_adic_cotangent_equiv (k := k) (R := R)
  let F := s2e_local_algebra_cotangent_equiv D.symm
  refine ⟨(B0.map F).map E.symm, ?_⟩
  intro i
  apply E.injective
  rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Module.Basis.map_apply]
  obtain ⟨hi, hBi⟩ := hB0 i
  rw [hBi]
  obtain ⟨hz, hF⟩ := s2e_local_algebra_cotangent_toCotangent D.symm
    ⟨AdicCompletion.of I (MvPolynomial σ k) (X i), hi⟩
  rw [hF]
  obtain ⟨hc', hE⟩ := s2e_local_adic_cotangent_toCotangent (k := k) ⟨c i, hc i⟩
  rw [hE]
  apply congrArg (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R)).toCotangent
  apply Subtype.ext
  exact (D.symm_apply_eq).mpr (hD i).symm

#print axioms s2e_exact_formal_coordinate_cotangent_basis
end HodgeLean.Foundations.Program
