import HodgeLean.Foundations.Program.SchoenCycleFormalCotangentRepresentatives
import HodgeLean.Foundations.Program.SchoenCycleFormalCoefficientCotangent
import HodgeLean.Foundations.Program.SchoenCycleLocalCotangentEquiv

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Formal coefficient coordinates have actual local-ring representatives of every order at least two, and the same representatives give a cotangent basis.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_formal_coordinate_representatives
    {k R σ : Type*} [Field k] [CommRing R] [Algebra k R]
    [IsLocalRing R] [IsNoetherianRing R] [Fintype σ]
    (D : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[k]
      AdicCompletion (idealOfVars σ k) (MvPolynomial σ k))
    (K : ℕ) (hK : 2 ≤ K) :
    ∃ (r : σ → R) (hr : ∀ i, r i ∈ IsLocalRing.maximalIdeal R)
      (B : Module.Basis σ k (IsLocalRing.maximalIdeal R).Cotangent),
      (∀ i, B i = (IsLocalRing.maximalIdeal R).toCotangent ⟨r i, hr i⟩) ∧
      ∀ i, AdicCompletion.of (IsLocalRing.maximalIdeal R) R (r i) -
        D.symm (AdicCompletion.of (idealOfVars σ k) (MvPolynomial σ k) (X i)) ∈
          IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ K := by
  let I := idealOfVars σ k
  let A := AdicCompletion I (MvPolynomial σ k)
  letI : I.IsMaximal := s2e_coefficient_origin_isMaximal k σ
  letI : IsLocalRing A := s2e_maximal_adic_isLocalRing I (idealOfVars_fg σ k)
  obtain ⟨B0, hB0⟩ := s2e_formal_coefficient_cotangent_basis k σ
  choose hi hBi using hB0
  choose hz hmap using fun i => s2e_local_algebra_cotangent_toCotangent D.symm
    ⟨AdicCompletion.of I (MvPolynomial σ k) (X i), hi i⟩
  let B := B0.map (s2e_local_algebra_cotangent_equiv D.symm)
  have hB (i : σ) : B i =
      (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R)).toCotangent
        ⟨D.symm (AdicCompletion.of I (MvPolynomial σ k) (X i)), hz i⟩ := by
    rw [Module.Basis.map_apply, hBi]
    exact hmap i
  exact s2e_formal_cotangent_basis_representatives K hK B
    (fun i => D.symm (AdicCompletion.of I (MvPolynomial σ k) (X i))) hz hB

#print axioms s2e_formal_coordinate_representatives
end HodgeLean.Foundations.Program
