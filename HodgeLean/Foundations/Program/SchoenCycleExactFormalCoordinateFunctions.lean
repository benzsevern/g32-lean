import HodgeLean.Foundations.Program.SchoenCycleExactFormalCotangentBasis

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Exact formal coefficient-variable values force actual vanishing at the local origin and an actual represented cotangent basis.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_exact_formal_coordinate_functions
    {k R σ : Type*} [Field k] [CommRing R] [Algebra k R]
    [IsLocalRing R] [IsNoetherianRing R] [Fintype σ]
    (D : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[k]
      AdicCompletion (idealOfVars σ k) (MvPolynomial σ k))
    (c : σ → R)
    (hD : ∀ i, D (AdicCompletion.of (IsLocalRing.maximalIdeal R) R (c i)) =
      AdicCompletion.of (idealOfVars σ k) (MvPolynomial σ k) (X i)) :
    ∃ (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal R)
      (B : Module.Basis σ k (IsLocalRing.maximalIdeal R).Cotangent),
      ∀ i, B i = (IsLocalRing.maximalIdeal R).toCotangent ⟨c i, hc i⟩ := by
  let I := idealOfVars σ k
  let A := AdicCompletion I (MvPolynomial σ k)
  let T := AdicCompletion (IsLocalRing.maximalIdeal R) R
  letI : I.IsMaximal := s2e_coefficient_origin_isMaximal k σ
  letI : IsLocalRing A := s2e_maximal_adic_isLocalRing I (idealOfVars_fg σ k)
  letI : IsLocalHom D.toRingHom := IsLocalHom.of_surjective D.toRingHom D.surjective
  obtain ⟨B0, hB0⟩ := s2e_formal_coefficient_cotangent_basis k σ
  have hc (i : σ) : c i ∈ IsLocalRing.maximalIdeal R := by
    have hx : D (AdicCompletion.of (IsLocalRing.maximalIdeal R) R (c i)) ∈
        IsLocalRing.maximalIdeal A := by
      rw [hD]
      exact (hB0 i).choose
    change AdicCompletion.of (IsLocalRing.maximalIdeal R) R (c i) ∈
      (IsLocalRing.maximalIdeal A).comap D.toRingHom at hx
    rw [IsLocalRing.maximalIdeal_comap] at hx
    change c i ∈ (IsLocalRing.maximalIdeal T).comap (algebraMap R T) at hx
    rwa [IsLocalRing.maximalIdeal_comap] at hx
  obtain ⟨B, hB⟩ := s2e_exact_formal_coordinate_cotangent_basis D c hc hD
  exact ⟨hc, B, hB⟩

#print axioms s2e_exact_formal_coordinate_functions
end HodgeLean.Foundations.Program
