import HodgeLean.Foundations.Program.SchoenCycleLocalAdicCotangent
import HodgeLean.Foundations.Program.SchoenCycleLocalCotangentEquiv
import HodgeLean.Foundations.Program.SchoenCycleAdicMapValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A formal comparison retaining prescribed actual function values transports their represented actual cotangent basis.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_formal_comparison_actual_cotangent_basis
    {k R S σ : Type*} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (d : σ → S)
    (E : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[k]
      AdicCompletion (IsLocalRing.maximalIdeal S) S)
    (c : σ → R) (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal R)
    (hfc : ∀ i, d i ∈ IsLocalRing.maximalIdeal S)
    (hE : ∀ i, E (AdicCompletion.of (IsLocalRing.maximalIdeal R) R (c i)) =
      AdicCompletion.of (IsLocalRing.maximalIdeal S) S (d i))
    (B : Module.Basis σ k (IsLocalRing.maximalIdeal R).Cotangent)
    (hB : ∀ i, B i = (IsLocalRing.maximalIdeal R).toCotangent ⟨c i, hc i⟩) :
    ∃ D : Module.Basis σ k (IsLocalRing.maximalIdeal S).Cotangent,
      ∀ i, D i = (IsLocalRing.maximalIdeal S).toCotangent ⟨d i, hfc i⟩ := by
  let ER := s2e_local_adic_cotangent_equiv (k := k) (R := R)
  let ES := s2e_local_adic_cotangent_equiv (k := k) (R := S)
  let F := s2e_local_algebra_cotangent_equiv E
  refine ⟨((B.map ER).map F).map ES.symm, ?_⟩
  intro i
  apply ES.injective
  rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    Module.Basis.map_apply, Module.Basis.map_apply, hB]
  obtain ⟨hc', hER⟩ := s2e_local_adic_cotangent_toCotangent (k := k) ⟨c i, hc i⟩
  rw [hER]
  obtain ⟨hx, hF⟩ := s2e_local_algebra_cotangent_toCotangent E
    ⟨AdicCompletion.of (IsLocalRing.maximalIdeal R) R (c i), hc'⟩
  rw [hF]
  obtain ⟨hfc', hES⟩ := s2e_local_adic_cotangent_toCotangent (k := k) ⟨d i, hfc i⟩
  rw [hES]
  apply congrArg (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal S) S)).toCotangent
  apply Subtype.ext
  exact hE i

#print axioms s2e_formal_comparison_actual_cotangent_basis
end HodgeLean.Foundations.Program
