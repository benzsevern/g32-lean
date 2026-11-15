import HodgeLean.Foundations.Program.SchoenCycleIdentifiedPrimeEtaleSections

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

/-- An actual prime-local formal model and cotangent basis realize prescribed pullback values by etale sections, retaining the canonical pullback of every original affine function.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8; EGA IV, 17.11.1. -/
theorem s2e_etale_section_pullback_values
    (S R : Type) [CommRing S] [IsDomain S] [CommRing R]
    [Algebra ℂ S] [Algebra ℂ R] [Algebra.FiniteType ℂ S]
    (n : ℕ) (z : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap S)))
    (Q : Ideal S) [Q.IsPrime] (hzQ : z.underlying.asIdeal = Q)
    (f : Localization.AtPrime Q →ₐ[ℂ] R) (q : Fin n → R)
    (h : ∃ (E : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
          (Localization.AtPrime Q) ≃ₐ[ℂ]
          AdicCompletion (idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
        (c : Fin n → Localization.AtPrime Q)
        (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (b : Module.Basis (Fin n) ℂ (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).Cotangent),
        (∀ i, b i = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent ⟨c i, hc i⟩) ∧
        (∀ i, f (c i) = q i)) :
    let XS := Over.mk (ComplexPoint.affineSpecStructureMap S)
    ∃ F : XS.left.presheaf.stalk z.underlying →+* R,
      (∀ s : S, F ((XS.left.presheaf.germ ⊤ z.underlying trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)) = f (algebraMap S (Localization.AtPrime Q) s)) ∧
      ∃ (V : XS.left.Opens) (_ : IsAffineOpen V) (hzV : z.underlying ∈ V),
        letI := s2e_step1_sectionAlgebra XS V
        ∃ G : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(XS.left, V),
          G.toRingHom.Etale ∧
          ∀ i, F ((XS.left.presheaf.germ V z.underlying hzV).hom (G (X i))) = q i := by
  obtain ⟨E, c, hc, b, hb, hval⟩ := h
  obtain ⟨L, hL, V, hV, hzV, G, het, hG⟩ :=
    s2e_spec_etale_sections_at_identified_prime S n z Q hzQ E c hc b hb
  refine ⟨f.toRingHom.comp L.toRingHom, ?_, V, hV, hzV, G, het, ?_⟩
  · intro s
    exact congrArg f (hL s)
  · intro i
    exact (congrArg f (hG i)).trans (hval i)

#print axioms s2e_etale_section_pullback_values
end HodgeLean.Foundations.Program
