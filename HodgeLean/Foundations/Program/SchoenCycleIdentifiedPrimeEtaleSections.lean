import HodgeLean.Foundations.Program.SchoenCycleSpecFormalEtaleCoordinates
import HodgeLean.Foundations.Program.SchoenCycleSpecFormalSmoothNeighbourhood
import HodgeLean.Foundations.Program.SchoenCycleNeighbourhoodCotangentEtaleCoordinates
import HodgeLean.Foundations.Program.SchoenCycleComplexSpecStalk
import HodgeLean.Foundations.Program.SchoenCycleLocalAdicEquivalence
import HodgeLean.Foundations.Program.SchoenCycleLocalCotangentEquiv
import HodgeLean.Foundations.Program.SchoenCycleFormalModelSmoothNeighbourhood

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Exact prime-local coefficient functions have etale section representatives whose stalk comparison retains the canonical values of every affine function, for any identified prime of the actual complex point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8; EGA IV, 17.11.1. -/
theorem s2e_spec_etale_sections_at_identified_prime
    (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S]
    (n : ℕ) (x : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap S)))
    (Q : Ideal S) [Q.IsPrime] (hQ : x.underlying.asIdeal = Q)
    (E : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (Localization.AtPrime Q) ≃ₐ[ℂ]
        AdicCompletion (idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    (c : Fin n → Localization.AtPrime Q)
    (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (b : Module.Basis (Fin n) ℂ
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).Cotangent)
    (hb : ∀ i, b i = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent
      ⟨c i, hc i⟩) :
    let X := Over.mk (ComplexPoint.affineSpecStructureMap S)
    letI : Algebra ℂ (X.left.presheaf.stalk x.underlying) :=
      (HodgeLean.Foundations.Curves.stalkC (X := X) x.underlying).toAlgebra
    ∃ L : X.left.presheaf.stalk x.underlying ≃ₐ[ℂ] Localization.AtPrime Q,
      (∀ s : S, L ((X.left.presheaf.germ ⊤ x.underlying trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)) = algebraMap S (Localization.AtPrime Q) s) ∧
      ∃ (W : X.left.Opens) (_ : IsAffineOpen W) (hxW : x.underlying ∈ W),
        letI := s2e_step1_sectionAlgebra X W
        ∃ G : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, W),
          G.toRingHom.Etale ∧
          ∀ i, L ((X.left.presheaf.germ W x.underlying hxW).hom
            (G (MvPolynomial.X i))) = c i := by
  subst Q
  let X := Over.mk (ComplexPoint.affineSpecStructureMap S)
  letI : IsIntegral X.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of S)))
  letI : Algebra ℂ (X.left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC (X := X) x.underlying).toAlgebra
  obtain ⟨W, hW, hxW, G, het, hG⟩ :=
    s2e_spec_etale_sections_of_formal_coordinates S n x E c hc b hb
  refine ⟨s2e_complex_spec_stalk_equiv S x.underlying, ?_, W, hW, hxW, G, het, hG⟩
  intro s
  change ((Spec (CommRingCat.of S)).presheaf.germ ⊤ x.underlying trivial ≫
    (Spec.stalkIso (CommRingCat.of S) x.underlying).hom).hom
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s) = _
  rw [Spec.germ_stalkMapIso_hom]
  change (((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫
    CommRingCat.ofHom (algebraMap S (Localization.AtPrime x.underlying.asIdeal))).hom s) = _
  rw [Iso.inv_hom_id_assoc]
  rfl

#print axioms s2e_spec_etale_sections_at_identified_prime
end HodgeLean.Foundations.Program
