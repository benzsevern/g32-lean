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

/-- A prime-local formal coefficient model realizes the prescribed cotangent functions as exact germs of etale coordinates on the actual affine scheme.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.6.1 and 17.11.1; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_spec_etale_sections_of_formal_coordinates
    (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S]
    (n : ℕ) (x : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap S)))
    (E : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime x.underlying.asIdeal))
        (Localization.AtPrime x.underlying.asIdeal) ≃ₐ[ℂ]
        AdicCompletion (idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    (c : Fin n → Localization.AtPrime x.underlying.asIdeal)
    (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal (Localization.AtPrime x.underlying.asIdeal))
    (b : Module.Basis (Fin n) ℂ
      (IsLocalRing.maximalIdeal (Localization.AtPrime x.underlying.asIdeal)).Cotangent)
    (hb : ∀ i, b i = (IsLocalRing.maximalIdeal (Localization.AtPrime x.underlying.asIdeal)).toCotangent
      ⟨c i, hc i⟩) :
    let X := Over.mk (ComplexPoint.affineSpecStructureMap S)
    ∃ (W : X.left.Opens) (_ : IsAffineOpen W) (hxW : x.underlying ∈ W),
      letI := s2e_step1_sectionAlgebra X W
      ∃ G : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, W),
        G.toRingHom.Etale ∧
        ∀ i, (Spec.stalkIso (CommRingCat.of S) x.underlying).hom
          ((X.left.presheaf.germ W x.underlying hxW).hom (G (MvPolynomial.X i))) = c i := by
  let X := Over.mk (ComplexPoint.affineSpecStructureMap S)
  letI : IsIntegral X.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of S)))
  let A := X.left.presheaf.stalk x.underlying
  letI : Algebra ℂ A := (HodgeLean.Foundations.Curves.stalkC (X := X) x.underlying).toAlgebra
  let L := s2e_complex_spec_stalk_equiv S x.underlying
  have hcA (i : Fin n) : L.symm (c i) ∈ IsLocalRing.maximalIdeal A :=
    (s2e_local_algebra_cotangent_toCotangent L.symm ⟨c i, hc i⟩).choose
  let bA := b.map (s2e_local_algebra_cotangent_equiv L.symm)
  have hbA (i : Fin n) : bA i = (IsLocalRing.maximalIdeal A).toCotangent
      ⟨L.symm (c i), hcA i⟩ := by
    rw [Module.Basis.map_apply, hb]
    exact (s2e_local_algebra_cotangent_toCotangent L.symm ⟨c i, hc i⟩).choose_spec
  obtain ⟨U, hU, hxU, hsm⟩ :=
    s2e_spec_standardSmooth_neighbourhood_of_formal_coordinates S n x E c hc b hb
  obtain ⟨W, hW, hxW, G, het, hG⟩ := s2e_etale_sections_of_standardSmooth_cotangent_basis
    X n x U hU hxU hsm (fun i => L.symm (c i)) hcA bA hbA
  refine ⟨W, hW, hxW, G, het, ?_⟩
  intro i
  change L ((X.left.presheaf.germ W x.underlying hxW).hom (G (MvPolynomial.X i))) = c i
  rw [hG, L.apply_symm_apply]

#print axioms s2e_spec_etale_sections_of_formal_coordinates
end HodgeLean.Foundations.Program
