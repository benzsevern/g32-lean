import HodgeLean.Foundations.Program.SchoenCycleBasicPolynomialGerms
import HodgeLean.Foundations.Program.SchoenCycleBasicStandardSmooth
import HodgeLean.Foundations.Program.SchoenCycleAugmentedLocalizedCotangentEtale
import HodgeLean.Foundations.Program.SchoenCycleActualLocalizationEtale
import HodgeLean.Foundations.Program.SchoenCycleComplexPointAugmentation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Any prescribed representatives of a cotangent basis at a complex point of a smooth scheme are the exact germs of actual étale algebraic coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.11.1; Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_localEtaleCoordinates_of_cotangent_basis
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] (x : ComplexPoint X) :
    let A := X.left.presheaf.stalk x.underlying
    letI : Algebra ℂ A := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∀ (c : Fin n → A) (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal A)
      (b : Module.Basis (Fin n) ℂ (IsLocalRing.maximalIdeal A).Cotangent),
      (∀ i, b i = (IsLocalRing.maximalIdeal A).toCotangent ⟨c i, hc i⟩) →
      ∃ D : LocalEtaleCoordinates X n x.underlying,
        ∀ i, (X.left.presheaf.germ D.neighborhood x.underlying D.mem).hom
          (D.coordinateAlgHom (MvPolynomial.X i)) = c i := by
  dsimp only
  let A := X.left.presheaf.stalk x.underlying
  letI : Algebra ℂ A := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  intro c hc b hb
  obtain ⟨U, hU, hxU, hsm⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension (d := n) X.hom x.underlying
  letI := s2e_step1_sectionAlgebra X U
  letI : Algebra.IsStandardSmoothOfRelativeDimension n ℂ Γ(X.left, U) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mp
      (algebraMap_isStandardSmoothOfRelativeDimension X hsm)
  obtain ⟨f, hxf, F, hF⟩ := s2e_basic_polynomial_germ_representatives X x.underlying U hU hxU c
  let V := X.left.basicOpen f
  have hV : IsAffineOpen V := hU.basicOpen f
  letI : Nonempty V := ⟨⟨x.underlying, hxf⟩⟩
  let S := Γ(X.left, V)
  letI : Algebra ℂ S := s2e_step1_sectionAlgebra X V
  letI : Algebra.IsStandardSmoothOfRelativeDimension (Nat.card (Fin n)) ℂ S := by
    simpa only [Nat.card_fin] using s2e_basicOpen_standardSmooth_dimension X U hU n f
  letI : Algebra S A := TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨x.underlying, hxf⟩
  letI : IsScalarTower ℂ S A := IsScalarTower.of_algebraMap_eq (fun z =>
    ((s2e_complex_section_germ X V x.underlying hxf).commutes z).symm)
  let P : Ideal S := (hV.primeIdealOf ⟨x.underlying, hxf⟩).asIdeal
  letI : IsLocalization.AtPrime A P := hV.isLocalization_stalk ⟨x.underlying, hxf⟩
  have hv (i : Fin n) : algebraMap S A (F (MvPolynomial.X i)) = c i := by
    have hh := DFunLike.congr_fun hF (MvPolynomial.X i)
    simp only [AlgHom.comp_apply, aeval_X] at hh
    exact hh
  obtain ⟨g, hg, het⟩ := s2e_etale_neighbourhood_of_augmented_localized_cotangent_basis
    ℂ S (Fin n) P A (s2e_complex_point_augmentation X x) (fun i => F (MvPolynomial.X i))
    (fun i => (hv i).symm ▸ hc i) b (by intro i; simpa only [hv] using hb i)
  have hxg : x.underlying ∈ X.left.basicOpen g := by
    rw [Scheme.mem_basicOpen X.left g x.underlying hxf]
    have hu : IsUnit (algebraMap S A g) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff A P g).mpr hg
    exact hu
  let W := X.left.basicOpen g
  letI := s2e_step1_sectionAlgebra X W
  let res := s2e_complex_section_restriction X V W (X.left.basicOpen_le g)
  letI : IsScalarTower ℂ S Γ(X.left, W) :=
    IsScalarTower.of_algebraMap_eq (fun z => (res.commutes z).symm)
  letI : IsLocalization.Away g Γ(X.left, W) := hV.isLocalization_basicOpen g
  have het' : (aeval (R := ℂ) (fun i => algebraMap S Γ(X.left, W) (F (MvPolynomial.X i)))).toRingHom.Etale :=
    s2e_actual_localization_coordinate_etale ℂ S Γ(X.left, W) (Fin n) g _ het
  let G := res.comp F
  have hG : G = aeval (R := ℂ) (fun i => algebraMap S Γ(X.left, W) (F (MvPolynomial.X i))) := by
    ext i
    simp only [G, AlgHom.comp_apply, aeval_X]
    rfl
  refine ⟨{
    neighborhood := W
    isAffine := hV.basicOpen g
    mem := hxg
    coordinateAlgHom := G
    etale := hG.symm ▸ het' }, ?_⟩
  intro i
  change (X.left.presheaf.map (homOfLE (X.left.basicOpen_le g)).op ≫
    X.left.presheaf.germ W x.underlying hxg).hom (F (MvPolynomial.X i)) = c i
  rw [X.left.presheaf.germ_res]
  exact hv i

#print axioms s2e_localEtaleCoordinates_of_cotangent_basis
end HodgeLean.Foundations.Program
