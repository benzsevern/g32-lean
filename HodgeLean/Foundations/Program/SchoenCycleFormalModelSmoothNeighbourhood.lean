import HodgeLean.Foundations.Program.SchoenCycleBasicPolynomialGerms
import HodgeLean.Foundations.Program.SchoenCycleFormalModelEtaleNeighbourhood
import HodgeLean.Foundations.Program.SchoenCycleActualLocalizationEtale
import HodgeLean.Foundations.Program.SchoenCycleComplexPointAugmentation
import HodgeLean.Foundations.Program.SchoenCycleComplexAffineFiniteType
import HodgeLean.Foundations.Program.SchoenCycleComplexSectionRestriction
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

/-- An actual coefficient formal model and represented cotangent basis yield a standard smooth affine neighbourhood of the actual complex point, without a smoothness premise on the scheme.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.6.1 and 17.11.1; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_standardSmooth_neighbourhood_of_formal_model
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (n : ℕ) (x : ComplexPoint X) :
    let A := X.left.presheaf.stalk x.underlying
    letI : Algebra ℂ A := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∀ (E : AdicCompletion (IsLocalRing.maximalIdeal A) A ≃ₐ[ℂ]
        AdicCompletion (idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
      (c : Fin n → A) (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal A)
      (b : Module.Basis (Fin n) ℂ (IsLocalRing.maximalIdeal A).Cotangent),
      (∀ i, b i = (IsLocalRing.maximalIdeal A).toCotangent ⟨c i, hc i⟩) →
      ∃ (W : X.left.Opens) (_ : IsAffineOpen W) (_ : x.underlying ∈ W),
        letI := s2e_step1_sectionAlgebra X W
        Algebra.IsStandardSmoothOfRelativeDimension n ℂ Γ(X.left, W) := by
  dsimp only
  let A := X.left.presheaf.stalk x.underlying
  letI : Algebra ℂ A := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  intro E c hc b hb
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := x.underlying) (U := ⊤) trivial
  obtain ⟨f, hxf, F, hF⟩ := s2e_basic_polynomial_germ_representatives X x.underlying U hU hxU c
  let V := X.left.basicOpen f
  have hV : IsAffineOpen V := hU.basicOpen f
  letI : Nonempty V := ⟨⟨x.underlying, hxf⟩⟩
  let S := Γ(X.left, V)
  letI : Algebra ℂ S := s2e_step1_sectionAlgebra X V
  letI : Algebra.FiniteType ℂ S := s2e_complex_affine_sections_finiteType X V hV
  letI : Algebra S A := TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨x.underlying, hxf⟩
  letI : IsScalarTower ℂ S A := IsScalarTower.of_algebraMap_eq (fun z =>
    ((s2e_complex_section_germ X V x.underlying hxf).commutes z).symm)
  let P : Ideal S := (hV.primeIdealOf ⟨x.underlying, hxf⟩).asIdeal
  letI : IsLocalization.AtPrime A P := hV.isLocalization_stalk ⟨x.underlying, hxf⟩
  have hv (i : Fin n) : algebraMap S A (F (MvPolynomial.X i)) = c i := by
    have hh := DFunLike.congr_fun hF (MvPolynomial.X i)
    simp only [AlgHom.comp_apply, aeval_X] at hh
    exact hh
  obtain ⟨g, hg, het⟩ := s2e_etale_neighbourhood_of_formal_model
    ℂ S (Fin n) P A (s2e_complex_point_augmentation X x) E (fun i => F (MvPolynomial.X i))
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
  let H : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, W) :=
    aeval (fun i => algebraMap S Γ(X.left, W) (F (MvPolynomial.X i)))
  have het' : H.toRingHom.Etale :=
    s2e_actual_localization_coordinate_etale ℂ S Γ(X.left, W) (Fin n) g _ het
  letI : Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, W) := H.toAlgebra
  letI : IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, W) :=
    IsScalarTower.of_algebraMap_eq' H.comp_algebraMap.symm
  letI : Algebra.Etale (MvPolynomial (Fin n) ℂ) Γ(X.left, W) := RingHom.etale_algebraMap.mp het'
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin n) ℂ) Γ(X.left, W) :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  refine ⟨W, hV.basicOpen g, hxg, ?_⟩
  simpa only [zero_add] using Algebra.IsStandardSmoothOfRelativeDimension.trans
    n 0 ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, W)

#print axioms s2e_standardSmooth_neighbourhood_of_formal_model
end HodgeLean.Foundations.Program
