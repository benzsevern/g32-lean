import HodgeLean.Foundations.Program.SchoenCycleC1FormalAffineBijective
import HodgeLean.Foundations.Program.SchoenCycleLocalizedAdicEtale
import HodgeLean.Foundations.Program.SchoenCycleComplexAffineFiniteType
import HodgeLean.Foundations.Program.SchoenCycleComplexPointAugmentation

/-! # Etaleness of actual affine sections from a formal stalk bijection -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A bijective actual formal stalk pullback makes the actual finite affine
section algebra etale at the specified complex point. -/
theorem s2e_c1_section_isEtaleAt_of_formal_pullback
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (x : ComplexPoint X) (hx : x.underlying ∈ f.left ⁻¹ᵁ U)
    (hcx : IsClosed ({x.underlying} : Set X.left))
    (hcy : IsClosed ({f.left x.underlying} : Set Y.left))
    (hbij : Function.Bijective (s2e_formal_stalk_pullback X Y f x.underlying)) :
    letI : Algebra Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) := (f.left.app U).hom.toAlgebra
    Algebra.IsEtaleAt Γ(Y.left, U)
      ((hU.preimage f.left).primeIdealOf ⟨x.underlying, hx⟩).asIdeal := by
  let W := f.left ⁻¹ᵁ U
  let A := Γ(Y.left, U)
  let C := Γ(X.left, W)
  letI := s2e_step1_sectionAlgebra Y U
  letI := s2e_step1_sectionAlgebra X W
  letI : Algebra A C := (f.left.app U).hom.toAlgebra
  letI := s2e_complex_section_app_tower X Y f U
  letI : Algebra.FiniteType ℂ A := s2e_complex_affine_sections_finiteType Y U hU
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  letI : Module.Finite A C := f.left.finite_app U hU
  letI : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  letI : Algebra.FinitePresentation A C := (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  let I := (hU.primeIdealOf ⟨f.left x.underlying, hx⟩).asIdeal
  let P := ((hU.preimage f.left).primeIdealOf ⟨x.underlying, hx⟩).asIdeal
  letI : I.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed _ hcy
  letI : P.IsMaximal := (hU.preimage f.left).primeIdealOf_isMaximal_of_isClosed _ hcx
  letI : P.LiesOver I := by
    constructor
    have he := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU W (hU.preimage f.left) le_rfl hx (f := f.left))
    change P.comap (f.left.appLE U W le_rfl).hom = I at he
    rw [show f.left.appLE U W le_rfl = f.left.app U from Scheme.Hom.appLE_eq_app f.left] at he
    exact he.symm
  let R := X.left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  letI : Algebra C R := TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨x.underlying, hx⟩
  letI : IsScalarTower ℂ C R := IsScalarTower.of_algebraMap_eq
    (fun c => ((s2e_complex_section_germ X W x.underlying hx).commutes c).symm)
  letI : IsLocalization.AtPrime R P := (hU.preimage f.left).isLocalization_stalk ⟨x.underlying, hx⟩
  let E := (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) R).restrictScalars ℂ
  let ε := (s2e_complex_point_augmentation X x).comp E.toAlgHom
  obtain ⟨h, hb⟩ := s2e_c1_affine_adic_bijective_of_formal_pullback X Y f U hU
    x.underlying hx hcx hcy hbij
  exact s2e_isEtaleAt_of_localized_adic_bijective ℂ A C I P h hb ε

end HodgeLean.Foundations.Program
