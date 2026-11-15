import HodgeLean.Foundations.Program.SchoenCycleC1GenericEtaleSchemeHelpers
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Generic etale opens of the actual finite projection -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Etale base neighbourhoods transport through an actual isomorphism square. -/
theorem s2e_c1_etale_restriction_of_iso_square
    {X Y X' Y' : Scheme} (f : X ⟶ Y) (g : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y') (he : f ≫ eY.hom = eX.hom ≫ g)
    (V : Y'.Opens) [Etale (g ∣_ V)] :
    Etale (f ∣_ eY.hom ⁻¹ᵁ V) := by
  haveI : Etale ((f ≫ eY.hom) ∣_ V) := by
    rw [he, morphismRestrict_comp]
    infer_instance
  haveI : Etale ((f ∣_ eY.hom ⁻¹ᵁ V) ≫ (eY.hom ∣_ V)) := by
    rw [← morphismRestrict_comp]
    infer_instance
  exact Etale.of_comp (f ∣_ eY.hom ⁻¹ᵁ V) (eY.hom ∣_ V)

/-- A finite dominant map between integral affine schemes in characteristic
zero has an actual nonempty finite etale base neighbourhood. -/
theorem s2e_c1_finite_affine_exists_etale_base_open
    (X Y : Scheme.{0}) [IsAffine X] [IsAffine Y] [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [CharZero Γ(Y, ⊤)]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] :
    ∃ U : Y.Opens, (U : Set Y).Nonempty ∧ IsFinite (f ∣_ U) ∧ Etale (f ∣_ U) := by
  let R := Γ(Y, ⊤)
  let S := Γ(X, ⊤)
  letI : Algebra R S := f.appTop.hom.toAlgebra
  haveI : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  haveI : FaithfulSMul R S :=
    (faithfulSMul_iff_algebraMap_injective R S).mpr (f.app_injective ⊤)
  haveI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  haveI : Module.Finite R S := f.finite_appTop
  haveI : Algebra.FinitePresentation R S :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  obtain ⟨V, hV, _, hEt⟩ := s2e_c1_finite_spec_exists_etale_base_open R S
  have hmap : CommRingCat.ofHom (algebraMap R S) = f.appTop := rfl
  rw [hmap] at hEt
  haveI := hEt
  let U := Y.isoSpec.hom ⁻¹ᵁ V
  haveI : Etale (f ∣_ U) := s2e_c1_etale_restriction_of_iso_square f
    (Spec.map f.appTop) X.isoSpec Y.isoSpec (Scheme.isoSpec_hom_naturality f).symm V
  obtain ⟨v, hv⟩ := hV
  obtain ⟨y, hy⟩ := Y.isoSpec.hom.surjective v
  refine ⟨U, ⟨y, ?_⟩, inferInstance, inferInstance⟩
  change Y.isoSpec.hom y ∈ V
  rwa [hy]


end HodgeLean.Foundations.Program
