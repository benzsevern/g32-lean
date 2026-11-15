import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_presheafedSpace_epi
    {C : Type*} [Category C] {X Y : PresheafedSpace C} (f : X ⟶ Y)
    (hsurj : Function.Surjective f.base)
    (hmono : ∀ U, Mono (f.c.app U)) : Epi f := by
  constructor
  rintro Z ⟨u, uc⟩ ⟨v, vc⟩ heq
  have huv : u = v := by
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    exact congrArg (fun h : X ⟶ Z => h.base x) heq
  subst v
  have hc : uc = vc := by
    ext U
    letI := hmono (Opposite.op ((TopologicalSpace.Opens.map u).obj U))
    apply (cancel_mono (f.c.app (Opposite.op ((TopologicalSpace.Opens.map u).obj U)))).mp
    have hh := PresheafedSpace.congr_app heq (Opposite.op U)
    dsimp at hh
    rw [X.presheaf.map_id, Category.comp_id] at hh
    exact hh
  subst vc
  rfl

lemma s2v_i1ahi_scheme_epi_of_sections
    {X Y : Scheme} (f : X ⟶ Y) [Surjective f]
    (hinj : ∀ U : Y.Opens, Function.Injective (f.app U).hom) : Epi f := by
  apply CategoryTheory.Functor.epi_of_epi_map Scheme.forgetToLocallyRingedSpace
  apply CategoryTheory.Functor.epi_of_epi_map LocallyRingedSpace.forgetToSheafedSpace
  apply CategoryTheory.Functor.epi_of_epi_map SheafedSpace.forgetToPresheafedSpace
  apply s2v_i1ahi_presheafedSpace_epi _ f.surjective
  intro U
  exact ConcreteCategory.mono_of_injective _ (hinj U.unop)

lemma s2v_i1ahi_schematic_dominance_of_appTop
    {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) [QuasiCompact f]
    (hinj : Function.Injective f.appTop.hom) : IsSchemeTheoreticallyDominant f := by
  constructor
  apply le_antisymm _ bot_le
  apply Scheme.IdealSheafData.le_of_isAffine
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot]
  exact le_of_eq ((RingHom.injective_iff_ker_eq_bot _).mp hinj)

lemma s2v_i1ahi_scheme_epi_of_schematic_dominance
    {X Y : Scheme} (f : X ⟶ Y) [Surjective f] [QuasiCompact f]
    [IsSchemeTheoreticallyDominant f] : Epi f :=
  s2v_i1ahi_scheme_epi_of_sections f (fun U => f.app_injective U)

lemma s2v_i1ahi_restricted_scheme_epi
    {X Y : Scheme} (f : X ⟶ Y) [Surjective f] [QuasiCompact f]
    [IsSchemeTheoreticallyDominant f] (U : Y.Opens) : Epi (f ∣_ U) := by
  haveI : IsSchemeTheoreticallyDominant (f ∣_ U) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict f U).flip
  haveI : Surjective (f ∣_ U) := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict f U).flip (inferInstance : Surjective f)
  exact s2v_i1ahi_scheme_epi_of_schematic_dominance (f ∣_ U)

lemma s2v_i1ahi_specMap_appTop_injective
    {R S : CommRingCat} (f : R ⟶ S) (hinj : Function.Injective f.hom) :
    Function.Injective (Spec.map f).appTop.hom := by
  intro x y h
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).injective
  apply hinj
  have he := congrArg (Scheme.ΓSpecIso S).hom.hom h
  change ((Spec.map f).appTop ≫ (Scheme.ΓSpecIso S).hom).hom x =
    ((Spec.map f).appTop ≫ (Scheme.ΓSpecIso S).hom).hom y at he
  rw [Scheme.ΓSpecIso_naturality] at he
  exact he

end HodgeLean.Foundations.Program
