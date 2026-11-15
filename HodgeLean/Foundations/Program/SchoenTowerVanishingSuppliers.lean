import HodgeLean.Foundations.Program.SchoenTowerFinitePointFibres
import HodgeLean.Foundations.SegreProjective
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import HodgeLean.Foundations.Program.SchoenTowerFibreDefs
import HodgeLean.Foundations.Program.SchoenTowerSheafDefs
import HodgeLean.Foundations.Program.SchoenTowerModelTransport
import HodgeLean.Foundations.Program.SchoenTowerActualCharacterStalk

/-! # Retained cyclic-cover tower statements
Implication from the retained curve quotient, paired branch points, blowup
universal properties and normalization maps to exceptional-cover geometry.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- Finite normalization descends along a finite integral extension of the base ring.
Source: Atiyah–Macdonald, Proposition 5.17 and transitivity of integral dependence. -/
theorem s2v_finite_integralClosure_over_finite_base {P A F L : Type*}
    [CommRing P] [IsDomain P] [IsIntegrallyClosed P] [IsNoetherianRing P]
    [CommRing A] [Algebra P A] [Module.Finite P A]
    [Field F] [Algebra P F] [IsFractionRing P F]
    [Field L] [Algebra F L] [Module.Finite F L] [Algebra.IsSeparable F L]
    [Algebra P L] [IsScalarTower P F L] [Algebra A L] [IsScalarTower P A L] :
    Module.Finite A (integralClosure A L) := by
  haveI : Algebra.IsIntegral P A := Algebra.IsIntegral.of_finite P A
  haveI : Module.Finite P (integralClosure P L) :=
    IsIntegralClosure.finite P F L (integralClosure P L)
  have hmem : ∀ x : L, x ∈ integralClosure P L ↔ x ∈ integralClosure A L := by
    intro x
    rw [mem_integralClosure_iff, mem_integralClosure_iff]
    exact ⟨fun hx => hx.tower_top, fun hx => isIntegral_trans (R := P) (A := A) x hx⟩
  let e : integralClosure P L ≃ₗ[P] (integralClosure A L).restrictScalars P :=
    LinearEquiv.ofEq (integralClosure P L).toSubmodule
      ((integralClosure A L).restrictScalars P).toSubmodule (by ext x; exact hmem x)
  haveI : Module.Finite P ((integralClosure A L).restrictScalars P) := Module.Finite.equiv e
  let e2 : (integralClosure A L).restrictScalars P ≃ₗ[P] integralClosure A L :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Module.Finite P (integralClosure A L) := Module.Finite.equiv e2
  exact Module.Finite.of_restrictScalars_finite P A (integralClosure A L)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Integral closure in a finite covering-field extension is finite for a finite-type domain.
Source: Atiyah–Macdonald, Proposition 5.17 and Exercise 5.16; Eisenbud, Corollary 13.13. -/
theorem s2v_finite_integralClosure_coveringField {k A F L : Type*}
    [Field k] [CharZero k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field L] [Algebra F L] [Module.Finite F L]
    [Algebra A L] [IsScalarTower A F L] :
    Module.Finite A (integralClosure A L) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin s) k
  let :=  g.toRingHom.toAlgebra
  have : Module.Finite P A := hfin
  let :=  ((algebraMap A F).comp (algebraMap P A)).toAlgebra
  have : IsScalarTower P A F := .of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  have hPF : Function.Injective (algebraMap P F) := (IsFractionRing.injective A F).comp hinj
  have : FaithfulSMul P F := (faithfulSMul_iff_algebraMap_injective P F).mpr hPF
  let FP := FractionRing P
  let :=  FractionRing.liftAlgebra P F
  have : IsScalarTower P FP F := inferInstance
  have : Algebra.IsIntegral P A := Algebra.IsIntegral.of_finite P A
  have : Module.Finite FP F := Module.Finite.of_isLocalization P A (Rₚ := FP) (Sₚ := F)
    (nonZeroDivisors P)
  let :=  ((algebraMap F L).comp (algebraMap P F)).toAlgebra
  have : IsScalarTower P F L := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower P A L := .of_algebraMap_eq fun x => by
    change algebraMap F L (algebraMap A F (algebraMap P A x)) =
      algebraMap A L (algebraMap P A x)
    rw [← IsScalarTower.algebraMap_apply A F L]
  let :=  ((algebraMap F L).comp (algebraMap FP F)).toAlgebra
  have : IsScalarTower FP F L := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower P FP L := .of_algebraMap_eq fun x => by
    change algebraMap F L (algebraMap P F x) =
      algebraMap F L (algebraMap FP F (algebraMap P FP x))
    rw [← IsScalarTower.algebraMap_apply P FP F]
  have : Module.Finite FP L := Module.Finite.trans F L
  exact s2v_finite_integralClosure_over_finite_base (P := P) (A := A) (F := FP) (L := L)

/-- Finite integral closures on affine opens give a finite relative normalization map.
Source: Stacks Project, tag 035H, the affine description of relative normalization. -/
theorem s2v_normalization_finite_of_affine_integralClosure {X Y : Scheme}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hfin : ∀ U : Y.affineOpens,
      letI := (f.app U.1).hom.toAlgebra
      Module.Finite Γ(Y, U.1) (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))) :
    IsFinite f.fromNormalization := by
  refine { finite_app := ?_ }
  intro U hU
  letI := (f.app U).hom.toAlgebra
  haveI : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := hfin ⟨U, hU⟩
  rw [f.fromNormalization_app hU]
  exact (RingHom.Finite.of_surjective (f.normalizationObjIso hU).inv.hom
    (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).surjective).comp
      (RingHom.finite_algebraMap.mpr inferInstance)

/-- Sections on a nonempty inverse image in a field spectrum identify with that field.
Source: Stacks Project, tag 035H, affine sections in relative normalization. -/
def s2v_fieldSourceSectionsIso {L : Type} [Field L] {Y : Scheme}
    (f : Spec (CommRingCat.of L) ⟶ Y) (U : Y.Opens)
    (hU : f ⁻¹ᵁ U = ⊤) : Γ(Spec (CommRingCat.of L), f ⁻¹ᵁ U) ≅ CommRingCat.of L :=
  (Spec (CommRingCat.of L)).presheaf.mapIso (eqToIso hU).symm.op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of L)

/-- Field-valued affine integral-closure calculations give a finite generic-source normalization.
Source: Stacks Project, tag 035H, relative normalization on affine opens. -/
theorem s2v_normalization_finite_of_field_integralClosure {L : Type} [Field L] {Y : Scheme}
    (f : Spec (CommRingCat.of L) ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hfin : ∀ (U : Y.affineOpens) (hU : f ⁻¹ᵁ U.1 = ⊤),
      letI := (f.app U.1 ≫ (s2v_fieldSourceSectionsIso f U.1 hU).hom).hom.toAlgebra
      Module.Finite Γ(Y, U.1) (integralClosure Γ(Y, U.1) L)) :
    IsFinite f.fromNormalization := by
  apply s2v_normalization_finite_of_affine_integralClosure f
  intro U
  letI := (f.app U.1).hom.toAlgebra
  by_cases hU : Nonempty (f ⁻¹ᵁ U.1)
  · have htop : f ⁻¹ᵁ U.1 = ⊤ := by
      apply top_unique
      intro x _
      obtain ⟨y⟩ := hU
      exact (Subsingleton.elim y.val x) ▸ y.property
    let e := s2v_fieldSourceSectionsIso f U.1 htop
    letI := (f.app U.1 ≫ e.hom).hom.toAlgebra
    let ea : Γ(Spec (CommRingCat.of L), f ⁻¹ᵁ U.1) ≃ₐ[Γ(Y, U.1)] L :=
      { e.commRingCatIsoToRingEquiv with commutes' := fun _ => rfl }
    haveI : Module.Finite Γ(Y, U.1) (integralClosure Γ(Y, U.1) L) := hfin U htop
    exact Module.Finite.equiv ea.symm.mapIntegralClosure.toLinearEquiv
  · have hbot : f ⁻¹ᵁ U.1 = ⊥ := by
      apply bot_unique
      intro x hx
      exact (hU ⟨⟨x, hx⟩⟩).elim
    haveI : Subsingleton Γ(Spec (CommRingCat.of L), f ⁻¹ᵁ U.1) := by
      rw [hbot]
      infer_instance
    infer_instance

/-- A dominant generic source embeds affine base sections into the retained covering field.
Source: Stacks Project, tags 01R5 and 035H, dominant maps to reduced schemes and normalization. -/
theorem s2v_fieldSource_coefficient_injective {L : Type} [Field L] {Y : Scheme}
    [IsReduced Y] (f : Spec (CommRingCat.of L) ⟶ Y) [QuasiCompact f] [IsDominant f]
    (U : Y.Opens) (hU : f ⁻¹ᵁ U = ⊤) :
    Function.Injective (f.app U ≫ (s2v_fieldSourceSectionsIso f U hU).hom).hom := by
  haveI : IsSchemeTheoreticallyDominant f := .of_isDominant f
  exact (ConcreteCategory.bijective_of_isIso (s2v_fieldSourceSectionsIso f U hU).hom).injective.comp
    (f.app_injective U)

/-- Finite affine fraction-field extensions give a finite normalization of an integral complex scheme.
Source: Atiyah–Macdonald, Proposition 5.17; Stacks Project, tag 035H. -/
theorem s2v_normalization_finite_of_affine_fraction_fields {L : Type} [Field L]
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    (f : Spec (CommRingCat.of L) ⟶ Y.left)
    [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
    (hfin : ∀ (U : Y.left.affineOpens) (hU : Nonempty U.1) (hfull : f ⁻¹ᵁ U.1 = ⊤),
      letI := hU
      letI := (f.app U.1 ≫ (s2v_fieldSourceSectionsIso f U.1 hfull).hom).hom.toAlgebra
      letI : FaithfulSMul Γ(Y.left, U.1) L :=
        (faithfulSMul_iff_algebraMap_injective Γ(Y.left, U.1) L).mpr
          (s2v_fieldSource_coefficient_injective f U.1 hfull)
      letI := FractionRing.liftAlgebra Γ(Y.left, U.1) L
      Module.Finite (FractionRing Γ(Y.left, U.1)) L) :
    IsFinite (s2b_normalizationMap Y f).left := by
  change IsFinite f.fromNormalization
  apply s2v_normalization_finite_of_field_integralClosure f
  intro U hfull
  have hU : Nonempty U.1 := by
    refine ⟨⟨f (IsLocalRing.closedPoint L), ?_⟩⟩
    have hm : IsLocalRing.closedPoint L ∈ f ⁻¹ᵁ U.1 := by rw [hfull]; trivial
    exact hm
  letI := hU
  letI : Algebra ℂ Γ(Y.left, U.1) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ Y.hom.appLE ⊤ U.1 (by simp)).hom.toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(Y.left, U.1) := by
    refine RingHom.finiteType_algebraMap.mp ?_
    change ((Y.hom.appLE ⊤ U.1 (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom).FiniteType
    refine RingHom.FiniteType.comp ?_ ?_
    · exact HasRingHomProperty.appLE (P := @LocallyOfFiniteType) Y.hom inferInstance
        ⟨⊤, isAffineOpen_top _⟩ U (by simp)
    · exact RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).surjective
  letI := (f.app U.1 ≫ (s2v_fieldSourceSectionsIso f U.1 hfull).hom).hom.toAlgebra
  letI : FaithfulSMul Γ(Y.left, U.1) L :=
    (faithfulSMul_iff_algebraMap_injective Γ(Y.left, U.1) L).mpr
      (s2v_fieldSource_coefficient_injective f U.1 hfull)
  letI := FractionRing.liftAlgebra Γ(Y.left, U.1) L
  haveI : IsScalarTower Γ(Y.left, U.1) (FractionRing Γ(Y.left, U.1)) L := inferInstance
  haveI : Module.Finite (FractionRing Γ(Y.left, U.1)) L := hfin U hU hfull
  exact s2v_finite_integralClosure_coveringField (k := ℂ)
    (A := Γ(Y.left, U.1)) (F := FractionRing Γ(Y.left, U.1)) (L := L)

theorem s2v_pullback_cohomology_vanishing_of_stalks {X Y : TopCat.{0}}
    (f : X ⟶ Y) (F : TopCat.Sheaf AddCommGrpCat.{0} Y)
    (hF : ∀ x : X, Subsingleton ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := Y) F.obj (f x))) (n : ℕ) :
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj F) n) := by
  apply Sheaf.subsingleton_H_of_isZero
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro x
  letI := hF x
  let e := s3_pullback_stalk_iso f F x
  haveI : Subsingleton
      ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := X)
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj F).obj x) :=
    e.symm.addCommGroupIsoToAddEquiv.injective.subsingleton
  change IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := X)
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj F).obj x)
  exact AddCommGrpCat.isZero_of_subsingleton _

theorem s2v_projective_of_closedImmersion {X Y : Over (Spec ↧ℂ)} (i : X ⟶ Y)
    [IsClosedImmersion i.left] [IsProjective Y.hom] : IsProjective X.hom := by
  obtain ⟨P⟩ := IsProjective.nonempty_presentation (f := Y.hom)
  let : IsClosedImmersion P.immersion := P.isClosedImmersion
  exact ⟨⟨{
    ambientDimension := P.ambientDimension
    immersion := i.left ≫ P.immersion
    isClosedImmersion := inferInstance
    immersion_toBase := by rw [Category.assoc, P.immersion_toBase, i.w] }⟩⟩
theorem s2v_preimage_projective {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsSeparated B.hom] [IsProjective E.hom]
    (β : W ⟶ B) (j : E ⟶ B) : IsProjective (s2b_preimage β j).hom := by
  let i : s2b_preimage β j ⟶ W ⊗ E :=
    CartesianMonoidalCategory.lift (pullback.fst β j) (pullback.snd β j)
  let : IsClosedImmersion i.left := s2v_pullback_toProduct_closedImmersion β j
  let : IsProjective (W ⊗ E).hom :=
    HodgeLean.Foundations.spec_g3c_isProjective_pullback W.hom E.hom
  exact s2v_projective_of_closedImmersion i
theorem s2v_schemeFibre_projective {E K : Over (Spec ↧ℂ)}
    [IsProjective E.hom] [IsSeparated K.hom] (p : E ⟶ K) (k : ComplexPoint K) :
    IsProjective (pullback p k).hom := by
  let : IsClosedImmersion (pullback.fst p k).left := s2v_schemeFibre_closedImmersion p k
  exact s2v_projective_of_closedImmersion (pullback.fst p k)
theorem s2v_centre_and_exceptional_projective {B' B : Over (Spec ↧ℂ)}
    [IsProjective B'.hom] [IsProjective B.hom]
    (b : B' ⟶ B) (I : B.left.IdealSheafData) :
    IsProjective (s2c_subscheme B I).hom ∧ IsProjective (s2c_exceptional b I).hom := by
  letI : IsClosedImmersion (s2c_subschemeι B I).left :=
    inferInstanceAs (IsClosedImmersion I.subschemeι)
  letI : IsProjective (s2c_subscheme B I).hom :=
    s2v_projective_of_closedImmersion (s2c_subschemeι B I)
  exact ⟨inferInstance, s2v_preimage_projective b (s2c_subschemeι B I)⟩


end HodgeLean.Foundations.Program
