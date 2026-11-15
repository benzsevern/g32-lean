import HodgeLean.Adapters.NormalConeB2Glue
import HodgeLean.Adapters.NormalCone
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Chart-local properties of a deformation family

For a deformation family `D`, the preimages of the affine opens of `X` cover the total space
and each is identified by its chart with `Spec Γ(X, U)[t, I(U)/t]`, over `X` and over the line.
Properties of `D` that are local on the total space reduce to the affine algebra.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData}

/-- The preimages of the affine opens cover the total space.
Source: Mathlib, `AlgebraicGeometry.iSup_affineOpens_eq_top`. -/
theorem a3b2_iSup_preimage (D : A3b2Deformation k X p I) :
    ⨆ U : X.affineOpens, D.toX ⁻¹ᵁ U.1 = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
  rfl

/-- The line map on a chart.
Source: the field `A3b2Deformation.chart_toLine`. -/
theorem a3b2_ι_toLine (D : A3b2Deformation k X p I) (U : X.affineOpens) :
    (D.toX ⁻¹ᵁ U.1).ι ≫ D.toLine = (D.chart U).hom ≫
      Spec.map (CommRingCat.ofHom (a3b2_lineMap k (a3b2_fieldMap k X p U.1) (I.ideal U))) :=
  (D.chart_toLine U).symm

/-- The projection to `X` on a chart.
Source: the field `A3b2Deformation.chart_toX` and `IsAffineOpen.isoSpec_hom_fromSpec`. -/
theorem a3b2_ι_toX (D : A3b2Deformation k X p I) (U : X.affineOpens) :
    (D.toX ⁻¹ᵁ U.1).ι ≫ D.toX = (D.chart U).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (a3cc3_deformationAlgebra (I.ideal U)))) ≫
        U.2.fromSpec := by
  rw [← morphismRestrict_ι, ← IsAffineOpen.isoSpec_hom_fromSpec U.2, ← Category.assoc,
    ← D.chart_toX, Category.assoc]

/-- The projection to `X` is affine.
Source: Fulton, *Intersection Theory*, second edition, §5.1, pp. 87–88; Mathlib,
`AlgebraicGeometry.IsAffineHom`. -/
theorem a3b2_isAffineHom (D : A3b2Deformation k X p I) : IsAffineHom D.toX := by
  constructor
  intro U hU
  have : IsAffine (D.toX ⁻¹ᵁ (⟨U, hU⟩ : X.affineOpens).1).toScheme :=
    IsAffine.of_isIso (D.chart ⟨U, hU⟩).hom
  exact this

/-- On a chart, the parameter-line map is the A3-B1 parameter map for the scalar structure.
Source: definitions `a3b2_lineMap` and `a3b1_parameterMap`. -/
theorem a3b2_lineMap_eq_parameterMap {R : Type*} [CommRing R] (φ : k →+* R) (J : Ideal R) :
    letI : Algebra k R := φ.toAlgebra
    a3b2_lineMap k φ J = a3b1_parameterMap k R J := rfl

/-- The family is flat over the parameter line.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88; stage A3-B1, `a3b1_flat`. -/
theorem a3b2_flat_toLine (D : A3b2Deformation k X p I) : Flat D.toLine := by
  haveI : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Flat) _ (a3b2_iSup_preimage D) fun U => ?_
  rw [a3b2_ι_toLine]
  haveI : Flat (Spec.map (CommRingCat.ofHom
      (a3b2_lineMap k (a3b2_fieldMap k X p U.1) (I.ideal U)))) := by
    rw [Flat.SpecMap_iff]
    letI : Algebra k Γ(X, U.1) := (a3b2_fieldMap k X p U.1).toAlgebra
    letI : Algebra (Polynomial k) (a3cc3_deformationAlgebra (I.ideal U)) :=
      (a3b1_parameterMap k Γ(X, U.1) (I.ideal U)).toAlgebra
    have := a3b1_flat k Γ(X, U.1) (I.ideal U)
    exact this
  infer_instance

/-- The projection to `X` is locally of finite type when `X` is locally Noetherian.
Source: Fulton, *Intersection Theory*, second edition, §5.1;
`a3cc3_deformationAlgebra_finiteType`. -/
theorem a3b2_locallyOfFiniteType_toX [IsLocallyNoetherian X] (D : A3b2Deformation k X p I) :
    LocallyOfFiniteType D.toX := by
  haveI : IsZariskiLocalAtSource (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFiniteType) _ (a3b2_iSup_preimage D) fun U => ?_
  rw [a3b2_ι_toX]
  haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U.1) (a3cc3_deformationAlgebra (I.ideal U))))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    have := a3cc3_deformationAlgebra_finiteType (I.ideal U)
    exact RingHom.finiteType_algebraMap.mpr this
  haveI : LocallyOfFiniteType U.2.fromSpec := by
    haveI : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec _
    infer_instance
  infer_instance

/-- The total space is locally Noetherian when `X` is.
Source: Mathlib, `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`. -/
theorem a3b2_isLocallyNoetherian_M [IsLocallyNoetherian X] (D : A3b2Deformation k X p I) :
    IsLocallyNoetherian D.M :=
  haveI := a3b2_locallyOfFiniteType_toX D
  LocallyOfFiniteType.isLocallyNoetherian D.toX

/-- The total space is Noetherian when `X` is.
Source: Mathlib, `AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`. -/
theorem a3b2_isNoetherian_M [IsNoetherian X] (D : A3b2Deformation k X p I) :
    IsNoetherian D.M :=
  haveI := a3b2_isLocallyNoetherian_M D
  haveI := a3b2_isAffineHom D
  haveI : CompactSpace D.M := QuasiCompact.compactSpace_of_compactSpace D.toX
  { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }

/-- The point `t = c` of the line is a closed immersion.
Source: Mathlib, `AlgebraicGeometry.IsClosedImmersion.spec_of_surjective`. -/
instance a3b2_point_isClosedImmersion (c : k) : IsClosedImmersion (a3b2_point k c) :=
  IsClosedImmersion.spec_of_surjective _ fun a => ⟨Polynomial.C a, by simp⟩

/-- The zero fibre is locally Noetherian when `X` is.
Source: Mathlib, `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`. -/
theorem a3b2_zeroFibre_isLocallyNoetherian [IsLocallyNoetherian X] (D : A3b2Deformation k X p I) :
    IsLocallyNoetherian (a3b2_zeroFibre D) :=
  haveI := a3b2_isLocallyNoetherian_M D
  LocallyOfFiniteType.isLocallyNoetherian (pullback.fst D.toLine (a3b2_point k 0))

/-- The zero fibre is Noetherian when `X` is.
Source: Mathlib, `AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`. -/
theorem a3b2_zeroFibre_isNoetherian [IsNoetherian X] (D : A3b2Deformation k X p I) :
    IsNoetherian (a3b2_zeroFibre D) :=
  haveI := a3b2_zeroFibre_isLocallyNoetherian D
  haveI := a3b2_isNoetherian_M D
  haveI : CompactSpace (a3b2_zeroFibre D) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst D.toLine (a3b2_point k 0))
  { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }

end HodgeLean.Adapters
