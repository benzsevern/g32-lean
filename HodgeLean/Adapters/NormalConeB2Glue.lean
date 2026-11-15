import HodgeLean.Adapters.NormalConeB2Local
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-! # Gluing the affine deformation algebras

The extended Rees algebras `Γ(X, U)[t, I(U)/t]` over the affine opens `U` of `X` form a
presheaf of rings on the affine Zariski site, and the structure map from `𝒪_X` is
coequifibered by the localization statement. Mathlib's relative gluing turns it into a scheme
over `X`; the parameter `t` defines the map to the line.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry LaurentPolynomial

universe u

/-- The functorial map sends constants to constants.
Source: Mathlib, `AddMonoidAlgebra.mapRingHom_single`. -/
theorem a3b2_deformationMap_algebraMap {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal R) (J : Ideal S) (h : I.map φ ≤ J) (r : R) :
    a3b2_deformationMap φ I J h (algebraMap R _ r) = algebraMap S _ (φ r) :=
  Subtype.ext (AddMonoidAlgebra.mapRingHom_single _ _ _)

/-- The functorial map sends the parameter to the parameter.
Source: Mathlib, `AddMonoidAlgebra.mapRingHom_single`. -/
theorem a3b2_deformationMap_parameter {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal R) (J : Ideal S) (h : I.map φ ≤ J) :
    a3b2_deformationMap φ I J h (a3cc3_parameter I) = a3cc3_parameter J := by
  apply Subtype.ext
  change AddMonoidAlgebra.mapRingHom ℤ φ (T 1 : LaurentPolynomial R) = T 1
  rw [T, AddMonoidAlgebra.mapRingHom_single, map_one]
  rfl

/-- Two ring maps that agree coefficient by coefficient give the same functorial map.
Source: Mathlib, `AddMonoidAlgebra.coeff_mapRingHom`. -/
theorem a3b2_deformationMap_congr {R S : Type*} [CommRing R] [CommRing S] (φ ψ : R →+* S)
    (I : Ideal R) (J : Ideal S) (h : I.map φ ≤ J) (h' : I.map ψ ≤ J) (e : φ = ψ) :
    a3b2_deformationMap φ I J h = a3b2_deformationMap ψ I J h' := by
  subst e; rfl

/-- The functorial map of the identity is the identity.
Source: Mathlib, `AddMonoidAlgebra.coeff_mapRingHom`. -/
theorem a3b2_deformationMap_id {R : Type*} [CommRing R] (I : Ideal R) (h : I.map (RingHom.id R) ≤ I) :
    a3b2_deformationMap (RingHom.id R) I I h = RingHom.id _ := by
  ext x : 1
  apply Subtype.ext
  apply AddMonoidAlgebra.coeff_injective
  ext n
  exact a3b2_deformationMap_coeff _ _ _ _ x n

/-- The localization statement for any target ideal equal to the extended ideal.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
theorem a3b2_isLocalization_away' {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (J : Ideal S) (hJ : I.map (algebraMap R S) = J) (f : R)
    [IsLocalization.Away f S] :
    letI : Algebra (a3cc3_deformationAlgebra I) (a3cc3_deformationAlgebra J) :=
      (a3b2_deformationMap (algebraMap R S) I J hJ.le).toAlgebra
    IsLocalization.Away (algebraMap R (a3cc3_deformationAlgebra I) f)
      (a3cc3_deformationAlgebra J) := by
  subst hJ
  exact a3b2_isLocalization_away I f

/-- Scalars from the base point restrict along inclusions of opens.
Source: Mathlib, `AlgebraicGeometry.Scheme.Hom.appLE_map`. -/
theorem a3b2_fieldMap_res (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) {U V : X.Opens} (h : U ≤ V) :
    (X.presheaf.map (homOfLE h).op).hom.comp (a3b2_fieldMap k X p V) = a3b2_fieldMap k X p U := by
  rw [a3b2_fieldMap, a3b2_fieldMap, ← CommRingCat.hom_comp, Category.assoc]
  congr 2
  exact Scheme.Hom.appLE_map _ _ _

/-- The spectrum of the scalar map is the structure map on an affine open.
Source: Mathlib, `AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec`. -/
theorem a3b2_fromSpec_comp (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (a3b2_fieldMap k X p U)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU (by simp),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- The line map is compatible with restriction of the coefficient ring.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
theorem a3b2_lineMap_res (k : Type u) [Field k] {R S : Type*} [CommRing R] [CommRing S]
    (φ : k →+* R) (ψ : R →+* S) (I : Ideal R) (J : Ideal S) (h : I.map ψ ≤ J) :
    (a3b2_deformationMap ψ I J h).comp (a3b2_lineMap k φ I) = a3b2_lineMap k (ψ.comp φ) J := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [a3b2_lineMap, a3b2_deformationMap_algebraMap]
  · simp [a3b2_lineMap, a3b2_deformationMap_parameter]

variable {X : Scheme.{u}}

/-- An element of the affine Zariski site is an affine open.
Source: Mathlib, `AlgebraicGeometry.Scheme.AffineZariskiSite`. -/
theorem a3b2_mem (U : X.AffineZariskiSite) : U.toOpens ∈ X.affineOpens := U.2

/-- An element of the affine Zariski site as an affine open.
Source: Mathlib, `AlgebraicGeometry.Scheme.AffineZariskiSite`. -/
abbrev a3b2_aff (U : X.AffineZariskiSite) : X.affineOpens := ⟨U.toOpens, a3b2_mem U⟩

/-- An affine open as an element of the affine Zariski site.
Source: Mathlib, `AlgebraicGeometry.Scheme.AffineZariskiSite`. -/
def a3b2_site (U : X.affineOpens) : X.AffineZariskiSite := ⟨U.1, U.2⟩

@[simp] theorem a3b2_site_toOpens (U : X.affineOpens) : (a3b2_site U).toOpens = U.1 := rfl

/-- The presheaf of extended Rees algebras on the affine Zariski site.
Source: Fulton, *Intersection Theory*, second edition, §5.1, pp. 87–88. -/
def a3b2_diagram (I : X.IdealSheafData) : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (a3cc3_deformationAlgebra (I.ideal (a3b2_aff U.unop)))
  map {U V} i := CommRingCat.ofHom (a3b2_deformationMap
    (X.presheaf.map (homOfLE (Scheme.AffineZariskiSite.toOpens_mono (leOfHom i.unop))).op).hom
      (I.ideal (a3b2_aff U.unop)) (I.ideal (a3b2_aff V.unop))
    (I.map_ideal (U := a3b2_aff V.unop) (V := a3b2_aff U.unop)
      (Scheme.AffineZariskiSite.toOpens_mono (leOfHom i.unop))).le)
  map_id U := by
    ext x : 2
    apply Subtype.ext
    apply AddMonoidAlgebra.coeff_injective
    ext n
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply]
    refine (a3b2_deformationMap_coeff _ _ _ ?_ x n).trans ?_
    simp
  map_comp {U V W} i j := by
    ext x : 2
    apply Subtype.ext
    apply AddMonoidAlgebra.coeff_injective
    ext n
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.comp_apply]
    refine (a3b2_deformationMap_coeff _ _ _ ?_ x n).trans ?_
    refine Eq.trans ?_ ((a3b2_deformationMap_coeff _ _ _ ?_ _ n).trans
      (congrArg _ (a3b2_deformationMap_coeff _ _ _ ?_ x n))).symm
    · change _ = (X.presheaf.map _ ≫ X.presheaf.map _).hom _
      rw [← Functor.map_comp]
      rfl
    all_goals exact (I.map_ideal _).le

/-- The structure map from `𝒪_X` to the presheaf of extended Rees algebras.
Source: Fulton, *Intersection Theory*, second edition, §5.1, pp. 87–88. -/
def a3b2_diagramMap (I : X.IdealSheafData) :
    (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ a3b2_diagram I where
  app U := (CommRingCat.ofHom (algebraMap Γ(X, U.unop.toOpens)
    (a3cc3_deformationAlgebra (I.ideal (a3b2_aff U.unop)))) : _)
  naturality {U V} i := by
    ext x
    exact (a3b2_deformationMap_algebraMap _ (I.ideal (a3b2_aff U.unop)) (I.ideal (a3b2_aff V.unop))
      (I.map_ideal (U := a3b2_aff V.unop) (V := a3b2_aff U.unop)
        (Scheme.AffineZariskiSite.toOpens_mono (leOfHom i.unop))).le x).symm

/-- The structure map is coequifibered: the algebra over `D(f)` is the localization away
from `f` of the algebra over `U`.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88; the localization statement
`a3b2_isLocalization_away'`. -/
theorem a3b2_diagramMap_coequifibered (I : X.IdealSheafData) :
    ((a3b2_diagramMap I).Coequifibered) := by
  refine Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  letI : Algebra Γ(X, U.toOpens) Γ(X, X.basicOpen r) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
  haveI : IsLocalization.Away r Γ(X, X.basicOpen r) := U.2.isLocalization_basicOpen r
  exact a3b2_isLocalization_away' (I.ideal (a3b2_aff U)) _
    (I.map_ideal_basicOpen (a3b2_aff U) r) r

/-- The relative gluing data of the affine deformation algebras.
Source: Mathlib, `AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData`. -/
def a3b2_glueData (I : X.IdealSheafData) :
    (Scheme.AffineZariskiSite.directedCover X).RelativeGluingData :=
  Scheme.AffineZariskiSite.relativeGluingData (a3b2_diagramMap_coequifibered I)

instance (I : X.IdealSheafData) : ((a3b2_glueData I).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The glued deformation family.
Source: Fulton, *Intersection Theory*, second edition, §5.1, pp. 87–88; Hartshorne,
*Algebraic Geometry*, II, Exercise 5.17. -/
def a3b2_family (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) : A3b2Deformation k X p I := by
  let d := a3b2_glueData I
  let toLine : d.glued ⟶ a3b2_line k := colimit.desc d.functor
    { pt := a3b2_line k
      ι :=
        { app := fun U => Spec.map (CommRingCat.ofHom
            (a3b2_lineMap k (a3b2_fieldMap k X p U.toOpens) (I.ideal (a3b2_aff U))))
          naturality := fun U V i => by
            have h : CommRingCat.ofHom (a3b2_lineMap k (a3b2_fieldMap k X p V.toOpens)
                (I.ideal (a3b2_aff V))) ≫ (a3b2_diagram I).map i.op =
                CommRingCat.ofHom (a3b2_lineMap k (a3b2_fieldMap k X p U.toOpens)
                  (I.ideal (a3b2_aff U))) := by
              have hle := Scheme.AffineZariskiSite.toOpens_mono (leOfHom i)
              have h0 := (a3b2_lineMap_res k (a3b2_fieldMap k X p V.toOpens)
                (X.presheaf.map (homOfLE hle).op).hom (I.ideal (a3b2_aff V)) (I.ideal (a3b2_aff U))
                (I.map_ideal (U := a3b2_aff U) (V := a3b2_aff V) hle).le).trans
                (by rw [a3b2_fieldMap_res])
              exact congrArg CommRingCat.ofHom h0
            simp only [Functor.const_obj_map, Category.comp_id]
            exact (Spec.map_comp _ _).symm.trans (congrArg Spec.map h) } }
  have hP : ∀ U : X.affineOpens, IsPullback (d.toBase ∣_ U.1) (d.toBase ⁻¹ᵁ U.1).ι
      (Scheme.AffineZariskiSite.directedCover X |>.f (a3b2_site U)) d.toBase :=
    fun U => isPullback_morphismRestrict d.toBase U.1
  exact
    { M := d.glued
      toX := d.toBase
      toLine := toLine
      w := by
        refine colimit.hom_ext fun U => ?_
        rw [← Category.assoc, Scheme.Cover.RelativeGluingData.ι_toBase, ← Category.assoc,
          colimit.ι_desc]
        change (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.toOpens)
            (a3cc3_deformationAlgebra (I.ideal (a3b2_aff U))))) ≫ U.2.isoSpec.inv) ≫
            U.toOpens.ι ≫ p = Spec.map (CommRingCat.ofHom
              (a3b2_lineMap k (a3b2_fieldMap k X p U.toOpens) (I.ideal (a3b2_aff U)))) ≫
            Spec.map (CommRingCat.ofHom Polynomial.C)
        rw [Category.assoc, ← Category.assoc U.2.isoSpec.inv, IsAffineOpen.isoSpec_inv_ι,
          a3b2_fromSpec_comp, ← Spec.map_comp, ← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        ext a
        simp [a3b2_lineMap]
      chart := fun U => (hP U).isoIsPullback _ _ (d.isPullback_natTrans_ι_toBase (a3b2_site U))
      chart_toX := fun U => by
        refine Eq.trans ?_ (congrArg (· ≫ U.2.isoSpec.hom) (IsPullback.isoIsPullback_hom_fst _ _
          (hP U) (d.isPullback_natTrans_ι_toBase (a3b2_site U))))
        refine (congrArg (_ ≫ ·) ?_).trans (Category.assoc _ _ _).symm
        change _ = (Spec.map _ ≫ U.2.isoSpec.inv) ≫ U.2.isoSpec.hom
        simp
        rfl
      chart_toLine := fun U => by
        refine Eq.trans ?_ (congrArg (· ≫ toLine) (IsPullback.isoIsPullback_hom_snd _ _
          (hP U) (d.isPullback_natTrans_ι_toBase (a3b2_site U))))
        refine (congrArg (_ ≫ ·) ?_).trans (Category.assoc _ _ _).symm
        change _ = colimit.ι d.functor (a3b2_site U) ≫ toLine
        simp only [toLine, colimit.ι_desc]
        rfl }

end HodgeLean.Adapters
