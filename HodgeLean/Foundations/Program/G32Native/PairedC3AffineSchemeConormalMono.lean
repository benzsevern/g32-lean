import HodgeLean.Foundations.Program.G32Native.PairedC3AffineConormalMono
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineSchemeFirstArrow
import HodgeLean.Foundations.Program.G32Native.UnionConormalIsoTransport
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth conormal injectivity on actual affine schemes -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Affine scheme coordinates carry the natural first map to the smooth
quotient-tower injection, without changing the original immersions.
Source: Hartshorne, Algebraic Geometry, II.8.12 and II.8.17. -/
theorem paired_c3_affine_scheme_conormal_first_mono
    (X F Q : Scheme.{0}) [IsAffine X] [IsAffine F] [IsAffine Q]
    (x : X ⟶ Spec ↧ℂ) (φ : F ⟶ Spec ↧ℂ) (q : Q ⟶ Spec ↧ℂ)
    [Smooth x] [Smooth φ]
    (i : F ⟶ X) (c : Q ⟶ X) (j : Q ⟶ F)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (ha : j ≫ i = c) (hi : i ≫ x = φ) (hj : j ≫ φ = q) :
    Mono (unionConormalFirst i c j ha) := by
  haveI : IsClosedImmersion c := by rw [← ha]; infer_instance
  let K := Γ(Spec ↧ℂ, ⊤)
  let A := Γ(X, ⊤)
  let B := Γ(F, ⊤)
  let C := Γ(Q, ⊤)
  letI : Algebra K A := x.appTop.hom.toAlgebra
  letI : Algebra K B := φ.appTop.hom.toAlgebra
  letI : Algebra K C := q.appTop.hom.toAlgebra
  letI : Algebra A B := i.appTop.hom.toAlgebra
  letI : Algebra A C := c.appTop.hom.toAlgebra
  letI : Algebra B C := j.appTop.hom.toAlgebra
  have hKB : x.appTop ≫ i.appTop = φ.appTop := by
    rw [← Scheme.Hom.comp_appTop, hi]
  have hc : c ≫ x = q := by rw [← ha, Category.assoc, hi, hj]
  have hKC : x.appTop ≫ c.appTop = q.appTop := by
    rw [← Scheme.Hom.comp_appTop, hc]
  have hBC : φ.appTop ≫ j.appTop = q.appTop := by
    rw [← Scheme.Hom.comp_appTop, hj]
  have hAC : i.appTop ≫ j.appTop = c.appTop := by
    rw [← Scheme.Hom.comp_appTop, ha]
  haveI : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq' (by
    change φ.appTop.hom = i.appTop.hom.comp x.appTop.hom
    exact congrArg CommRingCat.Hom.hom hKB.symm)
  haveI : IsScalarTower K A C := IsScalarTower.of_algebraMap_eq' (by
    change q.appTop.hom = c.appTop.hom.comp x.appTop.hom
    exact congrArg CommRingCat.Hom.hom hKC.symm)
  haveI : IsScalarTower K B C := IsScalarTower.of_algebraMap_eq' (by
    change q.appTop.hom = j.appTop.hom.comp φ.appTop.hom
    exact congrArg CommRingCat.Hom.hom hBC.symm)
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' (by
    change c.appTop.hom = j.appTop.hom.comp i.appTop.hom
    exact congrArg CommRingCat.Hom.hom hAC.symm)
  have hsX : x.appTop.hom.Smooth :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp (inferInstance : Smooth x)
  have hsF : φ.appTop.hom.Smooth :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp (inferInstance : Smooth φ)
  haveI : Algebra.Smooth K A := hsX.toAlgebra
  haveI : Algebra.Smooth K B := hsF.toAlgebra
  have hAB : Function.Surjective (algebraMap A B) := i.app_surjective ⊤ (isAffineOpen_top X)
  have hAC' : Function.Surjective (algebraMap A C) := c.app_surjective ⊤ (isAffineOpen_top X)
  have hspec : Spec.map j.appTop ≫ Spec.map i.appTop = Spec.map c.appTop := by
    rw [← Spec.map_comp, ← Scheme.Hom.comp_appTop, ha]
  haveI : Mono (unionConormalFirst (Spec.map i.appTop) (Spec.map c.appTop)
      (Spec.map j.appTop) hspec) :=
    paired_c3_affine_conormal_first_mono (K := K) (A := A) (B := B) (C := C) hAB hAC' hspec
  let ea := unionConormalAffineSchemeFirstArrowIso i c j ha
  haveI : Mono ((Scheme.Modules.pullback Q.isoSpec.inv).map (unionConormalFirst i c j ha)) :=
    ((MorphismProperty.monomorphisms (Spec Γ(Q, ⊤)).Modules).arrow_mk_iso_iff ea).mpr inferInstance
  exact unionConormal_mono_of_iso_pullback Q.isoSpec.inv (unionConormalFirst i c j ha)

#print axioms paired_c3_affine_scheme_conormal_first_mono
end HodgeLean.Foundations.Program.G32Native
