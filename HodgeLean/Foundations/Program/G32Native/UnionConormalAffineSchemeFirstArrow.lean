import HodgeLean.Foundations.Program.G32Native.UnionConormalFirstArrowBaseChange
import HodgeLean.Foundations.AlgebraicGeometry.ConormalIsoComparison

/-! # The first affine scheme arrow under its spectrum identifications -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- Spectrum identifications transport the actual affine first arrow. -/
def unionConormalAffineSchemeFirstArrowIso
    {V T T₁ : Scheme.{0}} [IsAffine V] [IsAffine T] [IsAffine T₁]
    (t : T ⟶ V) (t₁ : T₁ ⟶ V) (a : T₁ ⟶ T) (ha : a ≫ t = t₁) :
    Arrow.mk ((Scheme.Modules.pullback T₁.isoSpec.inv).map
      (unionConormalFirst t t₁ a ha)) ≅
      Arrow.mk (unionConormalFirst (Spec.map t.appTop) (Spec.map t₁.appTop)
        (Spec.map a.appTop) (by rw [← Spec.map_comp, ← Scheme.Hom.comp_appTop, ha])) := by
  let h₀ := (Scheme.isoSpec_inv_naturality t).symm
  let h₁ := (Scheme.isoSpec_inv_naturality t₁).symm
  haveI := idealPullbackMap_isIso_of_isIso t (Spec.map t.appTop)
    V.isoSpec.inv T.isoSpec.inv h₀
  haveI := idealPullbackMap_isIso_of_isIso t₁ (Spec.map t₁.appTop)
    V.isoSpec.inv T₁.isoSpec.inv h₁
  exact unionConormalFirstArrowBaseChangeIso t t₁ a ha
    (Spec.map t.appTop) (Spec.map t₁.appTop) (Spec.map a.appTop)
    (by rw [← Spec.map_comp, ← Scheme.Hom.comp_appTop, ha]) V.isoSpec.inv
    T.isoSpec.inv T₁.isoSpec.inv h₀ h₁ (Scheme.isoSpec_inv_naturality a)

end HodgeLean.Foundations.Program.G32Native
