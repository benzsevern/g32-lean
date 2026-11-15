import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual coefficient map on global sections induced by a scheme morphism to a coefficient spectrum. -/
def s2_affineCoefficientMap {K : Type} [CommRing K] (X : Scheme.{0})
    (s : X ⟶ Spec (.of K)) : K →+* Γ(X, ⊤) :=
  s.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom

/-- The actual coefficient map recovers the structure morphism under the affine spectrum presentation. -/
theorem s2_affineCoefficientMap_over {K : Type} [CommRing K] (X : Scheme.{0}) [IsAffine X]
    (s : X ⟶ Spec (.of K)) :
    s = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (s2_affineCoefficientMap X s)) := by
  change s = X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (.of K)).inv ≫ s.appTop)
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
    Category.assoc, ← Scheme.isoSpec_Spec_inv, Iso.hom_inv_id, Category.comp_id]

/-- A finite-type affine structure morphism gives finite type for its actual coefficient map on global sections. -/
theorem s2_affineCoefficientMap_finiteType {K : Type} [CommRing K] (X : Scheme.{0})
    [IsAffine X] (s : X ⟶ Spec (.of K)) [LocallyOfFiniteType s] :
    (s2_affineCoefficientMap X s).FiniteType := by
  have hf : s.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := s)).mp inferInstance
  have hi : (Scheme.ΓSpecIso (.of K)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective
  exact hf.comp hi

end HodgeLean.Foundations.Program
