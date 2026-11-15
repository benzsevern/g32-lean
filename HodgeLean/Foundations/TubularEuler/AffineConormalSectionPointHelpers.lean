import HodgeLean.Foundations.TubularEuler.AffineConormalSectionFibreHelpers

/-! # Original affine conormal sections and their canonical point values

The point comparison retains the original ideal-module section and its actual pullback.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

theorem affineConormalSection_pointValue_eq
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ)
    (u : RingHom.ker φ.hom) :
    i1_module_pointValue (Conormal.sheaf (Spec.map φ))
      (affineConormalSection R S φ u) (Spec.map ψ) =
    i1_module_pointValue
      ((Scheme.Modules.pullback (Spec.map φ)).obj (Conormal.idealModule (Spec.map φ)))
      (i1_module_sectionPullback (Spec.map φ) (Conormal.idealModule (Spec.map φ))
        (affineIdealModuleSection R S φ u)) (Spec.map ψ) := by
  rfl

#print axioms affineConormalSection_pointValue_eq

end HodgeLean.Foundations.TubularEuler
