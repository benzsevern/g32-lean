import HodgeLean.Foundations.Curves.CurvePoints

/-! # Scalars in maps between actual scheme stalks -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Stalk pullback along a morphism over the complex base preserves the actual
complex scalar maps.
Source: Hartshorne, Algebraic Geometry, II.2, morphisms of locally ringed spaces. -/
theorem s2e_stalkMap_complex_scalars
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) (x : X.left) (c : ℂ) :
    (f.left.stalkMap x).hom (HodgeLean.Foundations.Curves.stalkC (f.left x) c) =
      HodgeLean.Foundations.Curves.stalkC x c := by
  have he : CommRingCat.ofHom (HodgeLean.Foundations.Curves.stalkC (f.left x)) ≫
      f.left.stalkMap x = CommRingCat.ofHom (HodgeLean.Foundations.Curves.stalkC x) := by
    apply Spec.map_injective
    rw [Spec.map_comp,
      ← HodgeLean.Foundations.Curves.fromSpecStalk_comp_hom' (f.left x),
      ← Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Category.assoc, Over.w f,
      HodgeLean.Foundations.Curves.fromSpecStalk_comp_hom']
  exact congrArg (fun k : CommRingCat.of ℂ ⟶ X.left.presheaf.stalk x => k.hom c) he

end HodgeLean.Foundations.Program
