import HodgeLean.Foundations.Program.SchoenCycleNilpotentCurvePoints

/-! # Naturality of actual morphisms defined by stalk maps -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Composing an actual stalk-defined morphism with a scheme morphism composes
the specified local ring maps in the opposite direction.
Source: Hartshorne, Algebraic Geometry, II.2, functoriality of spectra and stalks. -/
theorem s2e_stalkMap_to_base_morphism_comp
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) (x : X.left) (A : Type) [CommRing A] [Algebra ℂ A]
    (l : X.left.presheaf.stalk x →+* A)
    (hl : ∀ c, l (HodgeLean.Foundations.Curves.stalkC x c) = algebraMap ℂ A c)
    (hc : ∀ c, (l.comp (f.left.stalkMap x).hom)
      (HodgeLean.Foundations.Curves.stalkC (f.left x) c) = algebraMap ℂ A c) :
    s2e_stalkMap_to_base_morphism X x A l hl ≫ f =
      s2e_stalkMap_to_base_morphism Y (f.left x) A (l.comp (f.left.stalkMap x).hom) hc := by
  apply Over.OverMorphism.ext
  change (Spec.map (CommRingCat.ofHom l) ≫ X.left.fromSpecStalk x) ≫ f.left =
    Spec.map (CommRingCat.ofHom (l.comp (f.left.stalkMap x).hom)) ≫
      Y.left.fromSpecStalk (f.left x)
  rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
    ← Category.assoc, ← Spec.map_comp]
  rfl

end HodgeLean.Foundations.Program
