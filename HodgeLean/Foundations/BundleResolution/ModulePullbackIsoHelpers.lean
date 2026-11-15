import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Pullback along an actual scheme isomorphism

The existing composition and identity isomorphisms give the inverse functor.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleResolution

theorem i1_modulePullback_iso_isEquivalence {X Y : Scheme.{0}} (e : X ≅ Y) :
    (Scheme.Modules.pullback e.hom).IsEquivalence := by
  let E := CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom) (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackId Y).symm ≪≫
      (Scheme.Modules.pullbackCongr e.inv_hom_id).symm ≪≫
      (Scheme.Modules.pullbackComp e.inv e.hom).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId X)
  exact (inferInstance : E.functor.IsEquivalence)

end HodgeLean.Foundations.BundleResolution
