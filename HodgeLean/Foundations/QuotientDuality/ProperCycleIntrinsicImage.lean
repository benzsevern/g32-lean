import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs

/-! # Actual singular images of intrinsic component classes

HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Push a supplied intrinsic class by the literal complex-point map. The component construction applies this to its reduced closed immersion.
Source: Fulton, Intersection Theory, section 19.1; Hatcher, Algebraic Topology, section 2.1.
HC no distance; AV milestone no distance. -/
def properCycle_intrinsic_image {V X : Over (Spec ↧ℂ)} (j : V ⟶ X) (d : ℕ)
    (c : Homology ℚ (a3b4_an V.hom) (2 * d)) : Homology ℚ (a3b4_an X.hom) (2 * d) :=
  homologyMap ℚ (2 * d) (TopCat.ofHom (Point.continuousMap j)) c

/-- The actual identity immersion retains the supplied intrinsic class.
Source: Hatcher, Algebraic Topology, section 2.1, functorial singular homology.
HC no distance; AV milestone no distance. -/
theorem properCycle_intrinsic_image_id (V : Over (Spec ↧ℂ)) (d : ℕ)
    (c : Homology ℚ (a3b4_an V.hom) (2 * d)) :
    properCycle_intrinsic_image (𝟙 V) d c = c := by
  have h : TopCat.ofHom (Point.continuousMap (𝟙 V)) = 𝟙 (a3b4_an V.hom) := by
    ext z : 1
    rfl
  unfold properCycle_intrinsic_image
  rw [h]
  exact LinearMap.congr_fun (homologyMap_id ℚ (a3b4_an V.hom) (2 * d)) c

example (V : Over (Spec ↧ℂ)) (d : ℕ) (c : Homology ℚ (a3b4_an V.hom) (2 * d)) :
    properCycle_intrinsic_image (𝟙 V) d c = c := properCycle_intrinsic_image_id V d c

end HodgeLean.Foundations.QuotientDuality
