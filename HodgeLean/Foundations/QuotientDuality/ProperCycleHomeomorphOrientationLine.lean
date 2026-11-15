import HodgeLean.Foundations.QuotientDuality.ProperCycleHomeomorphPointPair
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodCapNaturality

/-! # Specified actual ambient orientation lines under homeomorphisms
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original homology image through an actual homeomorphism retains bijectivity of the specified point orientation line.
Source: properCycle_relative_homology_projection_naturality; properCycle_homeomorph_point_pair_bijective.
HC no distance; AV milestone no distance. -/
lemma properCycle_homeomorph_orientation_line_bijective
    (X Y : TopCat.{0}) [T1Space Y] (e : X ≃ₜ Y) (n : ℕ)
    (c : Homology ℚ X n) (x : X) (hc : Function.Bijective (orientationLine X n c x)) :
    Function.Bijective (orientationLine Y n
      (homologyMap ℚ n (TopCat.ofHom ⟨e, e.continuous⟩) c) (e x)) := by
  let f := properCycle_homeomorph_point_pair X Y e x (e x) rfl
  let F := relativeHomologyMap ℚ n f
  have hF := properCycle_homeomorph_point_pair_bijective X Y e x (e x) rfl n
  have hn := properCycle_relative_homology_projection_naturality f n c
  change F (localOrientation X n c x) = localOrientation Y n
    (homologyMap ℚ n (TopCat.ofHom ⟨e, e.continuous⟩) c) (e x) at hn
  have hline : (orientationLine Y n
      (homologyMap ℚ n (TopCat.ofHom ⟨e, e.continuous⟩) c) (e x) : ℚ → _) =
      F ∘ orientationLine X n c x := by
    funext q
    change q • localOrientation Y n _ (e x) = F (q • localOrientation X n c x)
    rw [map_smul, hn]
  rw [hline]
  exact hF.comp hc

end HodgeLean.Foundations.QuotientDuality
