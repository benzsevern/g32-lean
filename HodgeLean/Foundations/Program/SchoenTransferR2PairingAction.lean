import HodgeLean.Foundations.Program.SchoenTransferE1TopAction
import HodgeLean.Foundations.Program.SchoenTransferR2ExceptionalRestriction
import HodgeLean.Foundations.Program.SchoenCyclePushDefs

/-! # Top action and invariant middle pairings

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Injective pullback descends the top action of a smooth projective cover.
Source: Hatcher, Algebraic Topology, Theorem 3.26 and naturality of cohomology.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_quotient_top_action
    (X W : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (q : X ⟶ W) (e : X ≅ X) (d : W ⟶ W)
    (he : e.hom ≫ q = q ≫ d)
    (hinj : Function.Injective (s2e_pullback ℚ q (2 * n))) :
    s2e_pullback ℚ d (2 * n) = LinearMap.id := by
  apply LinearMap.ext
  intro u
  apply hinj
  change s2e_pullback ℚ q (2 * n) (s2e_pullback ℚ d (2 * n) u) =
    s2e_pullback ℚ q (2 * n) u
  rw [← LinearMap.comp_apply, ← s4_assembly_pullback_comp, ← he,
    s4_assembly_pullback_comp, LinearMap.comp_apply]
  change cohomologyMap ℚ (2 * n) (TopCat.ofHom (Point.continuousMap e.hom))
    (s2e_pullback ℚ q (2 * n) u) = _
  rw [s4_e1_top_cohomology_action, LinearMap.id_apply]

#print axioms s4_assembly_quotient_top_action
/-- Identity in top degree makes every trace middle pairing invariant.
Source: Hatcher, Algebraic Topology, §3.2, naturality of the cup product.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_middle_pairing_invariant
    (W : Over (Spec ↧ℂ)) (d : W ⟶ W) (k : ℕ)
    (tr : Cohomology ℚ (TopCat.of (ComplexPoint W)) (2 * (2 * k)) →ₗ[ℚ] ℚ)
    (htop : s2e_pullback ℚ d (2 * (2 * k)) = LinearMap.id) :
    ∀ x y, s2e_middlePairing (TopCat.of (ComplexPoint W)) k tr
      (s2e_pullback ℚ d (2 * k) x) (s2e_pullback ℚ d (2 * k) y) =
        s2e_middlePairing (TopCat.of (ComplexPoint W)) k tr x y := by
  intro x y
  change tr (HodgeLean.Foundations.Singular.cup _ _ _ _) = tr _
  congr 1
  dsimp only [s2e_pullback]
  rw [← HodgeLean.Foundations.Singular.cohomologyMap_cup]
  change s2e_pullback ℚ d (2 * (2 * k)) _ = _
  rw [htop, LinearMap.id_apply]

#print axioms s4_assembly_middle_pairing_invariant
end HodgeLean.Foundations.Program
