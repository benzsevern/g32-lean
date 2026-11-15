import HodgeLean.Foundations.Program.SchoenTransferJ12PairMixedDivisor

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Pair pullback of the actual mixed divisor composes its source map.
Source: the actual mixed polarization pair pullback and composition of product maps. -/
theorem s4_selected_mixed_divisor_naturality
    (A Y T : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (f : T ⟶ Y) (g : Y ⟶ A) (pol : HQ A 2) :
    homPullback (lift (fst A T) (snd A T ≫ f)) 2
      (s4_selected_curve_mixed_divisor A Y g pol) =
    s4_selected_curve_mixed_divisor A T (f ≫ g) pol := by
  rw [← s4_selected_pair_mixed_divisor A Y g pol,
    ← LinearMap.comp_apply, ← spec_homPullback_comp]
  have hm : lift (fst A T) (snd A T ≫ f) ≫ lift (fst A Y) (snd A Y ≫ g) =
      lift (fst A T) (snd A T ≫ (f ≫ g)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp [Category.assoc]
  rw [hm, s4_selected_pair_mixed_divisor]

#print axioms s4_selected_mixed_divisor_naturality
end HodgeLean.Foundations.Program
