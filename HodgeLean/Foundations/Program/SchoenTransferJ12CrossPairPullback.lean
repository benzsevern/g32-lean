import HodgeLean.Foundations.Program.SchoenTransferJ12CrossMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Actual pair pullback of an external cross retains the target class and pulls back its source class.
Source: naturality of the actual cup and the two product projections. -/
theorem s4_selected_cross_pair_pullback
    (A Y T : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (f : T ⟶ Y) (p q m : ℕ) (h : p + q = m) (a : HQ A p) (b : HQ Y q) :
    homPullback (lift (fst A T) (snd A T ≫ f)) m
      (s4_selected_cross_map A Y p q m h (a ⊗ₜ[ℚ] b)) =
    (cupProductOf (A ⊗ T)).cup h
      (homPullback (fst A T) p a) (homPullback (snd A T) q (homPullback f q b)) := by
  rw [s4_selected_cross_map_tmul, spec_homPullback_cup]
  have h1 : homPullback (lift (fst A T) (snd A T ≫ f)) p
      (homPullback (fst A Y) p a) = homPullback (fst A T) p a := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_fst]
  have h2 : homPullback (lift (fst A T) (snd A T ≫ f)) q
      (homPullback (snd A Y) q b) = homPullback (snd A T) q (homPullback f q b) := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_snd,
      spec_homPullback_comp, LinearMap.comp_apply]
  rw [h1, h2]

#print axioms s4_selected_cross_pair_pullback
end HodgeLean.Foundations.Program
