import HodgeLean.Foundations.Program.SchoenCycleC1MixedRationalProductCharacter
import HodgeLean.Foundations.Program.SchoenCycleC1RationalDeckEigenvalueDescent
import HodgeLean.Foundations.Program.SchoenCycleC1RetainedRationalProduct
import HodgeLean.Foundations.Program.SchoenCycleC1LocalSquareComposition
import HodgeLean.Foundations.Program.SchoenCycleC1RationalPullbackScalars
import HodgeLean.Foundations.Program.SchoenCycleRetainedAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The descended coordinate product has the prescribed primitive-generator
eigenvalue for the actual retained residual deck morphism. -/
theorem s2e_c1_descended_product_eigencharacter
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] [IsIntegral W.left]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (N : ℕ) (φ : Fin N → (Y.left.functionField →+* (g3_power Y N).left.functionField))
    (hφ : ∀ i (p : (g3_power Y N).left) (r : Y.left.presheaf.stalk ((g3_proj Y N i).left p)),
      φ i (algebraMap (Y.left.presheaf.stalk ((g3_proj Y N i).left p)) Y.left.functionField r) =
        algebraMap ((g3_power Y N).left.presheaf.stalk p) (g3_power Y N).left.functionField
          (((g3_proj Y N i).left.stalkMap p).hom r))
    (χ : Multiplicative (ZMod S.m) →* ℂˣ) (f : Y.left.functionField)
    (heig : ∀ t : ZMod S.m,
      letI := s2e_step1_action_isIso Y (S.H ⧸ S.χ.ker) a ha1 hamul (e.symm (.ofAdd t))
      s2e_step1_fieldPullback Y.left (a (e.symm (.ofAdd t))).left f =
        HodgeLean.Foundations.Curves.stalkC (genericPoint Y.left) (χ (.ofAdd t) : ℂ) * f)
    (hN : 0 < N) (q : g3_power Y N ⟶ W) (d : W ⟶ W) [IsIso d]
    (hgen : q ≫ d = s2_action S Y a e N (s2_delta S N hN 1) 1 ≫ q)
    (qstar : W.left.functionField →+* (g3_power Y N).left.functionField)
    (hqstar : ∀ x (r : W.left.presheaf.stalk (q.left x)),
      qstar (algebraMap (W.left.presheaf.stalk (q.left x)) W.left.functionField r) =
        algebraMap ((g3_power Y N).left.presheaf.stalk x) (g3_power Y N).left.functionField
          ((q.left.stalkMap x).hom r))
    (z : W.left.functionField) (hz : qstar z = ∏ i, φ i f) :
    s2e_step1_fieldPullback W.left d.left z =
      HodgeLean.Foundations.Curves.stalkC (genericPoint W.left) (χ (.ofAdd 1) : ℂ) * z := by
  let A := s2_action S Y a e N (s2_delta S N hN 1) 1
  letI : IsIso A := s2e_c1_mixed_action_isIso S Y a e ha1 hamul N (s2_delta S N hN 1) 1
  apply s2e_c1_rational_deck_eigenvalue_descent (g3_power Y N) W q A d hgen qstar hqstar z
  rw [hz]
  have he := s2e_c1_mixed_rational_product_character S Y a e ha1 hamul N φ hφ χ f heig
    (s2_delta S N hN 1) 1
  simpa only [s2_check_delta_sum] using he

end HodgeLean.Foundations.Program
