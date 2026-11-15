import HodgeLean.Foundations.Program.SchoenCycleC1QuotientRationalDescent
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

/-- The curve eigenfunction coordinate product descends through the actual
retained mixed-action quotient using its original universal property. -/
theorem s2e_c1_retained_rational_product_descent
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
    (q : g3_power Y N ⟶ W) [IsFinite q.left] [Surjective q.left]
    (hqinv : ∀ v σ, ∑ i, v i = 0 → s2_action S Y a e N v σ ≫ q = q)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Y N ⟶ T),
      (∀ w σ, ∑ i, w i = 0 → s2_action S Y a e N w σ ≫ v = v) →
        ∃! u : W ⟶ T, q ≫ u = v) :
    let hg := s2e_c1_dominant_generic_point q.left
    let ψ := (eqToHom (congrArg W.left.presheaf.stalk hg.symm) ≫
      q.left.stalkMap (genericPoint (g3_power Y N).left)).hom
    ∃ z : W.left.functionField, ψ z = ∏ i, φ i f := by
  dsimp only
  let A := s2e_retainedAction S Y a e N
  obtain ⟨hA1, hAmul⟩ := s2e_retainedAction_laws S Y a e ha1 hamul N
  letI : ∀ g, IsIso (A g) := s2e_step1_action_isIso (g3_power Y N) (s2e_Retained S.m N)
    A hA1 hAmul
  apply s2e_c1_quotient_rational_descent (g3_power Y N) W (s2e_Retained S.m N) A q
    (fun g => hqinv g.vector g.perm g.zero_sum)
  · intro T v hv
    apply hq T v
    intro w σ hw
    exact hv ⟨w, hw, σ⟩
  · exact fun g => s2e_c1_retained_rational_product_invariant S Y a e ha1 hamul N φ hφ χ f heig g

end HodgeLean.Foundations.Program
