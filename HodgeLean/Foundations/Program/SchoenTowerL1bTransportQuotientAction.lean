import HodgeLean.Foundations.Program.SchoenTowerL1bKummerAction

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A field symmetry with the actual generic spectrum square is the actual function-field pullback. -/
theorem s2v_l1b_transport_symmetry_eq_pullback
    (W : Scheme.{0}) [IsIntegral W] (d : W ⟶ W) [IsDominant d]
    (τ : W.functionField →+* W.functionField)
    (hτ : Spec.map (CommRingCat.ofHom τ) ≫ W.fromSpecStalk (genericPoint W) =
      W.fromSpecStalk (genericPoint W) ≫ d) :
    CommRingCat.ofHom τ = s2v_l1b_functionFieldPullback d := by
  apply Spec.map_injective
  apply (cancel_mono (W.fromSpecStalk (genericPoint W))).mp
  rw [hτ, s2v_l1b_functionFieldPullback_generic_square]

/-- The original quotient square intertwines the retained field symmetry with actual covering pullback. -/
theorem s2v_l1b_transport_quotient_field_action
    {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W]
    (q : X ⟶ W) [IsDominant q]
    (g : X ⟶ X) [IsDominant g] (d : W ⟶ W) [IsDominant d]
    (hsquare : q ≫ d = g ≫ q)
    (τ : W.functionField →+* W.functionField)
    (hτ : Spec.map (CommRingCat.ofHom τ) ≫ W.fromSpecStalk (genericPoint W) =
      W.fromSpecStalk (genericPoint W) ≫ d) (t : W.functionField) :
    s2v_l1b_functionFieldPullback g (s2v_l1b_functionFieldPullback q t) =
      s2v_l1b_functionFieldPullback q (τ t) := by
  have he : s2v_l1b_functionFieldPullback q ≫ s2v_l1b_functionFieldPullback g =
      CommRingCat.ofHom τ ≫ s2v_l1b_functionFieldPullback q := by
    rw [s2v_l1b_transport_symmetry_eq_pullback W d τ hτ,
      ← s2v_l1b_functionFieldPullback_comp, ← s2v_l1b_functionFieldPullback_comp]
    congr 1
    exact hsquare.symm
  exact congrArg (fun h : W.functionField ⟶ X.functionField => h.hom t) he

/-- Pullback through the original quotient preserves the selected nonzero eigenfunction and its actual scalar. -/
theorem s2v_l1b_transport_quotient_eigenfunction
    {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W]
    (q : X ⟶ W) [IsDominant q]
    (g : X ⟶ X) [IsDominant g] (d : W ⟶ W) [IsDominant d]
    (hsquare : q ≫ d = g ≫ q)
    (τ : W.functionField →+* W.functionField)
    (hτ : Spec.map (CommRingCat.ofHom τ) ≫ W.fromSpecStalk (genericPoint W) =
      W.fromSpecStalk (genericPoint W) ≫ d)
    (t ξ : W.functionField) (ht : t ≠ 0) (heigen : τ t = ξ * t) :
    s2v_l1b_functionFieldPullback q t ≠ 0 ∧
      s2v_l1b_functionFieldPullback g (s2v_l1b_functionFieldPullback q t) =
        s2v_l1b_functionFieldPullback q ξ * s2v_l1b_functionFieldPullback q t := by
  refine ⟨?_, ?_⟩
  · simpa only [map_zero] using (s2v_l1b_functionFieldPullback q).hom.injective.ne ht
  · rw [s2v_l1b_transport_quotient_field_action q g d hsquare τ hτ, heigen, map_mul]

end HodgeLean.Foundations.Program
