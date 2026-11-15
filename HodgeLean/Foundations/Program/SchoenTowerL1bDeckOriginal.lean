import HodgeLean.Foundations.Program.SchoenTowerL1bDeckPowers
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerSumZeroOrbits
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerResidualOrder

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The retained residual generator gives an original generic-field symmetry of full order. -/
theorem s2v_l1b_original_deck_field_symmetry
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral W.left] [IsSeparated W.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (n : ℕ) (hn : 0 < n) [IsProjective (g3_power Y n).hom]
    (q : g3_power Y n ⟶ W) (d : W ⟶ W) [IsIso d]
    (hinv : ∀ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
      ∑ j, v j = 0 → s2_action S Y a e n v τ ≫ q = q)
    (hcat : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y n ⟶ T),
      (∀ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
        ∑ j, v j = 0 → s2_action S Y a e n v τ ≫ f = f) →
      ∃! u : W ⟶ T, q ≫ u = f)
    (hgen : q ≫ d = s2_action S Y a e n (s2_delta S n hn 1) 1 ≫ q) :
    ∃ φ : W.left.functionField ≃+* W.left.functionField,
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        W.left.fromSpecStalk (genericPoint W.left) =
        W.left.fromSpecStalk (genericPoint W.left) ≫ d.left) ∧
      orderOf φ = S.m := by
  haveI : Epi q := by
    constructor
    intro T f g hfg
    have hi : ∀ v τ, ∑ j, v j = 0 →
        s2_action S Y a e n v τ ≫ (q ≫ f) = q ≫ f := by
      intro v τ hv
      rw [← Category.assoc, hinv v τ hv]
    exact (hcat T (q ≫ f) hi).unique rfl hfg.symm
  have horbits := s2v_l1b_sum_zero_point_orbits S Y W a e ha1 hamul n q hinv hcat
  have hord := s2v_l1b_residual_order_of_orbits S Y W a e ha1 hamul hinj
    n hn q d hgen horbits (by have := S.three_le; omega)
  haveI := s2v_l1b_functionFieldPullback_isIso d.left
  let φ := (asIso (s2v_l1b_functionFieldPullback d.left)).commRingCatIsoToRingEquiv
  have hφ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      W.left.fromSpecStalk (genericPoint W.left) =
      W.left.fromSpecStalk (genericPoint W.left) ≫ d.left :=
    s2v_l1b_functionFieldPullback_generic_square d.left
  have hforget : orderOf (End.of d.left) = orderOf (End.of d) := by
    apply orderOf_injective ((Over.forget _).mapEnd W) _ (End.of d)
    intro u v huv
    apply End.ext
    apply Over.OverMorphism.ext
    exact congrArg End.asHom huv
  exact ⟨φ, hφ, (s2v_l1b_deck_generic_order W.left _ W.hom d.left (Over.w d) φ hφ).trans
    (hforget.trans hord)⟩

end HodgeLean.Foundations.Program
