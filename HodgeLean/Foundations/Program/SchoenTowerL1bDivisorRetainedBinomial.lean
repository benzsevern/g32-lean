import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorBinomialDescent
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerFullQuotient
import HodgeLean.Foundations.Program.SchoenTowerL1bDeckOriginal
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerInitial

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The retained original quotient square gives the base coefficient of a character power. -/
theorem s2v_l1b_divisor_retained_binomial
    (S : g32p_Supplier) (Y Z W B : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p : Y ⟶ Z) (hp : ∀ u, a u ≫ p = p)
    (hpsurj : Function.Surjective (Point.map p))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (n : ℕ) (hn : 0 < n)
    (q : g3_power Y n ⟶ W) [IsFinite q.left]
    (hqinv : ∀ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
      ∑ j, v j = 0 → s2_action S Y a e n v τ ≫ q = q)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y n ⟶ T),
      (∀ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
        ∑ j, v j = 0 → s2_action S Y a e n v τ ≫ f = f) →
      ∃! u : W ⟶ T, q ≫ u = f)
    (γ : g3_power Z n ⟶ B) (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z n τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z n ⟶ T),
      (∀ τ, s2_permute Z n τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (β : W ⟶ B) [IsFinite β.left]
    (hβ : q ≫ β = s2_powerMap p n ≫ γ)
    (d : W ⟶ W) (hd : d ≫ β = β)
    (hgen : q ≫ d = s2_action S Y a e n (s2_delta S n hn 1) 1 ≫ q)
    (κ : B.left.functionField ⟶ W.left.functionField)
    (hκ : Spec.map κ ≫ B.left.fromSpecStalk (genericPoint B.left) =
      W.left.fromSpecStalk (genericPoint W.left) ≫ β.left)
    (τ : W.left.functionField ≃+* W.left.functionField)
    (hτ : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      W.left.fromSpecStalk (genericPoint W.left) =
      W.left.fromSpecStalk (genericPoint W.left) ≫ d.left)
    (t ξ : W.left.functionField) (hξ : ξ ^ S.m = 1) (htξ : τ t = ξ * t) :
    ∃ v : B.left.functionField, t ^ S.m = κ.hom v := by
  haveI : IsDominant β.left := n1bc_dominant_of_points_surjective β
    (n1bc_originalCover_points_surjective p hpsurj n q γ hγsurj β hβ)
  have hκeq : κ = s2v_l1b_functionFieldPullback β.left := by
    apply Spec.map_injective
    apply (cancel_mono (B.left.fromSpecStalk (genericPoint B.left))).mp
    rw [hκ, s2v_l1b_functionFieldPullback_generic_square]
  haveI : Epi q := by
    constructor
    intro T f g hfg
    have hi : ∀ v τ, ∑ j, v j = 0 → s2_action S Y a e n v τ ≫ (q ≫ f) = q ≫ f := by
      intro v τ hv
      rw [← Category.assoc, hqinv v τ hv]
    exact (hq T (q ≫ f) hi).unique rfl hfg.symm
  haveI : IsFinite (q ≫ β).left := by
    change IsFinite (q.left ≫ β.left)
    infer_instance
  have hfull := s2v_l1b_full_coordinate_categorical_quotient S Y Z B a e ha1 hamul
    p hp hpsurj hporbit n γ hγsurj hγinv hγ (q ≫ β) hβ
  have hcat := s2v_l1b_residual_categorical_quotient S Y W B a e ha1 hamul
    n hn q β d hqinv hgen hfull
  have horbits := s2v_l1b_sum_zero_point_orbits S Y W a e ha1 hamul n q hqinv hq
  have hord := s2v_l1b_residual_order_of_orbits S Y W a e ha1 hamul hinj
    n hn q d hgen horbits (by have := S.three_le; omega)
  have hdPow : End.of d ^ S.m = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  haveI : IsIso d := (isUnit_iff_isIso (End.of d)).mp
    (IsUnit.of_pow_eq_one hdPow (NeZero.ne S.m))
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := genericPoint B.left) (U := ⊤) trivial
  letI : Nonempty U := ⟨⟨genericPoint B.left, hxU⟩⟩
  obtain ⟨v, hv⟩ := s2v_l1b_divisor_generator_binomial W B β d hd hcat ⟨U, hU⟩
    τ hτ t ξ S.m hξ htξ
  exact ⟨v, by rw [hκeq]; exact hv.symm⟩

end HodgeLean.Foundations.Program
