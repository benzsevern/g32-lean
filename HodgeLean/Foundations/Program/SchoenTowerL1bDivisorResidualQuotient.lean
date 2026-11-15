import HodgeLean.Foundations.Program.SchoenTowerL1bKummerFullQuotient
import HodgeLean.Foundations.Program.SchoenTowerL1bDeckOriginal

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The retained square presents the residual cover as a categorical quotient by its generator. -/
theorem s2v_l1b_divisor_residual_quotient
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
    (hqinv : ∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
      ∑ j, v j = 0 → s2_action S Y a e n v σ ≫ q = q)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y n ⟶ T),
      (∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
        ∑ j, v j = 0 → s2_action S Y a e n v σ ≫ f = f) →
      ∃! b : W ⟶ T, q ≫ b = f)
    (γ : g3_power Z n ⟶ B) (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ f = f) → ∃! b : B ⟶ T, γ ≫ b = f)
    (β : W ⟶ B) [IsFinite β.left] (hβ : q ≫ β = s2_powerMap p n ≫ γ)
    (d : W ⟶ W) (hgen : q ≫ d = s2_action S Y a e n (s2_delta S n hn 1) 1 ≫ q) :
    IsIso d ∧ ∀ (T : Over (Spec ↧ℂ)) (f : W ⟶ T),
      d ≫ f = f → ∃! b : B ⟶ T, β ≫ b = f := by
  letI : Epi q := by
    constructor
    intro T f g hfg
    have hi : ∀ v σ, ∑ j, v j = 0 → s2_action S Y a e n v σ ≫ (q ≫ f) = q ≫ f := by
      intro v σ hv
      rw [← Category.assoc, hqinv v σ hv]
    exact (hq T (q ≫ f) hi).unique rfl hfg.symm
  letI : IsFinite (q ≫ β).left := by
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
  exact ⟨(isUnit_iff_isIso (End.of d)).mp
    (IsUnit.of_pow_eq_one hdPow (NeZero.ne S.m)), hcat⟩

end HodgeLean.Foundations.Program
