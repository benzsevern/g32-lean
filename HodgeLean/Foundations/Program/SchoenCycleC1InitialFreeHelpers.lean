import HodgeLean.Foundations.Program.SchoenCycleC1ActionHelpers
import HodgeLean.Foundations.Program.SchoenTowerI1bTranslations
import HodgeLean.Foundations.Program.SchoenSumZeroActionFinite
import HodgeLean.Foundations.Program.SchoenCycleStep1

/-! # Freeness from the actual sum-kernel quotient -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A residual generator iterate fixing the quotient of a tuple with free
coordinates has exponent zero when its exponent is below the covering degree. -/
theorem s2e_c1_initial_fixed_iterate_zero
    (S : g32p_Supplier) (Y Z W : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (p : Y ⟶ Z) (hp : ∀ u, a u ≫ p = p)
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (N : ℕ) (hN : 0 < N)
    (q : g3_power Y N ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin N → ZMod S.m) (τ : Equiv.Perm (Fin N)),
      ∑ t, v t = 0 → s2_action S Y a e N v τ ≫ q = q)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y N ⟶ T),
      (∀ (v : Fin N → ZMod S.m) (τ : Equiv.Perm (Fin N)),
        ∑ t, v t = 0 → s2_action S Y a e N v τ ≫ f = f) →
      ∃! u : W ⟶ T, q ≫ u = f)
    (d : W ⟶ W)
    (hgenerator : q ≫ d = s2_action S Y a e N (s2_delta S N hN 1) 1 ≫ q)
    (x : ComplexPoint (g3_power Y N))
    (hfree : ∀ i : Fin N, Function.Injective (fun u =>
      Point.map (a u) (Point.map (g3_proj Y N i) x)))
    (n : ℕ) (hn : n < S.m)
    (hfix : (Point.map d)^[n] (Point.map q x) = Point.map q x) : n = 0 := by
  let G := s2_sumZeroActionGroup S Y a e ha1 hamul N
  letI : Finite G := s2_sumZeroActionGroup_finite S Y a e ha1 hamul N
  let A : G → (g3_power Y N ⟶ g3_power Y N) := fun g => g.val.asIso.hom
  have hA1 : A 1 = 𝟙 _ := rfl
  have hAmul : ∀ u v, A (u * v) = A v ≫ A u := fun _ _ => rfl
  have hAinv : ∀ g, A g ≫ q = q := by
    intro g
    obtain ⟨v, τ, hv, hg⟩ := g.property
    change g.val.asIso.hom ≫ q = q
    rw [hg]
    exact hqinv v τ hv
  have hAquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y N ⟶ T),
      (∀ g, A g ≫ f = f) → ∃! u : W ⟶ T, q ≫ u = f := by
    intro T f hf
    apply hq T f
    intro v τ hv
    let g : G := ⟨Aut.of (s2_coordinateActionIso S Y a e ha1 hamul N v τ),
      v, τ, hv, rfl⟩
    exact hf g
  haveI : Surjective q.left :=
    s2e_step1_surjective_of_complexPoint_surjective _ _ q hqsurj
  rw [s2v_residual_generator_iterate S Y W a e ha1 hamul N hN q d hgenerator] at hfix
  obtain ⟨g, hgfix⟩ := s2e_step1_finite_quotient_point_orbits
    (g3_power Y N) W G A hA1 hAmul q hAinv hAquot _ _ hfix
  obtain ⟨v, τ, hv, hg⟩ := g.property
  change Point.map g.val.asIso.hom _ = x at hgfix
  rw [hg] at hgfix
  have hcomp := (s2_coordinateAction_laws S Y a e ha1 hamul N).2
    (s2_delta S N hN n) v 1 τ
  rw [mul_one] at hcomp
  have he : Point.map (s2_action S Y a e N
      (fun i => v i + s2_delta S N hN n (τ.symm i)) τ) x = x := by
    rw [← hcomp, Point.map_comp_apply]
    exact hgfix
  have hs := s2e_c1_fixed_action_sum_zero S Y Z a e ha1 hamul p hp hporbit N x hfree _ τ he
  rw [Finset.sum_add_distrib, hv, zero_add, Equiv.sum_comp τ.symm,
    s2_check_delta_sum] at hs
  exact Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff n S.m).mp hs) hn

end HodgeLean.Foundations.Program
