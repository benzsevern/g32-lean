import HodgeLean.Foundations.Program.SchoenTowerI1bTranslations
import HodgeLean.Foundations.Program.SchoenTowerI1bAlignment
import HodgeLean.Foundations.Program.SchoenCycleStep1

/-! # Residual fibre exhaustion without a tower index
The quotient argument also applies when the retained tower has length zero.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The curve quotient, symmetric quotient and sum-kernel invariance give
residual orbit exhaustion before any modification of the base. -/
theorem s2e_c1_initial_fibre_exhaustion
    (S : g32p_Supplier) (Y Z W B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (p : Y ⟶ Z)
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (N : ℕ) (hN : 0 < N)
    (q : g3_power Y N ⟶ W) (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin N → ZMod S.m) (τ : Equiv.Perm (Fin N)),
      ∑ t, v t = 0 → s2_action S Y a e N v τ ≫ q = q)
    (γ : g3_power Z N ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z N τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z N ⟶ T),
      (∀ τ, s2_permute Z N τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (β : W ⟶ B) (hβ : q ≫ β = s2_powerMap p N ≫ γ)
    (d : W ⟶ W)
    (hgenerator : q ≫ d = s2_action S Y a e N (s2_delta S N hN 1) 1 ≫ q)
    (x y : ComplexPoint W) (hxy : Point.map β x = Point.map β y) :
    ∃ n : Fin S.m, (Point.map d)^[n.val] x = y := by
  obtain ⟨u, rfl⟩ := hqsurj x
  obtain ⟨v, rfl⟩ := hqsurj y
  have hp : Point.map γ (Point.map (s2_powerMap p N) u) =
      Point.map γ (Point.map (s2_powerMap p N) v) := by
    simpa only [Point.map, Category.assoc, hβ] using hxy
  obtain ⟨τ, hτ⟩ := s2e_step1_retained_symmetric_orbits Z B N γ hγsurj hγinv hγ _ _ hp
  obtain ⟨c, hc⟩ := s2v_i1b_align_points S Y Z a e p hporbit N u v τ hτ
  let t : ZMod S.m := ∑ j, c j
  refine ⟨⟨t.val, ZMod.val_lt t⟩, ?_⟩
  rw [s2v_residual_generator_iterate S Y W a e ha1 hamul N hN q d hgenerator]
  have he := s2v_action_quotient_delta_sum S Y W a e ha1 hamul N hN q hqinv c τ
  have ht : (t.val : ZMod S.m) = ∑ j, c j := ZMod.natCast_zmod_val t
  rw [ht]
  calc
    Point.map q (Point.map (s2_action S Y a e N
        (s2_delta S N hN (∑ j, c j)) 1) u) =
        Point.map q (Point.map (s2_action S Y a e N c τ) u) := by
      exact (congrArg (fun f => u ≫ f) he).symm
    _ = Point.map q v := congrArg (Point.map q) hc

end HodgeLean.Foundations.Program
