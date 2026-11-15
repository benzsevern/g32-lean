import HodgeLean.Foundations.Program.SchoenCycleC1InitialFreeHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1FreePointHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1DeckHelpers

/-! # Faithful powers of the retained initial generator -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The actual initial residual generator has no identity power with
positive exponent below the covering degree. -/
theorem s2e_c1_initial_generator_faithful_powers
    (S : g32p_Supplier) (Y Z W : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
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
    (hgenerator : q ≫ d = s2_action S Y a e N (s2_delta S N hN 1) 1 ≫ q) :
    ∀ n, n < S.m → End.of d ^ n = 1 → n = 0 := by
  obtain ⟨z, hfree⟩ := s2e_c1_exists_free_complex_point Y (S.H ⧸ S.χ.ker) a ha1 hamul hinj
  let x : ComplexPoint (g3_power Y N) := s2_lift N (fun _ => z)
  have hx (i : Fin N) : Point.map (g3_proj Y N i) x = z :=
    s2_check_lift_proj N (fun _ => z) i
  intro n hn hpow
  apply s2e_c1_initial_fixed_iterate_zero S Y Z W a e ha1 hamul p hp hporbit N hN q
    hqsurj hqinv hq d hgenerator x (fun i => by rw [hx i]; exact hfree) n hn
  rw [s2e_c1_point_map_power, hpow]
  rfl

end HodgeLean.Foundations.Program
