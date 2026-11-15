import HodgeLean.Foundations.Program.SchoenCycleC1BranchSupportHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1InitialOrbitHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1InitialFreeHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1FibreOrbitHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1ActionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1TupleHelpers

/-! # The degree-sized initial fibres away from the actual branch supports -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The actual initial fibre over a point avoiding all marked branch supports
has exactly the covering degree many complex points. -/
theorem s2e_c1_initial_fibre_card_off_marks
    (S : g32p_Supplier) (Y Z W B : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (p : Y ⟶ Z) (hp : ∀ u, a u ≫ p = p)
    (hpsurj : Function.Surjective (Point.map p))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (T I : Type*) [MulAction (S.H ⧸ S.χ.ker) T]
    (eY : T ≃ ComplexPoint Y)
    (hpointAction : ∀ u z, Point.map (a u) (eY z) = eY (u • z))
    (marks : I → ComplexPoint Z)
    (hbranch : ∀ z : T, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
      ∃ i, Point.map p (eY z) = marks i)
    (h : ℕ) (hh : 0 < h + 1)
    (q : g3_power Y (h + 1) ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q = q)
    (hq : ∀ (A : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ A),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W ⟶ A, q ≫ u = f)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (A : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ A),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ A, γ ≫ u = f)
    (β : W ⟶ B) (hβ : q ≫ β = s2_powerMap p (h + 1) ≫ γ)
    (d : W ⟶ W) (hd : d ≫ β = β) (horder : End.of d ^ S.m = 1)
    (hgenerator : q ≫ d = s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q)
    (b : ComplexPoint B)
    (hb : ∀ i, b.underlying ∉ (s2c_branchIdeal Z B h γ (marks i)).support) :
    Nat.card ((Point.map β) ⁻¹' {b}) = S.m := by
  obtain ⟨v, hv⟩ := hγsurj b
  obtain ⟨x, hx⟩ := s2_powerMap_point_surjective p hpsurj (h + 1) v
  let z := Point.map q x
  have hz : Point.map β z = b := by
    change (x ≫ q) ≫ β = b
    rw [Category.assoc, hβ, ← Category.assoc]
    change Point.map γ (Point.map (s2_powerMap p (h + 1)) x) = b
    rw [hx, hv]
  have hfree (j : Fin (h + 1)) : Function.Injective (fun u =>
      Point.map (a u) (Point.map (g3_proj Y (h + 1) j) x)) := by
    let y := Point.map (g3_proj Y (h + 1) j) x
    have hav (i : I) : Point.map p y ≠ marks i := by
      intro hi
      apply hb i
      have hcoord : Point.map (g3_proj Z (h + 1) j) v = marks i := by
        have hc := s2_powerComplexPointEquiv_powerMap p (h + 1) x j
        change Point.map (g3_proj Z (h + 1) j) (Point.map (s2_powerMap p (h + 1)) x) = Point.map p y at hc
        rw [hx] at hc
        exact hc.trans hi
      have hm := s2e_c1_marked_coordinate_mem_branch_support Z B h γ hγinv (marks i) v j hcoord
      have hval : γ.left v.underlying = b.underlying := by
        simpa only [Point.underlying_map] using congrArg Point.underlying hv
      exact hval ▸ hm
    have ht := s2e_c1_curve_orbit_injective_off_marks S Y Z a p T I eY hpointAction
      marks hbranch (eY.symm y) (by simpa only [eY.apply_symm_apply] using hav)
    simpa only [eY.apply_symm_apply] using ht
  have hperiod : Function.IsPeriodicPt (Point.map d) S.m z := by
    change (Point.map d)^[S.m] z = z
    rw [s2e_c1_point_map_power, horder]
    rfl
  have hreturn (n : ℕ) (hn : n < S.m) (hnz : (Point.map d)^[n] z = z) : n = 0 :=
    s2e_c1_initial_fixed_iterate_zero S Y Z W a e ha1 hamul p hp hporbit
      (h + 1) hh q hqsurj hqinv hq d hgenerator x hfree n hn hnz
  have hi : Function.Injective (fun t : Fin S.m => Point.map (End.of d ^ t.val).asHom z) := by
    simpa only [s2e_c1_point_map_power] using
      s2e_c1_periodic_orbit_injective (Point.map d) z S.m (NeZero.pos S.m) hperiod hreturn
  have he : ∀ w : ComplexPoint W, Point.map β w = Point.map β z →
      ∃ t : Fin S.m, Point.map (End.of d ^ t.val).asHom z = w := by
    intro w hw
    obtain ⟨t, ht⟩ := s2e_c1_initial_fibre_exhaustion S Y Z W B a e ha1 hamul p hporbit
      (h + 1) hh q hqsurj hqinv γ hγsurj hγinv hγ β hβ d hgenerator z w hw.symm
    exact ⟨t, (s2e_c1_point_map_power d t.val z).symm.trans ht⟩
  have hcard := s2e_c1_deck_orbit_fibre_card β d hd S.m z hi he
  rwa [hz] at hcard

end HodgeLean.Foundations.Program
