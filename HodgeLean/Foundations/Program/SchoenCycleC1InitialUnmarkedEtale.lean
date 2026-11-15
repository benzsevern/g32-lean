import HodgeLean.Foundations.Program.SchoenCycleC1InitialMeasuredFibres
import HodgeLean.Foundations.Program.SchoenCycleC1InitialUnmarkedFree
import HodgeLean.Foundations.Program.SchoenCycleC1InitialFaithfulHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1CyclicMeasuredEtale

/-! # Actual initial quotient etaleness away from the marked branch supports -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The retained initial quotient cover is etale over every base open
avoiding the marked branch supports, including its collision points. -/
theorem s2e_c1_initial_etale_over_unmarked_open
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
    (T I : Type*) [Finite I] [MulAction (S.H ⧸ S.χ.ker) T]
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
    (β : W ⟶ B) [IsFinite β.left] (hβ : q ≫ β = s2_powerMap p (h + 1) ≫ γ)
    (d : W ⟶ W) (hd : d ≫ β = β) (horder : End.of d ^ S.m = 1)
    (hgenerator : q ≫ d = s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q)
    (U : B.left.Opens)
    (hU : ∀ i, ∀ b ∈ U, b ∉ (s2c_branchIdeal Z B h γ (marks i)).support) :
    Etale (β.left ∣_ U) := by
  have hsurj : Function.Surjective (Point.map β) := by
    intro b
    obtain ⟨v, hv⟩ := hγsurj b
    obtain ⟨x, hx⟩ := s2_powerMap_point_surjective p hpsurj (h + 1) v
    refine ⟨Point.map q x, ?_⟩
    rw [← Point.map_comp_apply, hβ, Point.map_comp_apply, hx, hv]
  haveI : Surjective β.left :=
    s2e_step1_surjective_of_complexPoint_surjective W B β hsurj
  apply s2e_c1_cyclic_measured_etale_over_free_open W B β d hd S.m (NeZero.pos S.m) horder
  · exact s2e_c1_initial_generator_faithful_powers S Y Z W a e ha1 hamul hinj
      p hp hporbit (h + 1) hh q hqsurj hqinv hq d hgenerator
  · exact s2e_c1_initial_measured_fibres S Y Z W B a e ha1 hamul hinj p hp hpsurj hporbit
      T I eY hpointAction marks hbranch h hh q hqsurj hqinv hq γ hγsurj hγinv hγ
      β hβ d hd horder hgenerator
  · intro w hw n hn hfix
    apply s2e_c1_initial_free_off_marks S Y Z W B a e ha1 hamul p hp hporbit
      T I eY hpointAction marks hbranch h hh q hqsurj hqinv hq γ hγinv β hβ d hgenerator
      w _ n hn hfix
    intro i
    rw [Point.underlying_map]
    exact hU i _ hw

end HodgeLean.Foundations.Program
