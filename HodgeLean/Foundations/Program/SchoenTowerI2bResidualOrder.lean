import HodgeLean.Foundations.Program.SchoenTowerI1b
import HodgeLean.Foundations.Program.SchoenTowerI2bFreePoint
import HodgeLean.Foundations.Program.SchoenTowerComplexPointsExist

/-! Exact periods of the specified residual generator.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A global period of the retained residual generator is divisible by the cyclic degree.
Source: the sum-kernel quotient, tested on a constant tuple at a free curve point. -/
theorem s2v_i2b_residual_period_dvd
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (h : ℕ) (hh : 0 < h) (q : g3_power Y h ⟶ W) (d : W ⟶ W)
    (hgenerator : q ≫ d = s2_action S Y a e h (s2_delta S h hh 1) 1 ≫ q)
    (hqorbits : ∀ x z : ComplexPoint (g3_power Y h),
      Point.map q x = Point.map q z ↔
        ∃ (v : Fin h → ZMod S.m) (τ : Equiv.Perm (Fin h)),
          (∑ t, v t = 0) ∧ Point.map (s2_action S Y a e h v τ) x = z)
    (y : ComplexPoint Y) (hy : Function.Injective (fun u => Point.map (a u) y))
    (n : ℕ) (hn : ∀ w : ComplexPoint W, (Point.map d)^[n] w = w) : S.m ∣ n := by
  let x : ComplexPoint (g3_power Y h) := s2_lift h (fun _ => y)
  let z := Point.map (s2_action S Y a e h (s2_delta S h hh n) 1) x
  have hqeq : Point.map q x = Point.map q z :=
    (hn (Point.map q x)).symm.trans
      (s2v_residual_generator_iterate S Y W a e ha1 hamul h hh q d hgenerator n x)
  obtain ⟨v, τ, hv, hact⟩ := (hqorbits x z).mp hqeq
  have hconst : ∀ (w : Fin h → ZMod S.m) (ρ : Equiv.Perm (Fin h)) (j : Fin h),
      (x ≫ s2_action S Y a e h w ρ) ≫ g3_proj Y h j =
        y ≫ a (e.symm (.ofAdd (w j))) := by
    intro w ρ j
    rw [Category.assoc, s2_action, s2_check_lift_proj, ← Category.assoc]
    change (s2_lift h (fun _ => y) ≫ g3_proj Y h (ρ.symm j)) ≫ _ = _
    rw [s2_check_lift_proj]
  have hcoords : ∀ j, v j = s2_delta S h hh (n : ZMod S.m) j := by
    intro j
    have hcoord := congrArg (Point.map (g3_proj Y h j)) hact
    change (x ≫ s2_action S Y a e h v τ) ≫ g3_proj Y h j =
      (x ≫ s2_action S Y a e h (s2_delta S h hh n) 1) ≫ g3_proj Y h j at hcoord
    rw [hconst, hconst] at hcoord
    have he := hy hcoord
    exact Multiplicative.ofAdd.injective (e.symm.injective he)
  have hsum : (n : ZMod S.m) = 0 := by
    calc
      (n : ZMod S.m) = ∑ j, s2_delta S h hh (n : ZMod S.m) j :=
        (s2_check_delta_sum S h hh n).symm
      _ = ∑ j, v j := Finset.sum_congr rfl (fun j _ => (hcoords j).symm)
      _ = 0 := hv
  exact (ZMod.natCast_eq_zero_iff n S.m).mp hsum

/-- The retained curve quotient has a complex point with injective orbit map.
Source: the finite branch-orbit description and the complex charts on the retained curve. -/
theorem s2v_i2b_free_curve_point
    {G A ι : Type} [Group G] [Finite G] [TopologicalSpace A] [ChartedSpace ℂ A]
    [MulAction G A] [Finite ι]
    (Y Z : Over (Spec ↧ℂ)) [Nonempty Y.left] [LocallyOfFiniteType Y.hom]
    (a : G → (Y ⟶ Y)) (p : Y ⟶ Z)
    (horbit : ∀ x z : ComplexPoint Y, Point.map p x = Point.map p z ↔
      ∃ g : G, Point.map (a g) x = z)
    (eY : A ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ g z, Point.map (a g) (eY z) = eY (g • z))
    (y : ι → A)
    (hbranch : ∀ z : A, MulAction.stabilizer G z ≠ ⊥ ↔
      ∃ t, Point.map p (eY z) = Point.map p (eY (y t))) :
    ∃ z : ComplexPoint Y, Function.Injective (fun g => Point.map (a g) z) := by
  haveI : Nonempty A := ⟨eY.symm (Classical.choice (s2t_nonempty_complexPoints Y))⟩
  haveI : Infinite A := s2v_i2b_charted_curve_infinite A
  have hquotient : ∀ z z' : A,
      Point.map p (eY z) = Point.map p (eY z') ↔ ∃ g : G, g • z = z' := by
    intro z z'
    rw [horbit]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, eY.injective ((hpointAction g z).symm.trans hg)⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, (hpointAction g z).trans (congrArg eY hg)⟩
  obtain ⟨z, hz⟩ := s2v_i2b_exists_free_point (fun z => Point.map p (eY z)) y
    hquotient hbranch
  refine ⟨eY z, ?_⟩
  intro g k he
  apply s2v_i2b_orbitMap_injective z hz
  apply eY.injective
  exact (hpointAction g z).symm.trans (he.trans (hpointAction k z))

end HodgeLean.Foundations.Program
