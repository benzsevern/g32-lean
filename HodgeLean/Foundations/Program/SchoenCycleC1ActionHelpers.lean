import HodgeLean.Foundations.Program.SchoenCycleC1TupleHelpers
import HodgeLean.Foundations.Program.SchoenPowerComplexPoints

/-! # Translation sums for the retained curve action -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A retained coordinate action fixing a tuple with free curve coordinates
has zero translation sum. -/
theorem s2e_c1_fixed_action_sum_zero
    (S : g32p_Supplier) (Y Z : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (p : Y ⟶ Z) (hp : ∀ u, a u ≫ p = p)
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (N : ℕ) (x : ComplexPoint (g3_power Y N))
    (hfree : ∀ i : Fin N, Function.Injective (fun u =>
      Point.map (a u) (Point.map (g3_proj Y N i) x)))
    (c : Fin N → ZMod S.m) (τ : Equiv.Perm (Fin N))
    (hfix : Point.map (s2_action S Y a e N c τ) x = x) :
    ∑ i, c i = 0 := by
  letI : AddAction (ZMod S.m) (ComplexPoint Y) :=
    { vadd := fun g y => Point.map (a (e.symm (.ofAdd g))) y
      zero_vadd := by
        intro y
        change Point.map (a (e.symm 1)) y = y
        rw [map_one, ha1, Point.map_id]
      add_vadd := by
        intro u v y
        change Point.map (a (e.symm (.ofAdd (u + v)))) y =
          Point.map (a (e.symm (.ofAdd u))) (Point.map (a (e.symm (.ofAdd v))) y)
        rw [ofAdd_add, map_mul, hamul, Point.map_comp_apply] }
  refine s2e_c1_free_tuple_sum_zero (Point.map p) ?_ ?_
    (fun i => Point.map (g3_proj Y N i) x) ?_ τ c ?_
  · intro g y
    change (y ≫ a (e.symm (.ofAdd g))) ≫ p = y ≫ p
    rw [Category.assoc, hp]
  · intro y z hyz
    obtain ⟨u, hu⟩ := (hporbit y z).mp hyz
    refine ⟨(e u).toAdd, ?_⟩
    change Point.map (a (e.symm (.ofAdd (e u).toAdd))) y = z
    simpa only [ofAdd_toAdd, e.symm_apply_apply] using hu
  · intro i u v huv
    have he : e.symm (.ofAdd u) = e.symm (.ofAdd v) := hfree i huv
    exact Multiplicative.ofAdd.injective (e.symm.injective he)
  · intro i
    have he := s2_powerComplexPointEquiv_action S Y a e N c τ x i
    rw [hfix] at he
    exact he.symm

/-- The retained stabilizer criterion supplies a free curve orbit away from
all marked branch values. -/
theorem s2e_c1_curve_orbit_injective_off_marks
    (S : g32p_Supplier) (Y Z : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y)) (p : Y ⟶ Z)
    (T I : Type*) [MulAction (S.H ⧸ S.χ.ker) T]
    (eY : T ≃ ComplexPoint Y)
    (hpointAction : ∀ u z, Point.map (a u) (eY z) = eY (u • z))
    (b : I → ComplexPoint Z)
    (hbranch : ∀ z : T, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
      ∃ i, Point.map p (eY z) = b i)
    (z : T) (hz : ∀ i, Point.map p (eY z) ≠ b i) :
    Function.Injective (fun u => Point.map (a u) (eY z)) := by
  have hstab : MulAction.stabilizer (S.H ⧸ S.χ.ker) z = ⊥ := by
    by_contra hne
    obtain ⟨i, hi⟩ := (hbranch z).mp hne
    exact hz i hi
  intro u v huv
  have he : u • z = v • z := eY.injective (by
    rw [← hpointAction, ← hpointAction]
    exact huv)
  have hm : v⁻¹ * u ∈ MulAction.stabilizer (S.H ⧸ S.χ.ker) z := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, he, inv_smul_smul]
  have hunit : v⁻¹ * u = 1 := by
    simpa only [hstab, Subgroup.mem_bot] using hm
  calc
    u = v * (v⁻¹ * u) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    _ = v := by rw [hunit, mul_one]

end HodgeLean.Foundations.Program
