import HodgeLean.Foundations.Program.SchoenTowerI1bTranslations

/-! # Residual translations detected on diagonal tuples
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Equal translations of one point remain equal after summing their exponents.
Source: The composition law of a commutative group action. -/
theorem s2v_i2a_translation_sum_eq
    {A C I : Type*} [AddCommMonoid A]
    (f : A → C → C) (hadd : ∀ a b z, f (a + b) z = f a (f b z))
    (s : Finset I) (v w : I → A) (y : C)
    (h : ∀ i ∈ s, f (v i) y = f (w i) y) :
    f (∑ i ∈ s, v i) y = f (∑ i ∈ s, w i) y := by
  classical
  have hcomm (a b : A) (z : C) : f a (f b z) = f b (f a z) := by
    rw [← hadd, add_comm, hadd]
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]
  | @insert i s hi ih =>
    have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, hadd, hs,
      hcomm, h i (Finset.mem_insert_self i s), hcomm]

/-- A residual translation fixing the quotient of a diagonal tuple fixes its curve point.
Source: Schoen (1988), section 1, the sum-kernel quotient, and the retained I1a orbit description. -/
theorem s2v_i2a_diagonal_translation_fixed
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ) (hn : 0 < n) (q : g3_power Y n ⟶ W)
    (hq : ∀ x z : ComplexPoint (g3_power Y n),
      Point.map q x = Point.map q z →
        ∃ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
          (∑ i, v i = 0) ∧ Point.map (s2_action S Y a e n v τ) x = z)
    (y : ComplexPoint Y) (t : ZMod S.m)
    (ht : Point.map q (Point.map (s2_action S Y a e n (s2_delta S n hn t) 1)
      (s2_lift n (fun _ => y))) = Point.map q (s2_lift n (fun _ => y))) :
    Point.map (a (e.symm (.ofAdd t))) y = y := by
  classical
  let x : ComplexPoint (g3_power Y n) := s2_lift n (fun _ => y)
  obtain ⟨v, τ, hv, he⟩ := hq x
    (Point.map (s2_action S Y a e n (s2_delta S n hn t) 1) x) ht.symm
  let f : ZMod S.m → ComplexPoint Y → ComplexPoint Y :=
    fun u z => Point.map (a (e.symm (.ofAdd u))) z
  have hadd (u v : ZMod S.m) (z : ComplexPoint Y) : f (u + v) z = f u (f v z) := by
    dsimp only [f, Point.map]
    rw [show e.symm (.ofAdd (u + v)) = e.symm (.ofAdd u) * e.symm (.ofAdd v) from
      map_mul e.symm _ _, hamul, Category.assoc]
  have hvalues (i : Fin n) : f (v i) y = f (s2_delta S n hn t i) y := by
    have hi := congrArg (fun z : ComplexPoint (g3_power Y n) => z ≫ g3_proj Y n i) he
    simp only [Point.map, s2_action, Category.assoc, s2_check_lift_proj] at hi
    simp only [← Category.assoc, x, s2_check_lift_proj] at hi
    exact hi
  have H := s2v_i2a_translation_sum_eq f hadd Finset.univ v (s2_delta S n hn t) y
    (fun i _ => hvalues i)
  have hdelta : ∑ i, s2_delta S n hn t i = t := by simp [s2_delta]
  rw [hv, hdelta] at H
  have hfzero : f 0 y = y := by simp only [f, ofAdd_zero, map_one, ha1, Point.map,
    Category.comp_id]
  exact H.symm.trans hfzero

/-- Powers of an actual scheme endomorphism induce the corresponding iterates on complex points.
Source: Mathlib, CategoryTheory.End.mul_asHom and Point.map_comp_apply. -/
theorem s2v_i2a_pointMap_end_power
    (W : Over (Spec ↧ℂ)) (d : W ⟶ W) (k : ℕ) (z : ComplexPoint W) :
    Point.map (((End.of d) ^ k).asHom) z = (Point.map d)^[k] z := by
  induction k with
  | zero => simp only [pow_zero, End.one_asHom, Point.map_id, Function.iterate_zero, id_eq]
  | succ k ih =>
    simp only [pow_succ', End.mul_asHom, Point.map_comp_apply, ih,
      Function.iterate_succ_apply']

end HodgeLean.Foundations.Program
