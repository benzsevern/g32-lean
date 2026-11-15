import HodgeLean.Foundations.Program.SchoenTowerI1a
import HodgeLean.Foundations.Program.SchoenCoordinateActionLaws

/-! # I1b residual fibres and original branch inertia
Implication from the retained curve quotient, residual generator and tower inputs.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- A translation supported in one fixed coordinate fixes the actual product point.
Source: the universal property of the iterated scheme product. -/
theorem s2v_single_coordinate_translation_fixed
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (h : ℕ) (j : Fin h) (t : ZMod S.m)
    (x : ComplexPoint (g3_power Y h))
    (hx : Point.map (a (e.symm (.ofAdd t))) (Point.map (g3_proj Y h j) x) =
      Point.map (g3_proj Y h j) x) :
    Point.map (s2_action S Y a e h (Pi.single j t) 1) x = x := by
  classical
  obtain ⟨hlim⟩ := spec_g3_isLimit_fan_aux Y h
  apply Fan.IsLimit.hom_ext hlim
  intro i
  change (x ≫ s2_action S Y a e h (Pi.single j t) 1) ≫ g3_proj Y h i =
    x ≫ g3_proj Y h i
  rw [Category.assoc, s2_action, s2_check_lift_proj]
  have hi : (1 : Equiv.Perm (Fin h)).symm i = i := rfl
  rw [hi]
  by_cases hij : i = j
  · subst i
    simpa only [Point.map, Category.assoc, Pi.single_eq_same] using hx
  · simp [Pi.single_eq_of_ne hij, ha1]

/-- Translation vectors with equal sums induce the same map to the retained quotient.
Source: Schoen (1988), §1, p. 5, the sum kernel. -/
theorem s2v_quotient_translation_same_sum
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (h : ℕ) (q : g3_power Y h ⟶ W)
    (hqinv : ∀ (v : Fin h → ZMod S.m), ∑ i, v i = 0 →
      s2_action S Y a e h v 1 ≫ q = q)
    (v w : Fin h → ZMod S.m) (hvw : ∑ i, v i = ∑ i, w i) :
    s2_action S Y a e h v 1 ≫ q = s2_action S Y a e h w 1 ≫ q := by
  have hz : ∑ i, (v i - w i) = 0 := by rw [Finset.sum_sub_distrib, hvw, sub_self]
  have hc := (s2_coordinateAction_laws S Y a e ha1 hamul h).2 w (fun i => v i - w i) 1 1
  have hid : (fun i => v i - w i + w ((1 : Equiv.Perm (Fin h)).symm i)) = v := by
    funext i
    change v i - w i + w i = v i
    exact sub_add_cancel _ _
  rw [hid, one_mul] at hc
  rw [← hc, Category.assoc, hqinv _ hz]

/-- Iterates of the retained residual generator are represented by delta translations.
Source: Schoen (1988), §1, p. 5, the residual cyclic action. -/
theorem s2v_residual_generator_iterate
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (h : ℕ) (hh : 0 < h) (q : g3_power Y h ⟶ W) (d : W ⟶ W)
    (hgenerator : q ≫ d = s2_action S Y a e h (s2_delta S h hh 1) 1 ≫ q)
    (n : ℕ) (x : ComplexPoint (g3_power Y h)) :
    (Point.map d)^[n] (Point.map q x) =
      Point.map q (Point.map (s2_action S Y a e h (s2_delta S h hh n) 1) x) := by
  classical
  obtain ⟨hz, hadd⟩ := s2_coordinateAction_laws S Y a e ha1 hamul h
  induction n with
  | zero =>
    have hzero : s2_delta S h hh (0 : ZMod S.m) = 0 := by
      funext i
      simp [s2_delta]
    simp only [Nat.cast_zero, hzero, hz, Function.iterate_zero, id_eq, Point.map,
      Category.comp_id]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    change ((x ≫ s2_action S Y a e h (s2_delta S h hh n) 1) ≫ q) ≫ d = _
    rw [Category.assoc, hgenerator, ← Category.assoc, Category.assoc x,
      hadd _ _ 1 1]
    have he : (fun i => s2_delta S h hh 1 i +
        s2_delta S h hh (n : ZMod S.m) ((1 : Equiv.Perm (Fin h)).symm i)) =
        s2_delta S h hh (n + 1) := by
      funext i
      change s2_delta S h hh 1 i + s2_delta S h hh (n : ZMod S.m) i = _
      simp only [s2_delta]
      split_ifs <;> simp [add_comm]
    rw [he, one_mul]
    simp only [Nat.cast_add, Nat.cast_one, Point.map]

/-- A stabilizer of one point fixes its entire fibre in a cyclic curve quotient.
Source: Schoen (1988), §1, cyclic stabilizers and quotient fibres. -/
theorem s2v_curve_inertia_on_entire_fibre
    (S : g32p_Supplier) (Y Z : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (p : Y ⟶ Z)
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (u : S.H ⧸ S.χ.ker) (y : ComplexPoint Y)
    (hy : Point.map (a u) y = y) (x : ComplexPoint Y)
    (hx : Point.map p x = Point.map p y) : Point.map (a u) x = x := by
  obtain ⟨v, rfl⟩ := (hporbit y x).mp hx.symm
  have huv : u * v = v * u := by
    apply e.injective
    simp only [map_mul, mul_comm]
  change (y ≫ a v) ≫ a u = y ≫ a v
  rw [Category.assoc, ← hamul, huv, hamul, ← Category.assoc]
  exact congrArg (fun z : ComplexPoint Y => z ≫ a v) hy

/-- A fixed coordinate forces the corresponding residual deck iterate to fix its quotient point.
Source: Schoen (1988), §1, p. 5, the sum-kernel quotient. -/
theorem s2v_residual_iterate_fixed_of_coordinate
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (h : ℕ) (hh : 0 < h) (q : g3_power Y h ⟶ W)
    (hqinv : ∀ (v : Fin h → ZMod S.m), ∑ i, v i = 0 →
      s2_action S Y a e h v 1 ≫ q = q)
    (d : W ⟶ W)
    (hgenerator : q ≫ d = s2_action S Y a e h (s2_delta S h hh 1) 1 ≫ q)
    (n : ℕ) (j : Fin h) (x : ComplexPoint (g3_power Y h))
    (hx : Point.map (a (e.symm (.ofAdd (n : ZMod S.m))))
      (Point.map (g3_proj Y h j) x) = Point.map (g3_proj Y h j) x) :
    (Point.map d)^[n] (Point.map q x) = Point.map q x := by
  classical
  rw [s2v_residual_generator_iterate S Y W a e ha1 hamul h hh q d hgenerator]
  have hs : ∑ i, s2_delta S h hh (n : ZMod S.m) i =
      ∑ i, Pi.single j (n : ZMod S.m) i := by
    rw [s2_check_delta_sum]
    simp [Pi.single_apply]
  have he := s2v_quotient_translation_same_sum S Y W a e ha1 hamul h q hqinv
    (s2_delta S h hh (n : ZMod S.m)) (Pi.single j (n : ZMod S.m)) hs
  calc
    Point.map q (Point.map (s2_action S Y a e h (s2_delta S h hh n) 1) x) =
        Point.map q (Point.map (s2_action S Y a e h (Pi.single j (n : ZMod S.m)) 1) x) := by
      simpa only [Point.map, Category.assoc] using congrArg (fun f => x ≫ f) he
    _ = Point.map q x := congrArg (Point.map q)
      (s2v_single_coordinate_translation_fixed S Y a e ha1 h j n x hx)

/-- The retained rotation exponent fixes every point over its branch value.
Source: Schoen (1988), §1, p. 5, inertia exponents of the cyclic curve cover. -/
theorem s2v_rotation_exponent_fixes_curve_fibre
    (S : g32p_Supplier) (Y Z : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (p : Y ⟶ Z)
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    [ChartedSpace ℂ (rsq_Quot S.χ.ker C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C)]
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y))
    (y : rsq_Quot S.χ.ker C) (rot : S.H ⧸ S.χ.ker) (n : ℕ)
    (hrot : b4_IsRotGen ℂ y rot ∧ e rot = Multiplicative.ofAdd (n : ZMod S.m))
    (x : ComplexPoint Y) (hx : Point.map p x = Point.map p (eY y)) :
    Point.map (a (e.symm (.ofAdd (n : ZMod S.m)))) x = x := by
  have hy : Point.map (a rot) (eY y) = eY y := by
    rw [hpointAction, hrot.1.1]
  have he : e.symm (.ofAdd (n : ZMod S.m)) = rot := by
    rw [← hrot.2, e.symm_apply_apply]
  rw [he]
  exact s2v_curve_inertia_on_entire_fibre S Y Z a e hamul p hporbit rot (eY y) hy x hx

/-- A coordinate over a retained branch value gives inertia on the original quotient.
Source: Schoen (1988), §1, p. 5, the residual action and branch exponents. -/
theorem s2v_branch_coordinate_quotient_inertia
    (S : g32p_Supplier) (Y Z W : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (p : Y ⟶ Z)
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    [ChartedSpace ℂ (rsq_Quot S.χ.ker C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C)]
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y))
    (y : rsq_Quot S.χ.ker C) (rot : S.H ⧸ S.χ.ker) (n : ℕ)
    (hrot : b4_IsRotGen ℂ y rot ∧ e rot = Multiplicative.ofAdd (n : ZMod S.m))
    (h : ℕ) (hh : 0 < h) (q : g3_power Y h ⟶ W)
    (hqinv : ∀ (v : Fin h → ZMod S.m), ∑ i, v i = 0 →
      s2_action S Y a e h v 1 ≫ q = q)
    (d : W ⟶ W)
    (hgenerator : q ≫ d = s2_action S Y a e h (s2_delta S h hh 1) 1 ≫ q)
    (j : Fin h) (x : ComplexPoint (g3_power Y h))
    (hx : Point.map p (Point.map (g3_proj Y h j) x) = Point.map p (eY y)) :
    (Point.map d)^[n] (Point.map q x) = Point.map q x := by
  apply s2v_residual_iterate_fixed_of_coordinate S Y W a e ha1 hamul h hh q
    hqinv d hgenerator n j x
  exact s2v_rotation_exponent_fixes_curve_fibre S Y Z a e hamul p hporbit C eY
    hpointAction y rot n hrot (Point.map (g3_proj Y h j) x) hx

/-- Any translation and permutation has the same quotient map as its delta sum. -/
theorem s2v_action_quotient_delta_sum
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (h : ℕ) (hh : 0 < h) (q : g3_power Y h ⟶ W)
    (hqinv : ∀ (v : Fin h → ZMod S.m) (τ : Equiv.Perm (Fin h)),
      ∑ i, v i = 0 → s2_action S Y a e h v τ ≫ q = q)
    (v : Fin h → ZMod S.m) (τ : Equiv.Perm (Fin h)) :
    s2_action S Y a e h v τ ≫ q =
      s2_action S Y a e h (s2_delta S h hh (∑ i, v i)) 1 ≫ q := by
  let δ := s2_delta S h hh (∑ i, v i)
  let w := fun i => v i - δ (τ.symm i)
  have hw : ∑ i, w i = 0 := by
    dsimp [w]
    rw [Finset.sum_sub_distrib, Equiv.sum_comp τ.symm, s2_check_delta_sum, sub_self]
  have hc := (s2_coordinateAction_laws S Y a e ha1 hamul h).2 δ w 1 τ
  have he : (fun i => w i + δ (τ.symm i)) = v := by
    funext i
    exact sub_add_cancel _ _
  rw [he, mul_one] at hc
  rw [← hc, Category.assoc, hqinv w τ hw]

end HodgeLean.Foundations.Program
