import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.InsertionHelpers
import HodgeLean.Foundations.Program.SchoenCycleSymmetricBranch

/-! # Finite divisor support under insertion

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

/-- Distinct marked elements can be removed from a multiset with the exact residual cardinality.
Source: Effective-divisor multiset arithmetic; Milne, Jacobian Varieties, §3.
HC no distance; AV milestone no distance.
-/
theorem multiset_remove_distinct {α : Type*} (m k : ℕ) (s : Multiset α)
    (hs : s.card = m+k) (b : Fin k → α) (hb : Function.Injective b)
    (hmem : ∀ i, b i ∈ s) :
    ∃ r : Multiset α, r.card = m ∧ s = (List.ofFn b : Multiset α) + r := by
  classical
  let t : Multiset α := List.ofFn b
  have ht : t.Nodup := List.nodup_ofFn.mpr hb
  have hle : t ≤ s := (Multiset.le_iff_subset ht).mpr (by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hmem i)
  refine ⟨s-t, ?_, (by rw [add_comm]; exact (Multiset.sub_add_cancel hle).symm)⟩
  rw [Multiset.card_sub hle, hs]
  simp only [t, Multiset.coe_card, List.length_ofFn, Nat.add_sub_cancel_right]

/-- Inserting a point prepends it to the actual tuple of generalized coordinates.
Source: Milne, Jacobian Varieties, §3; finite product universal property.
HC no distance; AV milestone no distance.
-/
theorem insertion_point_coordinates (C : Over (Spec ↧ℂ)) (m : ℕ)
    (b : ComplexPoint C) (p : ComplexPoint (g3_power C m)) :
    (fun i => Point.map (g3_proj C (m+1) i)
      (Point.map (s2c_branchInsertion C m b) p)) =
      Fin.cons b (fun i => Point.map (g3_proj C m i) p) := by
  have H : p ≫ s2c_branchInsertion C m b =
      s2_lift (m+1) (Fin.cons b (fun i => Point.map (g3_proj C m i) p)) := by
    conv_lhs => rw [← s2e_lift_coordinates m p]
    exact s2e_branchInsertion_tuple C m b _
  funext i
  change (p ≫ s2c_branchInsertion C m b) ≫ g3_proj C (m+1) i = _
  rw [H, s2_check_lift_proj]

/-- The multiset of inserted coordinates is the marked multiset plus the residual tuple.
Source: Milne, Jacobian Varieties, §3, addition of effective divisors.
HC no distance; AV milestone no distance.
-/
theorem recursiveInsertion_point_multiset (C : Over (Spec ↧ℂ)) (m k : ℕ)
    (b : Fin k → ComplexPoint C) (p : ComplexPoint (g3_power C m)) :
    (List.ofFn (fun i => Point.map (g3_proj C (m+k) i)
      (Point.map (recursiveInsertion C m k b) p)) : Multiset (ComplexPoint C)) =
      (List.ofFn b : Multiset (ComplexPoint C)) +
        List.ofFn (fun i => Point.map (g3_proj C m i) p) := by
  induction k with
  | zero =>
    simp only [recursiveInsertion, Point.map, Category.comp_id, List.ofFn_zero,
      Multiset.coe_nil, zero_add, Nat.add_zero]
  | succ k ih =>
    have H := insertion_point_coordinates C (m+k) (b 0)
      (Point.map (recursiveInsertion C m k (fun i => b i.succ)) p)
    have hcoords : (fun i => Point.map (g3_proj C (m+(k+1)) i)
        (Point.map (recursiveInsertion C m (k+1) b) p)) =
        Fin.cons (b 0) (fun i => Point.map (g3_proj C (m+k) i)
          (Point.map (recursiveInsertion C m k (fun i => b i.succ)) p)) := by
      simpa only [recursiveInsertion, Point.map, Category.assoc, Nat.add_succ] using H
    rw [hcoords, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, ← Multiset.cons_coe]
    rw [ih]
    rw [List.ofFn_succ]
    simp only [← Multiset.cons_coe, Multiset.cons_add]

/-- Equality transport of a power degree preserves the multiset of its coordinates.
Source: Finite product universal property; equality transport.
HC no distance; AV milestone no distance.
-/
theorem point_multiset_power_cast (C : Over (Spec ↧ℂ)) {m n : ℕ} (h : m = n)
    (p : ComplexPoint (g3_power C m)) :
    (List.ofFn (fun i => Point.map (g3_proj C n i)
      (Point.map (eqToHom (congrArg (g3_power C) h)) p)) : Multiset (ComplexPoint C)) =
      List.ofFn (fun i => Point.map (g3_proj C m i) p) := by
  subst n
  simp only [eqToHom_refl, Point.map, Category.comp_id]

/-- Literal multiple insertion adds the marked multiset to the residual coordinate multiset.
Source: Milne, Jacobian Varieties, §3, addition of effective divisors.
HC no distance; AV milestone no distance.
-/
theorem multipleInsertion_point_multiset (C : Over (Spec ↧ℂ))
    [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    (h k : ℕ) (hk : k ≤ h+1) (b : Fin k → ComplexPoint C)
    (p : ComplexPoint (g3_power C (h+1-k))) :
    (List.ofFn (fun i => Point.map (g3_proj C (h+1) i)
      (Point.map (multipleInsertion C h k hk b) p)) : Multiset (ComplexPoint C)) =
      (List.ofFn b : Multiset (ComplexPoint C)) +
        List.ofFn (fun i => Point.map (g3_proj C (h+1-k) i) p) := by
  rw [← recursiveInsertion_eq_multipleInsertion C h k hk b]
  change (List.ofFn (fun i => Point.map (g3_proj C (h+1) i)
    (Point.map (eqToHom (congrArg (g3_power C) (Nat.sub_add_cancel hk)))
      (Point.map (recursiveInsertion C (h+1-k) k b) p))) : Multiset (ComplexPoint C)) = _
  rw [point_multiset_power_cast, recursiveInsertion_point_multiset]
  all_goals omega

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
