import HodgeLean.Foundations.Singular.GradedComm
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! # Exterior powers of degree-one singular cohomology
HC no distance; AV milestone no distance.
-/

namespace HodgeLean.Foundations.Singular

variable (Y : TopCat.{0})

/-- One step of the cup of `m` degree-one classes: `a ↦ (a ∪ -) ∘ f`, linear in `a`.
Source: Hatcher, *Algebraic Topology*, §3.2 and Theorem 3.11; iterated cup and alternation. -/
private noncomputable def cupLeftMulti (m : ℕ)
    (f : MultilinearMap ℚ (fun _ : Fin m => AlgebraicTopology.Singular.Cohomology ℚ Y 1) (AlgebraicTopology.Singular.Cohomology ℚ Y m)) :
    AlgebraicTopology.Singular.Cohomology ℚ Y 1 →ₗ[ℚ] MultilinearMap ℚ (fun _ : Fin m => AlgebraicTopology.Singular.Cohomology ℚ Y 1) (AlgebraicTopology.Singular.Cohomology ℚ Y (m + 1)) where
  toFun a := (cup Y (Nat.add_comm 1 m) a).compMultilinearMap f
  map_add' a b := by ext; simp
  map_smul' c a := by ext; simp

/-- The multilinear map `(a₁, …, a_m) ↦ a₁ ∪ (a₂ ∪ ⋯ ∪ (a_m ∪ 1))`, with the unit as the empty
product.
Source: Hatcher, *Algebraic Topology*, §3.2 and Theorem 3.11; iterated cup and alternation. -/
noncomputable def cupMulti :
    ∀ m : ℕ, MultilinearMap ℚ (fun _ : Fin m => AlgebraicTopology.Singular.Cohomology ℚ Y 1) (AlgebraicTopology.Singular.Cohomology ℚ Y m)
  | 0 => MultilinearMap.constOfIsEmpty ℚ _ (unit Y)
  | m + 1 => (cupLeftMulti Y m (cupMulti m)).uncurryLeft

/-- The empty iterated cup is the singular unit.
Source: the degree-zero clause of `cupMulti`. -/
theorem cupMulti_zero (v : Fin 0 → AlgebraicTopology.Singular.Cohomology ℚ Y 1) :
    cupMulti Y 0 v = unit Y :=
  rfl

/-- Iterated cup is computed from its first factor and its tail.
Source: the successor clause of `cupMulti`. -/
theorem cupMulti_succ (m : ℕ) (h : 1 + m = m + 1) (v : Fin (m + 1) → AlgebraicTopology.Singular.Cohomology ℚ Y 1) :
    cupMulti Y (m + 1) v = cup Y h (v 0) (cupMulti Y m (Fin.tail v)) :=
  rfl

/-- A degree-one class that already occurs among `w` cups `cupMulti Y m w` to zero.
Source: Hatcher, *Algebraic Topology*, §3.2 and Theorem 3.11; iterated cup and alternation. -/
private theorem cup_cupMulti_eq_zero :
    ∀ (m : ℕ) (h : 1 + m = m + 1) (w : Fin m → AlgebraicTopology.Singular.Cohomology ℚ Y 1) (k : Fin m),
      cup Y h (w k) (cupMulti Y m w) = 0
  | 0, _, _, k => k.elim0
  | m + 1, h, w, k => by
    rw [cupMulti_succ Y m (Nat.add_comm 1 m),
      ← cup_assoc Y (rfl : 1 + 1 = 2) (Nat.add_comm 1 m) (by omega) h]
    refine Fin.cases ?_ (fun k' => ?_) k
    · rw [cup_self_one_eq_zero Y, map_zero, LinearMap.zero_apply]
    · rw [cup_comm_one_one Y, map_neg, LinearMap.neg_apply,
        cup_assoc Y (rfl : 1 + 1 = 2) (Nat.add_comm 1 m) (by omega) h]
      have := cup_cupMulti_eq_zero m (Nat.add_comm 1 m) (Fin.tail w) k'
      rw [Fin.tail] at this
      rw [this, map_zero, neg_zero]

/-- `cupMulti Y m` vanishes on families with a repeated entry.
Source: Hatcher, *Algebraic Topology*, §3.2 and Theorem 3.11; iterated cup and alternation. -/
private theorem cupMulti_eq_zero_of_eq :
    ∀ (m : ℕ) (v : Fin m → AlgebraicTopology.Singular.Cohomology ℚ Y 1) (i j : Fin m), v i = v j → i ≠ j → cupMulti Y m v = 0
  | 0, _, i, _, _, _ => i.elim0
  | m + 1, v, i, j, hv, hij => by
    rw [cupMulti_succ Y m (Nat.add_comm 1 m)]
    have key : ∀ (i j : Fin (m + 1)), v i = v j → i ≠ j → i = 0 →
        cup Y (Nat.add_comm 1 m) (v 0) (cupMulti Y m (Fin.tail v)) = 0 := by
      intro i j hv hij hi
      subst hi
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hij.symm
      rw [hv]
      exact cup_cupMulti_eq_zero Y m _ (Fin.tail v) j'
    by_cases hi : i = 0
    · exact key i j hv hij hi
    by_cases hj : j = 0
    · exact key j i hv.symm hij.symm hj
    obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
    rw [cupMulti_eq_zero_of_eq m (Fin.tail v) i' j' hv (fun h => hij (by rw [h])), map_zero]

/-- The alternating map `(a₁, …, a_m) ↦ a₁ ∪ ⋯ ∪ a_m`.
Source: Hatcher, *Algebraic Topology*, §3.2 and Theorem 3.11; iterated cup and alternation. -/
private noncomputable def cupAlternating (m : ℕ) :
    AlgebraicTopology.Singular.Cohomology ℚ Y 1 [⋀^Fin m]→ₗ[ℚ] AlgebraicTopology.Singular.Cohomology ℚ Y m where
  toMultilinearMap := cupMulti Y m
  map_eq_zero_of_eq' v i j hv hij := cupMulti_eq_zero_of_eq Y m v i j hv hij

/-- The singular wedge map `⋀^m H¹(Y; ℚ) → H^m(Y; ℚ)`, `a₁ ∧ ⋯ ∧ a_m ↦ a₁ ∪ ⋯ ∪ a_m`.
Source: Hatcher, *Algebraic Topology*, §3.2 and Theorem 3.11; iterated cup and alternation. -/
noncomputable def cupWedgeMap (m : ℕ) : ⋀[ℚ]^m (AlgebraicTopology.Singular.Cohomology ℚ Y 1) →ₗ[ℚ] AlgebraicTopology.Singular.Cohomology ℚ Y m :=
  exteriorPower.alternatingMapLinearEquiv (cupAlternating Y m)

/-- On a pure wedge the exterior map is iterated cup.
Source: the universal property `exteriorPower.alternatingMapLinearEquiv_apply_ιMulti`. -/
theorem cupWedgeMap_ιMulti (m : ℕ) (v : Fin m → AlgebraicTopology.Singular.Cohomology ℚ Y 1) :
    cupWedgeMap Y m (exteriorPower.ιMulti ℚ m v) = cupMulti Y m v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _


example (v : Fin 0 → AlgebraicTopology.Singular.Cohomology ℚ Y 1) :
    cupMulti Y 0 v = unit Y := cupMulti_zero Y v

example (m : ℕ) (v : Fin m → AlgebraicTopology.Singular.Cohomology ℚ Y 1) :
    cupWedgeMap Y m (exteriorPower.ιMulti ℚ m v) = cupMulti Y m v :=
  cupWedgeMap_ιMulti Y m v

end HodgeLean.Foundations.Singular
