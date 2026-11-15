import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Tactic

/-!
# Extending a local one-parameter subgroup

Stage S11. HC no distance; AV milestone no distance. This retires nothing.
The subdivision construction uses only the group laws, without commutativity.
-/

open Filter Topology

namespace HodgeLean.Foundations

/-- A group-valued local homomorphism on a symmetric real interval.
Values outside that interval are not constrained.

Source: constructed here for the subdivision construction of one-parameter subgroups. -/
structure LocalOneParameter (G : Type*) [Group G] where
  radius : ℝ
  radius_pos : 0 < radius
  curve : ℝ → G
  map_zero : curve 0 = 1
  map_add : ∀ s t : ℝ, |s| < radius → |t| < radius → |s + t| < radius →
    curve (s + t) = curve s * curve t

example (G : Type*) [Group G] : LocalOneParameter G where
  radius := 1
  radius_pos := zero_lt_one
  curve := fun _ ↦ 1
  map_zero := rfl
  map_add := by intros; simp

namespace LocalOneParameter
variable {G : Type*} [Group G] (c : LocalOneParameter G)

private theorem curve_pow (n : ℕ) (x : ℝ) (hx : |(n : ℝ) * x| < c.radius) :
    c.curve x ^ n = c.curve ((n : ℝ) * x) := by
  induction n with
  | zero => simpa using c.map_zero.symm
  | succ n ih =>
    have hnx : |(n : ℝ) * x| < c.radius := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (n + 1)), Nat.cast_add, Nat.cast_one] at hx
      nlinarith [abs_nonneg x]
    have hx' : |x| < c.radius := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (n + 1)), Nat.cast_add, Nat.cast_one] at hx
      nlinarith [abs_nonneg x, Nat.cast_nonneg (α := ℝ) n]
    rw [pow_succ, ih hnx, ← c.map_add _ _ hnx hx' (by simpa [add_mul] using hx)]
    congr 1
    push_cast
    ring

private theorem exists_index (t : ℝ) :
    ∃ n : ℕ, 0 < n ∧ |t / (n : ℝ)| < c.radius := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| / c.radius)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (abs_nonneg _) c.radius_pos.le) hn
  refine ⟨n, Nat.cast_pos.mp hn0, ?_⟩
  rw [abs_div, abs_of_pos hn0, div_lt_iff₀ hn0]
  have h := (div_lt_iff₀ c.radius_pos).mp hn
  linarith

private theorem subdivision_independent (t : ℝ) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (htm : |t / (m : ℝ)| < c.radius) (htn : |t / (n : ℝ)| < c.radius) :
    c.curve (t / (m : ℝ)) ^ m = c.curve (t / (n : ℝ)) ^ n := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  let z := t / ((m : ℝ) * n)
  have hzm : (n : ℝ) * z = t / m := by dsimp [z]; field_simp
  have hzn : (m : ℝ) * z = t / n := by dsimp [z]; field_simp
  have h1 := c.curve_pow n z (by rwa [hzm])
  have h2 := c.curve_pow m z (by rwa [hzn])
  rw [hzm] at h1
  rw [hzn] at h2
  rw [← h1, ← h2, ← pow_mul, ← pow_mul, Nat.mul_comm n m]

private noncomputable def value (t : ℝ) : G :=
  c.curve (t / ((c.exists_index t).choose : ℝ)) ^ (c.exists_index t).choose

private theorem value_eq_pow (t : ℝ) {n : ℕ} (hn : 0 < n)
    (ht : |t / (n : ℝ)| < c.radius) :
    c.value t = c.curve (t / (n : ℝ)) ^ n :=
  c.subdivision_independent t (c.exists_index t).choose_spec.1 hn
    (c.exists_index t).choose_spec.2 ht

private theorem value_eq (t : ℝ) (ht : |t| < c.radius) : c.value t = c.curve t := by
  simpa using c.value_eq_pow t (n := 1) (by decide) (by simpa using ht)

private theorem value_zero : c.value 0 = 1 := by
  rw [c.value_eq 0 (by simpa using c.radius_pos), c.map_zero]

private theorem value_add (s t : ℝ) : c.value (s + t) = c.value s * c.value t := by
  obtain ⟨n, hn, hbound⟩ := c.exists_index (|s| + |t|)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hB : |s| + |t| < c.radius * n := by
    rw [abs_div, abs_of_nonneg (add_nonneg (abs_nonneg s) (abs_nonneg t)),
      abs_of_pos hn0, div_lt_iff₀ hn0] at hbound
    exact hbound
  have hs : |s / (n : ℝ)| < c.radius := by
    rw [abs_div, abs_of_pos hn0, div_lt_iff₀ hn0]
    linarith [abs_nonneg t]
  have ht : |t / (n : ℝ)| < c.radius := by
    rw [abs_div, abs_of_pos hn0, div_lt_iff₀ hn0]
    linarith [abs_nonneg s]
  have hst : |(s + t) / (n : ℝ)| < c.radius := by
    rw [abs_div, abs_of_pos hn0, div_lt_iff₀ hn0]
    exact lt_of_le_of_lt (abs_add_le s t) hB
  have hst' : |s / (n : ℝ) + t / n| < c.radius := by rwa [← add_div]
  have hts' : |t / (n : ℝ) + s / n| < c.radius := by rwa [add_comm]
  have hc : Commute (c.curve (s / (n : ℝ))) (c.curve (t / (n : ℝ))) := by
    change c.curve (s / (n : ℝ)) * c.curve (t / (n : ℝ)) = _
    rw [← c.map_add _ _ hs ht hst', ← c.map_add _ _ ht hs hts', add_comm]
  rw [c.value_eq_pow (s + t) hn hst, c.value_eq_pow s hn hs, c.value_eq_pow t hn ht,
    add_div, c.map_add _ _ hs ht hst', hc.mul_pow]

/-- The global homomorphism obtained by subdividing time and taking a group power.

Source: constructed here from the local group law by common refinement of subdivisions. -/
noncomputable def extend : ℝ →+ Additive G where
  toFun t := Additive.ofMul (c.value t)
  map_zero' := c.value_zero
  map_add' := c.value_add

/-- Every sufficiently fine positive integer subdivision computes the extension.
In particular its value is independent of the chosen subdivision.

Source: constructed here by refining subdivisions `m` and `n` to `m*n`. -/
theorem extend_eq_pow (t : ℝ) {n : ℕ} (hn : 0 < n)
    (ht : |t / (n : ℝ)| < c.radius) :
    (c.extend t).toMul = c.curve (t / (n : ℝ)) ^ n := c.value_eq_pow t hn ht

example (t : ℝ) {n : ℕ} (hn : 0 < n) (ht : |t / (n : ℝ)| < c.radius) :
    (c.extend t).toMul = c.curve (t / (n : ℝ)) ^ n := c.extend_eq_pow t hn ht

/-- Extension agrees with the original curve throughout its local interval.

Source: constructed here by taking the subdivision with one part. -/
theorem extend_eq (t : ℝ) (ht : |t| < c.radius) :
    (c.extend t).toMul = c.curve t := c.value_eq t ht

example (t : ℝ) (ht : |t| < c.radius) : (c.extend t).toMul = c.curve t := c.extend_eq t ht

example : c.extend 0 = 0 := _root_.map_zero c.extend

/-- Continuity at zero of the local curve gives continuity of the global homomorphism.

Source: constructed here using continuity of a group homomorphism at the identity. -/
theorem continuous_extend [TopologicalSpace G] [IsTopologicalGroup G]
    (hc : ContinuousAt c.curve 0) : Continuous c.extend := by
  apply continuous_of_continuousAt_zero c.extend
  have he : (fun t ↦ (c.extend t).toMul) =ᶠ[𝓝 0] c.curve := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) c.radius_pos] with t ht
    exact c.extend_eq t (by simpa [Real.dist_eq] using ht)
  exact hc.congr he.symm

example [TopologicalSpace G] [IsTopologicalGroup G] (hc : ContinuousAt c.curve 0) :
    Continuous c.extend := c.continuous_extend hc

end LocalOneParameter
/-- Homomorphisms out of the additive real line agreeing near zero agree everywhere.
No continuity or commutativity of the codomain is required.

Source: constructed here by subdividing each real time into arbitrarily small equal parts. -/
theorem real_addHom_ext_of_eventuallyEq {A : Type*} [AddGroup A]
    (f g : ℝ →+ A) (h : (f : ℝ → A) =ᶠ[𝓝 0] g) : f = g := by
  ext t
  have he := (tendsto_const_div_atTop_nhds_zero_nat t).eventually h
  obtain ⟨n, hn, he⟩ := ((eventually_gt_atTop 0).and he).exists
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have ht : n • (t / (n : ℝ)) = t := by
    rw [nsmul_eq_mul]
    field_simp
  calc
    f t = f (n • (t / (n : ℝ))) := congrArg f ht.symm
    _ = n • f (t / (n : ℝ)) := _root_.map_nsmul f _ _
    _ = n • g (t / (n : ℝ)) := congrArg (n • ·) he
    _ = g (n • (t / (n : ℝ))) := (_root_.map_nsmul g _ _).symm
    _ = g t := congrArg g ht

example {A : Type*} [AddGroup A] (f g : ℝ →+ A)
    (h : (f : ℝ → A) =ᶠ[𝓝 0] g) : f = g := real_addHom_ext_of_eventuallyEq f g h

end HodgeLean.Foundations

#print axioms HodgeLean.Foundations.LocalOneParameter.extend
#print axioms HodgeLean.Foundations.LocalOneParameter.extend_eq_pow
#print axioms HodgeLean.Foundations.LocalOneParameter.extend_eq
#print axioms HodgeLean.Foundations.LocalOneParameter.continuous_extend

#print axioms HodgeLean.Foundations.real_addHom_ext_of_eventuallyEq
