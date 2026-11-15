import Mathlib.Topology.Homotopy.Basic
import Mathlib.Algebra.BigOperators.Field
import HodgeLean.Foundations.Program.SchoenTransferC1a5BoundaryCoordinates
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Coordinate constructions for standard simplex boundary neighborhoods.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Convexity
namespace HodgeLean.Foundations.Program

/-- Minimum barycentric coordinate of a positive-dimensional standard simplex.
Source: Hatcher §2.1, Theorem 2.20, simplex boundary neighborhood construction. -/
def c1a5_simplex_min_weight (n : ℕ) (p : StdSimplex ℝ (Fin (n + 2))) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i ↦ p.weights i)

example (n : ℕ) := c1a5_simplex_min_weight n (StdSimplex.single 0)

/-- The minimum coordinate lies below each coordinate.
Source: Mathlib Finset.inf'_le. -/
lemma c1a5_simplex_min_weight_le (n : ℕ) (p : StdSimplex ℝ (Fin (n + 2))) (i : Fin (n + 2)) :
    c1a5_simplex_min_weight n p ≤ p.weights i :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- Minimum barycentric coordinates are nonnegative.
Source: Mathlib Finset.le_inf' and StdSimplex.weights_nonneg. -/
lemma c1a5_simplex_min_weight_nonneg (n : ℕ) (p : StdSimplex ℝ (Fin (n + 2))) :
    0 ≤ c1a5_simplex_min_weight n p := by
  exact Finset.le_inf' _ _ (fun i _ ↦ p.nonneg i)

/-- A minimum barycentric coordinate is attained at an actual vertex index.
Source: Mathlib Finset.exists_mem_eq_inf'. -/
lemma c1a5_simplex_min_weight_exists (n : ℕ) (p : StdSimplex ℝ (Fin (n + 2))) :
    ∃ i : Fin (n + 2), c1a5_simplex_min_weight n p = p.weights i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ)
    Finset.univ_nonempty (fun i ↦ p.weights i)
  exact ⟨i, hi⟩

/-- The minimum vanishes exactly on the coordinate boundary.
Source: Mathlib Finset.inf'_le and attainment of a finite minimum. -/
lemma c1a5_simplex_min_weight_eq_zero_iff (n : ℕ) (p : StdSimplex ℝ (Fin (n + 2))) :
    c1a5_simplex_min_weight n p = 0 ↔ ∃ i, p.weights i = 0 := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := c1a5_simplex_min_weight_exists n p
    exact ⟨i, hi.symm.trans h⟩
  · rintro ⟨i, hi⟩
    exact le_antisymm (hi ▸ c1a5_simplex_min_weight_le n p i)
      (c1a5_simplex_min_weight_nonneg n p)

/-- Subtract a common amount from every coordinate and normalize the remaining mass.
Source: Hatcher §2.1, Theorem 2.20, radial simplex boundary neighborhood construction. -/
def c1a5_simplex_trim (n : ℕ) (p : StdSimplex ℝ (Fin (n + 2))) (t : ℝ)
    (ht : t ≤ c1a5_simplex_min_weight n p) (hd : 0 < 1 - (n + 2 : ℝ) * t) :
    StdSimplex ℝ (Fin (n + 2)) where
  weights := Finsupp.onFinset Finset.univ
    (fun i ↦ (p.weights i - t) / (1 - (n + 2 : ℝ) * t)) (fun i _ ↦ Finset.mem_univ i)
  nonneg := by
    intro i
    change 0 ≤ (p.weights i - t) / (1 - (n + 2 : ℝ) * t)
    exact div_nonneg (sub_nonneg.mpr (ht.trans (c1a5_simplex_min_weight_le n p i))) hd.le
  total := by
    rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
    simp only [Finsupp.onFinset_apply]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, StdSimplex.total_of_fintype]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat]
    exact div_self (ne_of_gt hd)

example (n : ℕ) (p : StdSimplex ℝ (Fin (n + 2))) :=
  c1a5_simplex_trim n p 0 (c1a5_simplex_min_weight_nonneg n p) (by norm_num)

/-- The normalized subtraction has the specified barycentric coordinates.
Source: Mathlib Finsupp.onFinset_apply. -/
@[simp]
lemma c1a5_simplex_trim_weights (n : ℕ) (p : StdSimplex ℝ (Fin (n + 2))) (t : ℝ)
    (ht : t ≤ c1a5_simplex_min_weight n p) (hd : 0 < 1 - (n + 2 : ℝ) * t) (i : Fin (n + 2)) :
    (c1a5_simplex_trim n p t ht hd).weights i =
      (p.weights i - t) / (1 - (n + 2 : ℝ) * t) := rfl

/-- The minimum barycentric coordinate varies continuously.
Source: Mathlib Continuous.finset_inf'_apply and StdSimplex.continuous_weights_apply. -/
@[fun_prop]
lemma c1a5_continuous_simplex_min_weight (n : ℕ) : Continuous (c1a5_simplex_min_weight n) := by
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun i _ ↦ StdSimplex.continuous_weights_apply ℝ i)

/-- Minimum coordinates transform by the same normalized subtraction formula.
Source: Mathlib finite minimum inequalities and positive division. -/
lemma c1a5_simplex_trim_min_weight (n : ℕ) (p : StdSimplex ℝ (Fin (n + 2))) (t : ℝ)
    (ht : t ≤ c1a5_simplex_min_weight n p) (hd : 0 < 1 - (n + 2 : ℝ) * t) :
    c1a5_simplex_min_weight n (c1a5_simplex_trim n p t ht hd) =
      (c1a5_simplex_min_weight n p - t) / (1 - (n + 2 : ℝ) * t) := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := c1a5_simplex_min_weight_exists n p
    calc
      c1a5_simplex_min_weight n (c1a5_simplex_trim n p t ht hd) ≤
          (c1a5_simplex_trim n p t ht hd).weights i := c1a5_simplex_min_weight_le _ _ _
      _ = _ := by rw [c1a5_simplex_trim_weights, ← hi]
  · apply Finset.le_inf'
    intro i _
    change (c1a5_simplex_min_weight n p - t) / (1 - (n + 2 : ℝ) * t) ≤
      (p.weights i - t) / (1 - (n + 2 : ℝ) * t)
    exact (div_le_div_iff_of_pos_right hd).2
      (sub_le_sub_right (c1a5_simplex_min_weight_le n p i) t)

/-- Normalized subtraction depends continuously on its simplex and scalar parameters.
Source: Mathlib StdSimplex.isEmbedding_toFun_comp_weights and continuity of division. -/
lemma c1a5_continuous_simplex_trim {X : Type*} [TopologicalSpace X]
    (n : ℕ) (p : X → StdSimplex ℝ (Fin (n + 2))) (t : X → ℝ)
    (hp : Continuous p) (ht : Continuous t)
    (hmin : ∀ x, t x ≤ c1a5_simplex_min_weight n (p x))
    (hd : ∀ x, 0 < 1 - (n + 2 : ℝ) * t x) :
    Continuous (fun x ↦ c1a5_simplex_trim n (p x) (t x) (hmin x) (hd x)) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff]
  unfold Function.comp
  refine continuous_pi (fun i ↦ ?_)
  simp only [c1a5_simplex_trim_weights]
  exact (((StdSimplex.continuous_weights_apply ℝ i).comp hp).sub ht).div
    (continuous_const.sub (continuous_const.mul ht)) (fun x ↦ ne_of_gt (hd x))

/-- The gap from the simplex center transforms by a positive denominator.
Source: normalized subtraction of barycentric coordinates and field algebra. -/
lemma c1a5_simplex_trim_gap (n : ℕ) (p : StdSimplex ℝ (Fin (n + 2))) (t : ℝ)
    (ht : t ≤ c1a5_simplex_min_weight n p) (hd : 0 < 1 - (n + 2 : ℝ) * t) :
    1 - (n + 2 : ℝ) * c1a5_simplex_min_weight n (c1a5_simplex_trim n p t ht hd) =
      (1 - (n + 2 : ℝ) * c1a5_simplex_min_weight n p) / (1 - (n + 2 : ℝ) * t) := by
  rw [c1a5_simplex_trim_min_weight]
  field_simp [ne_of_gt hd]
  <;> ring

/-- Subtracting zero is the identity on simplex points.
Source: the explicit normalized subtraction coordinate formula. -/
@[simp]
lemma c1a5_simplex_trim_zero (n : ℕ) (p : StdSimplex ℝ (Fin (n + 2))) :
    c1a5_simplex_trim n p 0 (c1a5_simplex_min_weight_nonneg n p) (by norm_num) = p := by
  apply StdSimplex.ext
  ext i
  simp only [c1a5_simplex_trim_weights, mul_zero, sub_zero, div_one]

/-- The standard simplex neighborhood obtained by removing the common-coordinate center.
Source: Hatcher §2.1, Theorem 2.20, simplex boundary neighborhood construction. -/
abbrev c1a5_simplex_collar (n : ℕ) : Type :=
  {p : StdSimplex ℝ (Fin (n + 2)) //
    0 < 1 - (n + 2 : ℝ) * c1a5_simplex_min_weight n p}

example (n : ℕ) (p : c1a5_simplex_collar n) : StdSimplex ℝ (Fin (n + 2)) := p.val

/-- The coordinate boundary lies in the standard simplex neighborhood.
Source: the vanishing-minimum characterization of the coordinate boundary. -/
lemma c1a5_simplex_collar_contains_boundary (n : ℕ) (p : StdSimplex ℝ (Fin (n + 2)))
    (hp : ∃ i, p.weights i = 0) :
    0 < 1 - (n + 2 : ℝ) * c1a5_simplex_min_weight n p := by
  rw [(c1a5_simplex_min_weight_eq_zero_iff n p).2 hp]
  norm_num

/-- The standard simplex boundary neighborhood is open.
Source: continuity of the finite minimum of the barycentric coordinates. -/
lemma c1a5_simplex_collar_isOpen (n : ℕ) :
    IsOpen (setOf (fun p : StdSimplex ℝ (Fin (n + 2)) ↦
      0 < 1 - (n + 2 : ℝ) * c1a5_simplex_min_weight n p)) := by
  exact isOpen_lt continuous_const
    (continuous_const.sub (continuous_const.mul (c1a5_continuous_simplex_min_weight n)))

/-- The coordinate boundary includes continuously into its open simplex neighborhood.
Source: Hatcher §2.1, Theorem 2.20, the simplex boundary neighborhood. -/
def c1a5_coordinate_boundary_to_collar (n : ℕ) :
    C({p : StdSimplex ℝ (Fin (n + 2)) // ∃ i : Fin (n + 2), p.weights i = 0},
      c1a5_simplex_collar n) where
  toFun p := ⟨p.val, c1a5_simplex_collar_contains_boundary n p.val p.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

example (n : ℕ) := c1a5_coordinate_boundary_to_collar n

/-- Normalized minimum subtraction retracts the simplex neighborhood to its coordinate boundary.
Source: Hatcher §2.1, Theorem 2.20, simplex boundary neighborhood retraction. -/
def c1a5_simplex_collar_retract (n : ℕ) :
    C(c1a5_simplex_collar n,
      {p : StdSimplex ℝ (Fin (n + 2)) // ∃ i : Fin (n + 2), p.weights i = 0}) where
  toFun p := by
    refine ⟨c1a5_simplex_trim n p.val (c1a5_simplex_min_weight n p.val) le_rfl p.property, ?_⟩
    apply (c1a5_simplex_min_weight_eq_zero_iff n _).1
    rw [c1a5_simplex_trim_min_weight, sub_self, zero_div]
  continuous_toFun :=
    (c1a5_continuous_simplex_trim n Subtype.val
      (fun p : c1a5_simplex_collar n ↦ c1a5_simplex_min_weight n p.val)
      continuous_subtype_val ((c1a5_continuous_simplex_min_weight n).comp continuous_subtype_val)
      (fun _ ↦ le_rfl) (fun p ↦ p.property)).subtype_mk _

example (n : ℕ) := c1a5_simplex_collar_retract n

/-- The neighborhood retraction fixes every coordinate boundary point.
Source: the zero-minimum characterization and normalized subtraction coordinate formula. -/
lemma c1a5_simplex_collar_retract_boundary (n : ℕ) :
    (c1a5_simplex_collar_retract n).comp (c1a5_coordinate_boundary_to_collar n) =
      ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply StdSimplex.ext
  ext i
  change (p.val.weights i - c1a5_simplex_min_weight n p.val) /
    (1 - (n + 2 : ℝ) * c1a5_simplex_min_weight n p.val) = p.val.weights i
  rw [(c1a5_simplex_min_weight_eq_zero_iff n p.val).2 p.property]
  simp only [sub_zero, mul_zero, div_one]

/-- Every intermediate subtraction amount in the unit interval has positive normalization mass.
Source: positivity of the simplex neighborhood gap and the unit interval bound. -/
lemma c1a5_collar_time_denominator_pos (n : ℕ) (p : c1a5_simplex_collar n) (t : unitInterval) :
    0 < 1 - (n + 2 : ℝ) * ((t : ℝ) * c1a5_simplex_min_weight n p.val) := by
  have ht : (t : ℝ) * c1a5_simplex_min_weight n p.val ≤ c1a5_simplex_min_weight n p.val :=
    mul_le_of_le_one_left (c1a5_simplex_min_weight_nonneg n p.val) t.property.2
  exact lt_of_lt_of_le p.property
    (sub_le_sub_left (mul_le_mul_of_nonneg_left ht (by positivity)) 1)

/-- Normalized subtraction restricts to the actual simplex neighborhood.
Source: the explicit positive gap formula for normalized subtraction. -/
def c1a5_collar_trim (n : ℕ) (p : c1a5_simplex_collar n) (t : ℝ)
    (ht : t ≤ c1a5_simplex_min_weight n p.val) (hd : 0 < 1 - (n + 2 : ℝ) * t) :
    c1a5_simplex_collar n :=
  ⟨c1a5_simplex_trim n p.val t ht hd, by
    rw [c1a5_simplex_trim_gap]
    exact div_pos p.property hd⟩

example (n : ℕ) (p : c1a5_simplex_collar n) :=
  c1a5_collar_trim n p 0 (c1a5_simplex_min_weight_nonneg n p.val) (by norm_num)

/-- The coordinate boundary neighborhood deforms continuously onto its boundary retraction.
Source: Hatcher §2.1, Theorem 2.20, radial boundary neighborhood deformation. -/
def c1a5_simplex_collar_homotopy (n : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id (c1a5_simplex_collar n))
      ((c1a5_coordinate_boundary_to_collar n).comp (c1a5_simplex_collar_retract n)) where
  toFun q := c1a5_collar_trim n q.2
    ((q.1 : ℝ) * c1a5_simplex_min_weight n q.2.val)
    (mul_le_of_le_one_left (c1a5_simplex_min_weight_nonneg n q.2.val) q.1.property.2)
    (c1a5_collar_time_denominator_pos n q.2 q.1)
  continuous_toFun := by
    have hp : Continuous (fun q : unitInterval × c1a5_simplex_collar n ↦ q.2.val) :=
      continuous_subtype_val.comp continuous_snd
    have ht : Continuous (fun q : unitInterval × c1a5_simplex_collar n ↦
        (q.1 : ℝ) * c1a5_simplex_min_weight n q.2.val) :=
      (continuous_subtype_val.comp continuous_fst).mul
        ((c1a5_continuous_simplex_min_weight n).comp hp)
    exact (c1a5_continuous_simplex_trim n
      (fun q : unitInterval × c1a5_simplex_collar n ↦ q.2.val)
      (fun q ↦ (q.1 : ℝ) * c1a5_simplex_min_weight n q.2.val) hp ht
      (fun q ↦ mul_le_of_le_one_left (c1a5_simplex_min_weight_nonneg n q.2.val) q.1.property.2)
      (fun q ↦ c1a5_collar_time_denominator_pos n q.2 q.1)).subtype_mk _
  map_zero_left p := by
    apply Subtype.ext
    apply StdSimplex.ext
    ext i
    change (p.val.weights i - (0 : ℝ) * c1a5_simplex_min_weight n p.val) /
      (1 - (n + 2 : ℝ) * ((0 : ℝ) * c1a5_simplex_min_weight n p.val)) = p.val.weights i
    simp only [zero_mul, mul_zero, sub_zero, div_one]
  map_one_left p := by
    apply Subtype.ext
    apply StdSimplex.ext
    ext i
    change (p.val.weights i - (1 : ℝ) * c1a5_simplex_min_weight n p.val) /
      (1 - (n + 2 : ℝ) * ((1 : ℝ) * c1a5_simplex_min_weight n p.val)) =
        (p.val.weights i - c1a5_simplex_min_weight n p.val) /
          (1 - (n + 2 : ℝ) * c1a5_simplex_min_weight n p.val)
    simp only [one_mul]

example (n : ℕ) := c1a5_simplex_collar_homotopy n

/-- The neighborhood deformation fixes boundary points at every time.
Source: the zero minimum weight of boundary points and the coordinate deformation formula. -/
lemma c1a5_simplex_collar_homotopy_fixed (n : ℕ) (t : unitInterval)
    (p : {p : StdSimplex ℝ (Fin (n + 2)) // ∃ i : Fin (n + 2), p.weights i = 0}) :
    c1a5_simplex_collar_homotopy n (t, c1a5_coordinate_boundary_to_collar n p) =
      c1a5_coordinate_boundary_to_collar n p := by
  apply Subtype.ext
  apply StdSimplex.ext
  ext i
  change (p.val.weights i - (t : ℝ) * c1a5_simplex_min_weight n p.val) /
    (1 - (n + 2 : ℝ) * ((t : ℝ) * c1a5_simplex_min_weight n p.val)) = p.val.weights i
  rw [(c1a5_simplex_min_weight_eq_zero_iff n p.val).2 p.property]
  simp only [mul_zero, sub_zero, div_one]

end HodgeLean.Foundations.Program
