import HodgeConjecture.Mathlib.Topology.Category.TopPair
import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.FundamentalClass
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

/-! # Affine local cycles with a variable negative vertex

The parameter stays positive so every boundary face avoids the origin.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.QuotientDuality

/-- The standard affine simplex with its last vertex multiplied by the given parameter. -/
def properCycle_scaled_affine_simplex (d : ℕ) (a : ℝ)
    (t : StdSimplex ℝ (Fin (d+1))) : Fin d → ℝ :=
  fun j => t.weights (Fin.castSucc j) - a * t.weights (Fin.last d)

/-- Positive scaling of the negative vertex keeps every original face away from the origin. -/
theorem properCycle_scaled_affine_simplex_face_ne_zero
    (d : ℕ) (a : ℝ) (ha : 0 < a) (t : StdSimplex ℝ (Fin (d+1)))
    (i : Fin (d+1)) (hi : t.weights i = 0) :
    properCycle_scaled_affine_simplex d a t ≠ 0 := by
  intro hz
  have hcoord (j : Fin d) : t.weights (Fin.castSucc j) = a * t.weights (Fin.last d) := by
    exact sub_eq_zero.mp (congrFun hz j)
  have hlast : t.weights (Fin.last d) = 0 := by
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have hp : a * t.weights (Fin.last d) = 0 := (hcoord j).symm.trans hi
      exact (mul_eq_zero.mp hp).resolve_left (ne_of_gt ha)
    · exact hi
  have hall (j : Fin (d+1)) : t.weights j = 0 := by
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · exact (hcoord k).trans (by rw [hlast, mul_zero])
    · exact hlast
  have hzero : ∑ j, t.weights j = 0 := Finset.sum_eq_zero (fun j _ => hall j)
  exact zero_ne_one (hzero.symm.trans t.total_of_fintype)

example : properCycle_scaled_affine_simplex 1 0 (StdSimplex.single (Fin.last 1)) = 0 := by
  ext j
  simp only [properCycle_scaled_affine_simplex, zero_mul, sub_zero, Pi.zero_apply, StdSimplex.weights_single]
  exact Finsupp.single_eq_of_ne (Fin.castSucc_ne_last j)

/-- The affine local family is jointly continuous in its parameter and barycentric coordinates. -/
@[fun_prop] theorem properCycle_continuous_scaled_affine_simplex (d : ℕ) :
    Continuous (fun z : ℝ × StdSimplex ℝ (Fin (d+1)) =>
      properCycle_scaled_affine_simplex d z.1 z.2) := by
  apply continuous_pi
  intro j
  exact ((StdSimplex.continuous_weights_apply ℝ (Fin.castSucc j)).comp continuous_snd).sub
    (continuous_fst.mul ((StdSimplex.continuous_weights_apply ℝ (Fin.last d)).comp continuous_snd))

/-- At unit parameter the family is the original affine simplex used for the standard local class. -/
theorem properCycle_scaled_affine_simplex_one (d : ℕ) :
    properCycle_scaled_affine_simplex d 1 = standardAffineSimplex d := by
  funext t j
  simp only [properCycle_scaled_affine_simplex, standardAffineSimplex, one_mul]

/-- The segment between two positive vertex parameters stays positive at every homotopy time. -/
theorem properCycle_positive_vertex_segment (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (t : unitInterval) : 0 < (1 - (t : ℝ)) * a + (t : ℝ) * b := by
  by_cases ht : (t : ℝ) = 1
  · simpa only [ht, sub_self, zero_mul, one_mul, zero_add] using hb
  · have hlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) ha)
      (mul_nonneg t.property.1 (le_of_lt hb))

/-- The actual standard simplex paired with the union of its barycentric boundary faces. -/
def properCycle_affine_boundary_pair (d : ℕ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (StdSimplex ℝ (Fin (d+1))))
    {t | ∃ i : Fin (d+1), t.weights i = 0}

/-- The scaled affine simplex maps its actual boundary into the punctured coordinate space. -/
def properCycle_scaled_affine_pair (d : ℕ) (a : ℝ) (ha : 0 < a) :
    properCycle_affine_boundary_pair d ⟶ puncturedPair ℝ d :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨properCycle_scaled_affine_simplex d a,
      (properCycle_continuous_scaled_affine_simplex d).comp (continuous_const.prodMk continuous_id)⟩)
    (by
      intro t ht
      obtain ⟨i, hi⟩ := ht
      exact properCycle_scaled_affine_simplex_face_ne_zero d a ha t i hi)

/-- Positive changes of the last vertex give a homotopy of the actual relative pairs. -/
def properCycle_scaled_affine_pair_homotopy (d : ℕ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    TopPair.Homotopy (properCycle_scaled_affine_pair d a ha)
      (properCycle_scaled_affine_pair d b hb) where
  fst :=
    { toFun := fun tz => properCycle_scaled_affine_simplex d
        ((1 - (tz.1 : ℝ)) * a + (tz.1 : ℝ) * b) tz.2
      continuous_toFun := by
        exact (properCycle_continuous_scaled_affine_simplex d).comp
          (show Continuous (fun tz : unitInterval × StdSimplex ℝ (Fin (d+1)) =>
            (((1 - (tz.1 : ℝ)) * a + (tz.1 : ℝ) * b), tz.2)) by fun_prop)
      map_zero_left := by intro z; change properCycle_scaled_affine_simplex d _ z = properCycle_scaled_affine_simplex d a z; simp
      map_one_left := by intro z; change properCycle_scaled_affine_simplex d _ z = properCycle_scaled_affine_simplex d b z; simp }
  snd :=
    { toFun := fun tz => ⟨properCycle_scaled_affine_simplex d
        ((1 - (tz.1 : ℝ)) * a + (tz.1 : ℝ) * b) tz.2.val, by
          obtain ⟨i, hi⟩ := tz.2.property
          exact properCycle_scaled_affine_simplex_face_ne_zero d _
            (properCycle_positive_vertex_segment a b ha hb tz.1) _ i hi⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (properCycle_continuous_scaled_affine_simplex d).comp
          (show Continuous (fun tz : unitInterval × {t : StdSimplex ℝ (Fin (d+1)) | ∃ i, t.weights i = 0} =>
            (((1 - (tz.1 : ℝ)) * a + (tz.1 : ℝ) * b), tz.2.val)) by fun_prop)
      map_zero_left := by intro z; apply Subtype.ext; change properCycle_scaled_affine_simplex d _ z.val = properCycle_scaled_affine_simplex d a z.val; simp
      map_one_left := by intro z; apply Subtype.ext; change properCycle_scaled_affine_simplex d _ z.val = properCycle_scaled_affine_simplex d b z.val; simp }
  w := rfl

/-- Every positive vertex parameter induces the same relative homology map as parameter one. -/
theorem properCycle_scaled_affine_pair_homology (d n : ℕ) (a : ℝ) (ha : 0 < a)
    (z : RelativeHomology ℚ (properCycle_affine_boundary_pair d) n) :
    relativeHomologyMap ℚ n (properCycle_scaled_affine_pair d a ha) z =
      relativeHomologyMap ℚ n (properCycle_scaled_affine_pair d 1 zero_lt_one) z :=
  (properCycle_scaled_affine_pair_homotopy d a 1 ha zero_lt_one).relativeHomologyMap_apply_eq n z

end HodgeLean.Foundations.QuotientDuality
