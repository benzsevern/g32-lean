import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.FundamentalClass

/-! # Repeated-vertex simplices for the signed local orientation calculation -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Convexity AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Insert the vertex pattern `i, i+1, i` in place of `i, i+1`. -/
def foldedOrientationVertex (d i : ℕ) (hi : i + 1 < d) (j : Fin (d + 2)) : Fin (d + 1) :=
  if h : j.val ≤ i + 1 then ⟨j.val, by omega⟩
  else if j.val = i + 2 then ⟨i, by omega⟩
  else ⟨j.val - 1, by have := j.isLt; omega⟩

/-- The inserted vertex has precisely the two specified occurrences. -/
theorem foldedOrientationVertex_collision (d i : ℕ) (hi : i + 1 < d)
    (a b : Fin (d + 2)) :
    (foldedOrientationVertex d i hi a).val = (foldedOrientationVertex d i hi b).val ↔
      a.val = b.val ∨ (a.val = i ∧ b.val = i + 2) ∨ (a.val = i + 2 ∧ b.val = i) := by
  unfold foldedOrientationVertex
  split_ifs <;> simp_all <;> omega

#print axioms foldedOrientationVertex_collision

/-- Deleting any vertex other than the repeated pair omits its image from the whole face. -/
theorem foldedOrientationVertex_face_misses (d i : ℕ) (hi : i + 1 < d)
    (a : Fin (d + 2)) (hai : a.val ≠ i) (ha₂ : a.val ≠ i + 2)
    (j : Fin (d + 1)) :
    foldedOrientationVertex d i hi (a.succAbove j) ≠ foldedOrientationVertex d i hi a := by
  intro h
  rcases (foldedOrientationVertex_collision d i hi (a.succAbove j) a).mp
    (congrArg Fin.val h) with h | h | h
  · exact Fin.succAbove_ne a j (Fin.ext h)
  · exact ha₂ h.2
  · exact hai h.2

#print axioms foldedOrientationVertex_face_misses

/-- Deleting the second occurrence recovers the original ordered vertices. -/
theorem foldedOrientationVertex_face_right (d i : ℕ) (hi : i + 1 < d)
    (j : Fin (d + 1)) :
    foldedOrientationVertex d i hi ((⟨i + 2, by omega⟩ : Fin (d + 2)).succAbove j) = j := by
  apply Fin.ext
  simp only [Fin.succAbove]
  split_ifs <;> simp_all [foldedOrientationVertex] <;> split_ifs <;> simp_all [Fin.lt_def, Fin.le_def] <;> omega

#print axioms foldedOrientationVertex_face_right

/-- Deleting the first occurrence exchanges exactly the two adjacent original vertices. -/
theorem foldedOrientationVertex_face_left (d i : ℕ) (hi : i + 1 < d)
    (j : Fin (d + 1)) :
    foldedOrientationVertex d i hi ((⟨i, by omega⟩ : Fin (d + 2)).succAbove j) =
      Equiv.swap (⟨i, by omega⟩ : Fin (d + 1)) ⟨i + 1, by omega⟩ j := by
  apply Fin.ext
  simp only [Fin.succAbove, Equiv.swap_apply_def]
  split_ifs <;> simp_all [foldedOrientationVertex, Fin.ext_iff] <;>
    split_ifs <;> simp_all [Fin.lt_def, Fin.le_def, Fin.ext_iff] <;> omega

#print axioms foldedOrientationVertex_face_left

/-- Every other affine face has an identically zero barycentric coordinate. -/
theorem foldedOrientation_face_weight_zero (d i : ℕ) (hi : i + 1 < d)
    (a : Fin (d + 2)) (hai : a.val ≠ i) (ha₂ : a.val ≠ i + 2)
    (t : StdSimplex ℝ (Fin (d + 1))) :
    (StdSimplex.map (foldedOrientationVertex d i hi) (StdSimplex.map a.succAbove t)).weights
      (foldedOrientationVertex d i hi a) = 0 := by
  classical
  rw [StdSimplex.map_map, StdSimplex.weights_map_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact False.elim (foldedOrientationVertex_face_misses d i hi a hai ha₂ j
    (Finset.mem_filter.mp hj).2)

#print axioms foldedOrientation_face_weight_zero

/-- The affine simplex with the inserted repeated-vertex pattern. -/
def foldedOrientationSimplex (d i : ℕ) (hi : i + 1 < d) :
    C(StdSimplex ℝ (Fin (d + 2)), Fin d → ℝ) where
  toFun t := standardAffineSimplex d (StdSimplex.map (foldedOrientationVertex d i hi) t)
  continuous_toFun := by fun_prop

/-- All faces other than the two distinguished occurrences avoid the actual origin. -/
theorem foldedOrientationSimplex_face_ne_zero (d i : ℕ) (hi : i + 1 < d)
    (a : Fin (d + 2)) (hai : a.val ≠ i) (ha₂ : a.val ≠ i + 2)
    (t : StdSimplex ℝ (Fin (d + 1))) :
    foldedOrientationSimplex d i hi (StdSimplex.map a.succAbove t) ≠ 0 := by
  exact standardAffineSimplex_ne_zero_of_coord_zero d _ (foldedOrientationVertex d i hi a)
    (foldedOrientation_face_weight_zero d i hi a hai ha₂ t)

#print axioms foldedOrientationSimplex_face_ne_zero

/-- The second distinguished face is the original affine orientation simplex. -/
theorem foldedOrientationSimplex_face_right (d i : ℕ) (hi : i + 1 < d)
    (t : StdSimplex ℝ (Fin (d + 1))) :
    foldedOrientationSimplex d i hi
      (StdSimplex.map (⟨i + 2, by omega⟩ : Fin (d + 2)).succAbove t) =
      standardAffineSimplex d t := by
  change standardAffineSimplex d (StdSimplex.map (foldedOrientationVertex d i hi)
    (StdSimplex.map (⟨i + 2, by omega⟩ : Fin (d + 2)).succAbove t)) = _
  simp only [StdSimplex.map_map, foldedOrientationVertex_face_right]
  exact congrArg (standardAffineSimplex d) (StdSimplex.map_id t)

#print axioms foldedOrientationSimplex_face_right

/-- The first distinguished face has exactly the adjacent exchanged vertex ordering. -/
theorem foldedOrientationSimplex_face_left (d i : ℕ) (hi : i + 1 < d)
    (t : StdSimplex ℝ (Fin (d + 1))) :
    foldedOrientationSimplex d i hi
      (StdSimplex.map (⟨i, by omega⟩ : Fin (d + 2)).succAbove t) =
      standardAffineSimplex d (StdSimplex.map
        (Equiv.swap (⟨i, by omega⟩ : Fin (d + 1)) ⟨i + 1, by omega⟩) t) := by
  change standardAffineSimplex d (StdSimplex.map (foldedOrientationVertex d i hi)
    (StdSimplex.map (⟨i, by omega⟩ : Fin (d + 2)).succAbove t)) = _
  simp only [StdSimplex.map_map, foldedOrientationVertex_face_left]

#print axioms foldedOrientationSimplex_face_left

/-- Exchanging the two specified vertices exchanges exactly those real affine coordinates. -/
theorem standardAffineSimplex_adjacent_swap (d i : ℕ) (hi : i + 1 < d)
    (t : StdSimplex ℝ (Fin (d + 1))) :
    standardAffineSimplex d (StdSimplex.map
      (Equiv.swap (⟨i, by omega⟩ : Fin (d + 1)) ⟨i + 1, by omega⟩) t) =
      fun j => standardAffineSimplex d t
        (Equiv.swap (⟨i, by omega⟩ : Fin d) ⟨i + 1, hi⟩ j) := by
  have heval (j : Fin d) :
      Equiv.swap (⟨i, by omega⟩ : Fin (d + 1)) ⟨i + 1, by omega⟩ j.castSucc =
        (Equiv.swap (⟨i, by omega⟩ : Fin d) ⟨i + 1, hi⟩ j).castSucc := by
    apply Fin.ext
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  have hlast : Equiv.swap (⟨i, by omega⟩ : Fin (d + 1)) ⟨i + 1, by omega⟩
      (Fin.last d) = Fin.last d := by
    apply Equiv.swap_apply_of_ne_of_ne <;> intro h <;>
      have hval := congrArg Fin.val h <;> simp only [Fin.val_last] at hval <;> omega
  funext j
  simp only [standardAffineSimplex, StdSimplex.weights_map_apply, Equiv.swap_apply_eq_iff]
  simp [heval, hlast, Finset.sum_filter]

#print axioms standardAffineSimplex_adjacent_swap
end HodgeLean.Foundations.Program.G32Native.EulerModel
