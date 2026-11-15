import HodgeLean.Foundations.Program.BraidCertificateDefs

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem b65b_collision_0 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin 12) (he : b65b_track t 0 = b65b_track t j) : (0 : Fin 12) = j := by
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  fin_cases j <;> first | rfl | (
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at hre <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at him <;>
    linarith [ht.1, ht.2])

set_option maxHeartbeats 400000 in
theorem b65b_collision_1 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin 12) (he : b65b_track t 1 = b65b_track t j) : (1 : Fin 12) = j := by
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  fin_cases j <;> first | rfl | (
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at hre <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at him <;>
    linarith [ht.1, ht.2])

set_option maxHeartbeats 400000 in
theorem b65b_collision_2 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin 12) (he : b65b_track t 2 = b65b_track t j) : (2 : Fin 12) = j := by
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  fin_cases j <;> first | rfl | (
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at hre <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at him <;>
    linarith [ht.1, ht.2])

set_option maxHeartbeats 400000 in
theorem b65b_collision_3 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin 12) (he : b65b_track t 3 = b65b_track t j) : (3 : Fin 12) = j := by
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  fin_cases j <;> first | rfl | (
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at hre <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at him <;>
    linarith [ht.1, ht.2])

set_option maxHeartbeats 400000 in
theorem b65b_collision_4 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin 12) (he : b65b_track t 4 = b65b_track t j) : (4 : Fin 12) = j := by
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  fin_cases j <;> first | rfl | (
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at hre <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at him <;>
    linarith [ht.1, ht.2])

set_option maxHeartbeats 400000 in
theorem b65b_collision_5 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin 12) (he : b65b_track t 5 = b65b_track t j) : (5 : Fin 12) = j := by
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  fin_cases j <;> first | rfl | (
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at hre <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at him <;>
    linarith [ht.1, ht.2])

set_option maxHeartbeats 400000 in
theorem b65b_collision_6 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin 12) (he : b65b_track t 6 = b65b_track t j) : (6 : Fin 12) = j := by
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  fin_cases j <;> first | rfl | (
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at hre <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at him <;>
    linarith [ht.1, ht.2])

set_option maxHeartbeats 400000 in
theorem b65b_collision_7 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin 12) (he : b65b_track t 7 = b65b_track t j) : (7 : Fin 12) = j := by
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  fin_cases j <;> first | rfl | (
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at hre <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at him <;>
    linarith [ht.1, ht.2])

set_option maxHeartbeats 400000 in
theorem b65b_collision_8 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin 12) (he : b65b_track t 8 = b65b_track t j) : (8 : Fin 12) = j := by
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  fin_cases j <;> first | rfl | (
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at hre <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at him <;>
    linarith [ht.1, ht.2])

set_option maxHeartbeats 400000 in
theorem b65b_collision_9 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin 12) (he : b65b_track t 9 = b65b_track t j) : (9 : Fin 12) = j := by
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  fin_cases j <;> first | rfl | (
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at hre <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at him <;>
    linarith [ht.1, ht.2])

set_option maxHeartbeats 400000 in
theorem b65b_collision_10 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin 12) (he : b65b_track t 10 = b65b_track t j) : (10 : Fin 12) = j := by
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  fin_cases j <;> first | rfl | (
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at hre <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at him <;>
    linarith [ht.1, ht.2])

set_option maxHeartbeats 400000 in
theorem b65b_collision_11 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin 12) (he : b65b_track t 11 = b65b_track t j) : (11 : Fin 12) = j := by
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  fin_cases j <;> first | rfl | (
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at hre <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im] at him <;>
    linarith [ht.1, ht.2])

set_option maxHeartbeats 400000 in
theorem b65b_track_bound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin 12) :
    ‖b65b_track t i - (-11/2 : ℂ)‖ < 10 := by
  have hmul : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  have hsq : ‖b65b_track t i - (-11/2 : ℂ)‖ ^ 2 < 100 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    fin_cases i <;>
      norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
        Complex.mul_re, Complex.mul_im] <;>
      nlinarith [ht.1, ht.2]
  nlinarith [norm_nonneg (b65b_track t i - (-11/2 : ℂ))]

set_option maxHeartbeats 400000 in
theorem b65b_event_0 (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin 12) (hij : (0 : Fin 12) < j) :
    (((b65b_track t 0 - (-11/2 + 10 * Complex.I)) *
        star (b65b_track t j - (-11/2 + 10 * Complex.I))).im = 0 ↔
      ((0 : Fin 12) = 8 ∧ j = 10 ∧ t = (63109263/2063109263 : ℝ)) ∨
      ((0 : Fin 12) = 9 ∧ j = 10 ∧ t = (48671253/298671253 : ℝ))) := by
  have hmul : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  fin_cases j <;> norm_num at hij <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;>
    (try constructor) <;> intro h <;>
    nlinarith [ht.1, ht.2, sq_nonneg t, sq_nonneg (1-t)]

set_option maxHeartbeats 400000 in
theorem b65b_event_1 (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin 12) (hij : (1 : Fin 12) < j) :
    (((b65b_track t 1 - (-11/2 + 10 * Complex.I)) *
        star (b65b_track t j - (-11/2 + 10 * Complex.I))).im = 0 ↔
      ((1 : Fin 12) = 8 ∧ j = 10 ∧ t = (63109263/2063109263 : ℝ)) ∨
      ((1 : Fin 12) = 9 ∧ j = 10 ∧ t = (48671253/298671253 : ℝ))) := by
  have hmul : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  fin_cases j <;> norm_num at hij <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;>
    (try constructor) <;> intro h <;>
    nlinarith [ht.1, ht.2, sq_nonneg t, sq_nonneg (1-t)]

set_option maxHeartbeats 400000 in
theorem b65b_event_2 (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin 12) (hij : (2 : Fin 12) < j) :
    (((b65b_track t 2 - (-11/2 + 10 * Complex.I)) *
        star (b65b_track t j - (-11/2 + 10 * Complex.I))).im = 0 ↔
      ((2 : Fin 12) = 8 ∧ j = 10 ∧ t = (63109263/2063109263 : ℝ)) ∨
      ((2 : Fin 12) = 9 ∧ j = 10 ∧ t = (48671253/298671253 : ℝ))) := by
  have hmul : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  fin_cases j <;> norm_num at hij <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;>
    (try constructor) <;> intro h <;>
    nlinarith [ht.1, ht.2, sq_nonneg t, sq_nonneg (1-t)]

set_option maxHeartbeats 400000 in
theorem b65b_event_3 (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin 12) (hij : (3 : Fin 12) < j) :
    (((b65b_track t 3 - (-11/2 + 10 * Complex.I)) *
        star (b65b_track t j - (-11/2 + 10 * Complex.I))).im = 0 ↔
      ((3 : Fin 12) = 8 ∧ j = 10 ∧ t = (63109263/2063109263 : ℝ)) ∨
      ((3 : Fin 12) = 9 ∧ j = 10 ∧ t = (48671253/298671253 : ℝ))) := by
  have hmul : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  fin_cases j <;> norm_num at hij <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;>
    (try constructor) <;> intro h <;>
    nlinarith [ht.1, ht.2, sq_nonneg t, sq_nonneg (1-t)]

set_option maxHeartbeats 400000 in
theorem b65b_event_4 (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin 12) (hij : (4 : Fin 12) < j) :
    (((b65b_track t 4 - (-11/2 + 10 * Complex.I)) *
        star (b65b_track t j - (-11/2 + 10 * Complex.I))).im = 0 ↔
      ((4 : Fin 12) = 8 ∧ j = 10 ∧ t = (63109263/2063109263 : ℝ)) ∨
      ((4 : Fin 12) = 9 ∧ j = 10 ∧ t = (48671253/298671253 : ℝ))) := by
  have hmul : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  fin_cases j <;> norm_num at hij <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;>
    (try constructor) <;> intro h <;>
    nlinarith [ht.1, ht.2, sq_nonneg t, sq_nonneg (1-t)]

set_option maxHeartbeats 400000 in
theorem b65b_event_5 (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin 12) (hij : (5 : Fin 12) < j) :
    (((b65b_track t 5 - (-11/2 + 10 * Complex.I)) *
        star (b65b_track t j - (-11/2 + 10 * Complex.I))).im = 0 ↔
      ((5 : Fin 12) = 8 ∧ j = 10 ∧ t = (63109263/2063109263 : ℝ)) ∨
      ((5 : Fin 12) = 9 ∧ j = 10 ∧ t = (48671253/298671253 : ℝ))) := by
  have hmul : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  fin_cases j <;> norm_num at hij <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;>
    (try constructor) <;> intro h <;>
    nlinarith [ht.1, ht.2, sq_nonneg t, sq_nonneg (1-t)]

set_option maxHeartbeats 400000 in
theorem b65b_event_6 (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin 12) (hij : (6 : Fin 12) < j) :
    (((b65b_track t 6 - (-11/2 + 10 * Complex.I)) *
        star (b65b_track t j - (-11/2 + 10 * Complex.I))).im = 0 ↔
      ((6 : Fin 12) = 8 ∧ j = 10 ∧ t = (63109263/2063109263 : ℝ)) ∨
      ((6 : Fin 12) = 9 ∧ j = 10 ∧ t = (48671253/298671253 : ℝ))) := by
  have hmul : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  fin_cases j <;> norm_num at hij <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;>
    (try constructor) <;> intro h <;>
    nlinarith [ht.1, ht.2, sq_nonneg t, sq_nonneg (1-t)]

set_option maxHeartbeats 400000 in
theorem b65b_event_7 (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin 12) (hij : (7 : Fin 12) < j) :
    (((b65b_track t 7 - (-11/2 + 10 * Complex.I)) *
        star (b65b_track t j - (-11/2 + 10 * Complex.I))).im = 0 ↔
      ((7 : Fin 12) = 8 ∧ j = 10 ∧ t = (63109263/2063109263 : ℝ)) ∨
      ((7 : Fin 12) = 9 ∧ j = 10 ∧ t = (48671253/298671253 : ℝ))) := by
  have hmul : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  fin_cases j <;> norm_num at hij <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;>
    (try constructor) <;> intro h <;>
    nlinarith [ht.1, ht.2, sq_nonneg t, sq_nonneg (1-t)]

set_option maxHeartbeats 400000 in
theorem b65b_event_8 (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin 12) (hij : (8 : Fin 12) < j) :
    (((b65b_track t 8 - (-11/2 + 10 * Complex.I)) *
        star (b65b_track t j - (-11/2 + 10 * Complex.I))).im = 0 ↔
      ((8 : Fin 12) = 8 ∧ j = 10 ∧ t = (63109263/2063109263 : ℝ)) ∨
      ((8 : Fin 12) = 9 ∧ j = 10 ∧ t = (48671253/298671253 : ℝ))) := by
  have hmul : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  fin_cases j <;> norm_num at hij <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;>
    (try constructor) <;> intro h <;>
    nlinarith [ht.1, ht.2, sq_nonneg t, sq_nonneg (1-t)]

set_option maxHeartbeats 400000 in
theorem b65b_event_9 (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin 12) (hij : (9 : Fin 12) < j) :
    (((b65b_track t 9 - (-11/2 + 10 * Complex.I)) *
        star (b65b_track t j - (-11/2 + 10 * Complex.I))).im = 0 ↔
      ((9 : Fin 12) = 8 ∧ j = 10 ∧ t = (63109263/2063109263 : ℝ)) ∨
      ((9 : Fin 12) = 9 ∧ j = 10 ∧ t = (48671253/298671253 : ℝ))) := by
  have hmul : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  fin_cases j <;> norm_num at hij <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;>
    (try constructor) <;> intro h <;>
    nlinarith [ht.1, ht.2, sq_nonneg t, sq_nonneg (1-t)]

set_option maxHeartbeats 400000 in
theorem b65b_event_10 (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin 12) (hij : (10 : Fin 12) < j) :
    (((b65b_track t 10 - (-11/2 + 10 * Complex.I)) *
        star (b65b_track t j - (-11/2 + 10 * Complex.I))).im = 0 ↔
      ((10 : Fin 12) = 8 ∧ j = 10 ∧ t = (63109263/2063109263 : ℝ)) ∨
      ((10 : Fin 12) = 9 ∧ j = 10 ∧ t = (48671253/298671253 : ℝ))) := by
  have hmul : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  fin_cases j <;> norm_num at hij <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;>
    (try constructor) <;> intro h <;>
    nlinarith [ht.1, ht.2, sq_nonneg t, sq_nonneg (1-t)]

set_option maxHeartbeats 400000 in
theorem b65b_event_11 (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin 12) (hij : (11 : Fin 12) < j) :
    (((b65b_track t 11 - (-11/2 + 10 * Complex.I)) *
        star (b65b_track t j - (-11/2 + 10 * Complex.I))).im = 0 ↔
      ((11 : Fin 12) = 8 ∧ j = 10 ∧ t = (63109263/2063109263 : ℝ)) ∨
      ((11 : Fin 12) = 9 ∧ j = 10 ∧ t = (48671253/298671253 : ℝ))) := by
  have hmul : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  fin_cases j <;> norm_num at hij <;>
    norm_num [b65b_track, b65b_vertex0, b65b_vertex1,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;>
    (try constructor) <;> intro h <;>
    nlinarith [ht.1, ht.2, sq_nonneg t, sq_nonneg (1-t)]

end HodgeLean.Foundations.Program
