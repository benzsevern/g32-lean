import HodgeLean.Foundations.Program.BraidCertificateReplay
import HodgeLean.Foundations.Program.BraidCertificateGeometry
import HodgeLean.Foundations.Program.BraidCertificateIntervals

/-! # Braid-certificate arithmetic replay, track geometry and interval bounds. -/

noncomputable section
namespace HodgeLean.Foundations.Program

def b65b_evalIn {G : Type*} [Group G] (D : Fin 3 → G)
    (w : List (Fin 3 × ℤ)) : G :=
  (w.reverse.map (fun a ↦ D a.1 ^ a.2)).prod

theorem b65b_path_identity {G : Type*} [Group G] (D : Fin 3 → G) :
    b4_braid 2 3 (b4_braid 3 4 (fun i ↦ b65b_evalIn D (b65b_initialWords i))) =
      (fun i ↦ b65b_evalIn D (b65b_finalWords i)) := by
  funext i
  fin_cases i <;>
    norm_num [b4_braid, b65b_initialWords, b65b_finalWords,
      b65b_evalIn, Equiv.swap_apply_def] <;> group

theorem b65b_literal_matrices_aux  :
    (∀ i, b4b_toMatrix (b65b_initial i) = b65b_decode (b65b_initialIntegral i)) ∧
    (∀ i, b4b_toMatrix (b65b_final i) = b65b_decode (b65b_finalIntegral i)) := by
  constructor
  · intro i
    have h := congrArg Units.val (b65b_realize_eval (b65b_initialWords i))
    change (b65b_qEval (b65b_initialWords i)).val.map b65b_embedding =
      b4b_toMatrix (b65b_initial i) at h
    rw [b65b_qLiteralInitial, b65b_realize_decode] at h
    exact h.symm
  · intro i
    have h := congrArg Units.val (b65b_realize_eval (b65b_finalWords i))
    change (b65b_qEval (b65b_finalWords i)).val.map b65b_embedding =
      b4b_toMatrix (b65b_final i) at h
    rw [b65b_qLiteralFinal, b65b_realize_decode] at h
    exact h.symm

theorem b65b_replay_aux  :
    b65s_word b65b_word b65s_columnRoot =
      b4_conjTuple (b4b_generators 1)⁻¹ b65b_final ∧
    ∀ i, b4b_toMatrix (b65s_word b65b_word b65s_columnRoot i) =
      b4b_toMatrix ((b4b_generators 1)⁻¹) *
        b65b_decode (b65b_finalIntegral i) * b4b_toMatrix (b4b_generators 1) := by
  have hm : ∀ i, b4b_toMatrix (b65s_word b65b_word b65s_columnRoot i) =
      b4b_toMatrix ((b4b_generators 1)⁻¹) *
        b65b_decode (b65b_finalIntegral i) * b4b_toMatrix (b4b_generators 1) := by
    intro i
    have hq := b65b_qWord_realize b65b_word (by decide +kernel)
      b65b_qColumnRoot b65s_columnRoot b65b_realize_columnRoot i
    rw [b65b_replay_calculation] at hq
    have he : b65b_replayStage43 i = (b65b_qGenerators 1)⁻¹ *
        b65b_qEval (b65b_finalWords i) * b65b_qGenerators 1 := by
      apply Units.ext
      change (b65b_replayStage43 i).val = (b65b_qGenerators 1).inv *
        (b65b_qEval (b65b_finalWords i)).val * (b65b_qGenerators 1).val
      rw [b65b_qLiteralFinal]
      exact b65b_replay_endpoint i
    rw [he] at hq
    simp only [map_mul, map_inv, b65b_realize_generators,
      b65b_realize_eval] at hq
    have h := congrArg Units.val hq.symm
    change b4b_toMatrix (b65s_word b65b_word b65s_columnRoot i) =
      b4b_toMatrix ((b4b_generators 1)⁻¹) * b4b_toMatrix (b65b_final i) *
        b4b_toMatrix (b4b_generators 1) at h
    rw [b65b_literal_matrices_aux.2 i] at h
    exact h
  refine ⟨?_, hm⟩
  funext i
  apply Subtype.ext
  change b4b_toMatrix (b65s_word b65b_word b65s_columnRoot i) =
    b4b_toMatrix ((b4b_generators 1)⁻¹ * b65b_final i * ((b4b_generators 1)⁻¹)⁻¹)
  rw [map_mul, map_mul, inv_inv, b65b_literal_matrices_aux.2 i]
  exact hm i

theorem b65b_path_replay_aux  :
    b65s_word b65b_pathWord b65b_initial = b65b_final := by
  exact b65b_path_identity b65b_cut

theorem b65b_component_aux  :
    b4_SameComponent b65s_columnRoot b65b_final := by
  have h := (b65s_word_orbit b65b_word b65s_columnRoot).1
  rw [b65b_replay_aux.1] at h
  refine Relation.EqvGen.trans _ _ _ h ?_
  apply Relation.EqvGen.rel
  left
  refine ⟨b4b_generators 1, ?_⟩
  funext i
  simp [b4_conjTuple, mul_assoc]

set_option maxHeartbeats 400000 in
theorem b65b_path_geometry_aux  :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (b65b_track t)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i, ‖b65b_track t i - (-11/2 : ℂ)‖ < 10) ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ i j : Fin 12, i < j →
      (((b65b_track t i - (-11/2 + 10 * Complex.I)) *
          star (b65b_track t j - (-11/2 + 10 * Complex.I))).im = 0 ↔
        (i = 8 ∧ j = 10 ∧ t = (63109263/2063109263 : ℝ)) ∨
        (i = 9 ∧ j = 10 ∧ t = (48671253/298671253 : ℝ))) := by
  constructor
  · intro t ht i j he
    fin_cases i
    · exact b65b_collision_0 t ht j he
    · exact b65b_collision_1 t ht j he
    · exact b65b_collision_2 t ht j he
    · exact b65b_collision_3 t ht j he
    · exact b65b_collision_4 t ht j he
    · exact b65b_collision_5 t ht j he
    · exact b65b_collision_6 t ht j he
    · exact b65b_collision_7 t ht j he
    · exact b65b_collision_8 t ht j he
    · exact b65b_collision_9 t ht j he
    · exact b65b_collision_10 t ht j he
    · exact b65b_collision_11 t ht j he
  refine ⟨b65b_track_bound, ?_⟩
  intro t ht i j hij
  fin_cases i
  · exact b65b_event_0 t ht j hij
  · exact b65b_event_1 t ht j hij
  · exact b65b_event_2 t ht j hij
  · exact b65b_event_3 t ht j hij
  · exact b65b_event_4 t ht j hij
  · exact b65b_event_5 t ht j hij
  · exact b65b_event_6 t ht j hij
  · exact b65b_event_7 t ht j hij
  · exact b65b_event_8 t ht j hij
  · exact b65b_event_9 t ht j hij
  · exact b65b_event_10 t ht j hij
  · exact b65b_event_11 t ht j hij


set_option maxHeartbeats 400000 in
set_option maxRecDepth 10000 in
theorem b65b_rational_enclosures_aux  :
    (∀ i : Fin 12, 0 < b65b_radius i ∧ b65b_radius i ≤ 1/4) ∧
    (∀ i : Fin 12, ∀ a b : Fin 2,
      (b65b_enclosure i ⟨a.val, by omega⟩ - (b65b_vertex0 i).1)^2 +
        (b65b_enclosure i ⟨b.val + 2, by omega⟩ - (b65b_vertex0 i).2)^2 < (b65b_radius i)^2) ∧
    ∀ i j : Fin 12, i < j →
      0 < b65b_dot i j ∧
      (b65b_cross i j)^2 > (b65b_radius i)^2 * b65b_dot j j +
        (b65b_radius j)^2 * b65b_dot i i +
        b65b_radius i * b65b_radius j * (b65b_dot i i + b65b_dot j j) := by
  constructor
  · intro i
    fin_cases i <;> norm_num [b65b_radius]
  constructor
  · intro i a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      norm_num [b65b_enclosure, b65b_vertex0, b65b_radius]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | omega | norm_num [b65b_dot, b65b_cross, b65b_vertex0, b65b_radius]


theorem b65b_normalization_enclosure_aux :
    ∀ (k : Fin 12) (z : ℂ) (a b : ℝ),
      |z.re - ((b65b_boxCentre k).1 : ℝ)| ≤ (1/10000 : ℝ) →
      |z.im - ((b65b_boxCentre k).2 : ℝ)| ≤ (1/10000 : ℝ) →
      |a - ((b65b_boxCentre 0).1 : ℝ)| ≤ (1/10000 : ℝ) →
      |b - ((b65b_boxCentre 6).1 : ℝ)| ≤ (1/10000 : ℝ) →
      z * ((b : ℂ) - a) ≠ 0 ∧
      (b65s_normalize a b z).re ∈ Set.Icc
        (b65b_enclosure (b65b_boxIndex k) 0 : ℝ)
        (b65b_enclosure (b65b_boxIndex k) 1 : ℝ) ∧
      (b65s_normalize a b z).im ∈ Set.Icc
        (b65b_enclosure (b65b_boxIndex k) 2 : ℝ)
        (b65b_enclosure (b65b_boxIndex k) 3 : ℝ) ∧
      ‖b65s_normalize a b z - b65b_track 0 (b65b_boxIndex k)‖ <
        (b65b_radius (b65b_boxIndex k) : ℝ) := by
  intro k z a b hzr hzi ha hb
  have hi := b65b_normalization_interval k z a b hzr hzi ha hb
  refine ⟨b65b_normalization_denominator k z a b hzr ha hb, hi.1, hi.2, ?_⟩
  let i := b65b_boxIndex k
  have hr : (0 : ℝ) < b65b_radius i := by
    exact_mod_cast (b65b_rational_enclosures_aux.1 i).1
  have ht : b65b_track 0 i =
      (((b65b_vertex0 i).1 : ℝ) : ℂ) +
        (((b65b_vertex0 i).2 : ℝ) : ℂ) * Complex.I := by simp [b65b_track]
  rw [ht]
  apply b65b_rectangle_bound _ _ _ _ _ _ _ _ hr hi.1 hi.2
  · exact_mod_cast (b65b_rational_enclosures_aux.2.1 i 0 0)
  · exact_mod_cast (b65b_rational_enclosures_aux.2.1 i 0 1)
  · exact_mod_cast (b65b_rational_enclosures_aux.2.1 i 1 0)
  · exact_mod_cast (b65b_rational_enclosures_aux.2.1 i 1 1)

end HodgeLean.Foundations.Program
