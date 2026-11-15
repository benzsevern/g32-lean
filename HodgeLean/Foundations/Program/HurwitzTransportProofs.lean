import HodgeLean.Foundations.Program.HurwitzTransportDefs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Antilipschitz

/-! # B6-2a: topological transport of Hurwitz covers

Implication from a normalized configuration and, for covering statements, an existing
finite-group quotient covering to local topological transport. Analytic family charts,
ramification filling, and comparison to selected compact fibres are later tasks.
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.Program

private theorem b6t_radius_pos (b : Fin 10 → ℂ) : 0 < b6t_radius b := by
  simp only [b6t_radius]
  positivity

private theorem homeomorph_add_of_contracting {g : ℂ → ℂ} {K : NNReal}
    (hg : ContractingWith K g) :
    ∃ e : ℂ ≃ₜ ℂ, ∀ z, e z = z + g z := by
  let f : ℂ → ℂ := fun z ↦ z + g z
  have hf_cont : Continuous f := continuous_id.add hg.toLipschitzWith.continuous
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hdist : dist x y = dist (g x) (g y) := by
      simp only [dist_eq_norm]
      rw [show x - y = -(g x - g y) by dsimp [f] at hxy; linear_combination hxy]
      rw [norm_neg]
    have hle := hg.dist_le_mul x y
    rw [← hdist] at hle
    by_contra hne
    have hd : 0 < dist x y := dist_pos.mpr hne
    have hK : (K : ℝ) < 1 := hg.1
    nlinarith
  have hf_surj : Function.Surjective f := by
    intro y
    let q : ℂ → ℂ := fun z ↦ y - g z
    have hq : ContractingWith K q := by
      refine ⟨hg.1, LipschitzWith.of_dist_le_mul fun x z ↦ ?_⟩
      calc
        dist (q x) (q z) = dist (g x) (g z) := by
          simp only [dist_eq_norm]
          rw [show q x - q z = -(g x - g z) by simp [q], norm_neg]
        _ ≤ (K : ℝ) * dist x z := hg.dist_le_mul x z
    let x := hq.fixedPoint q
    have hx : q x = x := hq.fixedPoint_isFixedPt
    refine ⟨x, ?_⟩
    dsimp [f]
    dsimp [q] at hx
    exact eq_of_sub_eq_zero (by linear_combination -hx)
  have hf_anti : AntilipschitzWith ⟨(1 - (K : ℝ))⁻¹, inv_nonneg.mpr (sub_nonneg.mpr hg.1.le)⟩ f := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    have htri : dist x y ≤ dist (f x) (f y) + dist (g x) (g y) := by
      calc
        dist x y = dist (f x - g x) (f y - g y) := by simp [f]
        _ ≤ dist (f x) (f y) + dist (g x) (g y) := dist_sub_sub_le _ _ _ _
    have hgxy := hg.dist_le_mul x y
    have hpos : 0 < 1 - (K : ℝ) := hg.one_sub_K_pos
    change dist x y ≤ (1 - (K : ℝ))⁻¹ * dist (f x) (f y)
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ hpos).2
    nlinarith
  let e := (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).toHomeomorphOfIsInducing
    (hf_anti.isInducing hf_cont)
  exact ⟨e, fun z ↦ rfl⟩

private def b6t_singleShift (b t : Fin 10 → ℂ) (i : Fin 10) (z : ℂ) : ℂ :=
  (max 0 (1 - dist z (b i) / b6t_radius b)) • (t i - b i)

private theorem b6t_singleShift_contracting (b t : Fin 10 → ℂ) (i : Fin 10)
    (hi : dist (t i) (b i) < b6t_radius b) :
    ∃ K : NNReal, ContractingWith K (b6t_singleShift b t i) := by
  have hr : 0 < b6t_radius b := b6t_radius_pos b
  let K : NNReal := ⟨‖t i - b i‖ / b6t_radius b, div_nonneg (norm_nonneg _) hr.le⟩
  refine ⟨K, ?_, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  · change ‖t i - b i‖ / b6t_radius b < 1
    rw [div_lt_one hr]
    simpa [dist_eq_norm] using hi
  · let ax : ℝ := max 0 (1 - dist x (b i) / b6t_radius b)
    let ay : ℝ := max 0 (1 - dist y (b i) / b6t_radius b)
    have hmax : |ax - ay| ≤
        |(1 - dist x (b i) / b6t_radius b) -
          (1 - dist y (b i) / b6t_radius b)| := by
      exact (abs_max_sub_max_le_max 0 _ 0 _).trans (by simp)
    have hdist : |dist y (b i) - dist x (b i)| ≤ dist x y := by
      simpa [dist_comm] using abs_dist_sub_le y x (b i)
    have hscalar : |ax - ay| ≤ dist x y / b6t_radius b := by
      calc
        |ax - ay| ≤ |(1 - dist x (b i) / b6t_radius b) -
            (1 - dist y (b i) / b6t_radius b)| := hmax
        _ = |dist y (b i) - dist x (b i)| / b6t_radius b := by
          rw [show (1 - dist x (b i) / b6t_radius b) -
            (1 - dist y (b i) / b6t_radius b) =
              (dist y (b i) - dist x (b i)) / b6t_radius b by ring]
          rw [abs_div, abs_of_pos hr]
        _ ≤ dist x y / b6t_radius b := (div_le_div_iff_of_pos_right hr).2 hdist
    change dist (ax • (t i - b i)) (ay • (t i - b i)) ≤ (K : ℝ) * dist x y
    rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
    change |ax - ay| * ‖t i - b i‖ ≤ (‖t i - b i‖ / b6t_radius b) * dist x y
    calc
      |ax - ay| * ‖t i - b i‖ ≤ (dist x y / b6t_radius b) * ‖t i - b i‖ :=
        mul_le_mul_of_nonneg_right hscalar (norm_nonneg _)
      _ = (‖t i - b i‖ / b6t_radius b) * dist x y := by ring

private theorem b6t_singleShift_eq_zero_of_not_mem (b t : Fin 10 → ℂ) (i : Fin 10)
    {z : ℂ} (hz : z ∉ Metric.closedBall (b i) (b6t_radius b)) :
    b6t_singleShift b t i z = 0 := by
  have hd : b6t_radius b < dist z (b i) := by
    simpa [Metric.mem_closedBall, not_le] using hz
  have hs : 1 - dist z (b i) / b6t_radius b < 0 := by
    exact sub_neg.mpr ((lt_div_iff₀ (b6t_radius_pos b)).2 (by simpa using hd))
  simp [b6t_singleShift, max_eq_left hs.le]

private theorem b6t_singleMap_maps_closedBall (b t : Fin 10 → ℂ) (i : Fin 10)
    (hi : dist (t i) (b i) < b6t_radius b) {z : ℂ}
    (hz : z ∈ Metric.closedBall (b i) (b6t_radius b)) :
    z + b6t_singleShift b t i z ∈ Metric.closedBall (b i) (b6t_radius b) := by
  have hr : 0 < b6t_radius b := b6t_radius_pos b
  have hzle : dist z (b i) ≤ b6t_radius b := hz
  have hsnonneg : 0 ≤ 1 - dist z (b i) / b6t_radius b :=
    sub_nonneg.mpr ((div_le_one hr).2 hzle)
  rw [Metric.mem_closedBall, dist_eq_norm]
  rw [b6t_singleShift, max_eq_right hsnonneg]
  have hnormd : ‖t i - b i‖ < b6t_radius b := by
    simpa [dist_eq_norm, norm_sub_rev] using hi
  calc
    ‖z + (1 - dist z (b i) / b6t_radius b) • (t i - b i) - b i‖
        ≤ ‖z - b i‖ + ‖(1 - dist z (b i) / b6t_radius b) • (t i - b i)‖ := by
          convert norm_add_le (z - b i)
            ((1 - dist z (b i) / b6t_radius b) • (t i - b i)) using 1 <;> ring
    _ = dist z (b i) + (1 - dist z (b i) / b6t_radius b) * ‖t i - b i‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsnonneg, dist_eq_norm]
    _ ≤ b6t_radius b := by
      have hs : 0 ≤ 1 - dist z (b i) / b6t_radius b := hsnonneg
      calc
        dist z (b i) + (1 - dist z (b i) / b6t_radius b) * ‖t i - b i‖ ≤
            dist z (b i) + (1 - dist z (b i) / b6t_radius b) * b6t_radius b := by
          gcongr
        _ = b6t_radius b := by field_simp; ring

private noncomputable def b6t_singleHomeomorph (b t : Fin 10 → ℂ) (i : Fin 10)
    (hi : dist (t i) (b i) < b6t_radius b) : ℂ ≃ₜ ℂ :=
  Classical.choose (homeomorph_add_of_contracting
    (Classical.choose_spec (b6t_singleShift_contracting b t i hi)))

private theorem b6t_singleHomeomorph_apply (b t : Fin 10 → ℂ) (i : Fin 10)
    (hi : dist (t i) (b i) < b6t_radius b) (z : ℂ) :
    b6t_singleHomeomorph b t i hi z = z + b6t_singleShift b t i z :=
  Classical.choose_spec (homeomorph_add_of_contracting
    (Classical.choose_spec (b6t_singleShift_contracting b t i hi))) z

private theorem b6t_singleHomeomorph_eq_self_of_not_mem (b t : Fin 10 → ℂ)
    (i : Fin 10) (hi : dist (t i) (b i) < b6t_radius b) {z : ℂ}
    (hz : z ∉ Metric.closedBall (b i) (b6t_radius b)) :
    b6t_singleHomeomorph b t i hi z = z := by
  rw [b6t_singleHomeomorph_apply, b6t_singleShift_eq_zero_of_not_mem b t i hz, add_zero]

private theorem b6t_singleHomeomorph_maps_closedBall (b t : Fin 10 → ℂ)
    (i : Fin 10) (hi : dist (t i) (b i) < b6t_radius b) {z : ℂ}
    (hz : z ∈ Metric.closedBall (b i) (b6t_radius b)) :
    b6t_singleHomeomorph b t i hi z ∈ Metric.closedBall (b i) (b6t_radius b) := by
  rw [b6t_singleHomeomorph_apply]
  exact b6t_singleMap_maps_closedBall b t i hi hz

private theorem b6t_radius_lt_quarter_of_inv_le (b : Fin 10 → ℂ) (x : ℝ)
    (hx : 0 < x) (hterm : x⁻¹ ≤ ∑ k : Fin 10, (‖b k‖⁻¹ + ‖b k - 1‖⁻¹ +
      ∑ j : Fin 10, if k = j then 0 else (dist (b k) (b j))⁻¹)) :
    b6t_radius b < x / 4 := by
  have hden : 4 * x⁻¹ < 4 * (1 + ∑ k : Fin 10, (‖b k‖⁻¹ +
      ‖b k - 1‖⁻¹ + ∑ j : Fin 10, if k = j then 0 else (dist (b k) (b j))⁻¹)) := by
    nlinarith
  rw [b6t_radius]
  have hinv := (inv_lt_inv₀
    (by positivity : 0 < (4 : ℝ) * (1 + ∑ k : Fin 10, (‖b k‖⁻¹ +
      ‖b k - 1‖⁻¹ + ∑ j : Fin 10, if k = j then 0 else (dist (b k) (b j))⁻¹)))
    (by positivity : 0 < (4 : ℝ) * x⁻¹)).2 hden
  rw [show ((4 : ℝ) * x⁻¹)⁻¹ = x / 4 by field_simp] at hinv
  exact hinv

private theorem b6t_radius_lt_norm_quarter (b : Fin 10 → ℂ) (i : Fin 10)
    (hi : b i ≠ 0) : b6t_radius b < ‖b i‖ / 4 := by
  have hnorm : 0 < ‖b i‖ := norm_pos_iff.mpr hi
  have hnonneg (k : Fin 10) : 0 ≤ ‖b k‖⁻¹ + ‖b k - 1‖⁻¹ +
      ∑ j : Fin 10, if k = j then 0 else (dist (b k) (b j))⁻¹ := by
    exact add_nonneg (add_nonneg (inv_nonneg.mpr (norm_nonneg _)) (inv_nonneg.mpr (norm_nonneg _)))
      (Finset.sum_nonneg fun j _ ↦ by split <;> positivity)
  have hterm : ‖b i‖⁻¹ ≤ ∑ k : Fin 10, (‖b k‖⁻¹ + ‖b k - 1‖⁻¹ +
      ∑ j : Fin 10, if k = j then 0 else (dist (b k) (b j))⁻¹) := by
    calc
      ‖b i‖⁻¹ ≤ ‖b i‖⁻¹ + ‖b i - 1‖⁻¹ +
          ∑ j : Fin 10, if i = j then 0 else (dist (b i) (b j))⁻¹ := by
        have hs : 0 ≤ ∑ j : Fin 10, if i = j then 0 else (dist (b i) (b j))⁻¹ :=
          Finset.sum_nonneg fun j _ ↦ by split <;> positivity
        have hn : 0 ≤ ‖b i - 1‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
        linarith
      _ ≤ ∑ k : Fin 10, (‖b k‖⁻¹ + ‖b k - 1‖⁻¹ +
          ∑ j : Fin 10, if k = j then 0 else (dist (b k) (b j))⁻¹) := by
        exact Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin 10 ↦
          ‖b k‖⁻¹ + ‖b k - 1‖⁻¹ + ∑ j : Fin 10,
            if k = j then 0 else (dist (b k) (b j))⁻¹) (fun k _ ↦ hnonneg k) (by simp)
  have hden : 4 * ‖b i‖⁻¹ < 4 * (1 + ∑ k : Fin 10, (‖b k‖⁻¹ +
      ‖b k - 1‖⁻¹ + ∑ j : Fin 10, if k = j then 0 else (dist (b k) (b j))⁻¹)) := by
    nlinarith
  rw [b6t_radius]
  have hinv := (inv_lt_inv₀
    (by positivity : 0 < (4 : ℝ) * (1 + ∑ k : Fin 10, (‖b k‖⁻¹ +
      ‖b k - 1‖⁻¹ + ∑ j : Fin 10, if k = j then 0 else (dist (b k) (b j))⁻¹)))
    (by positivity : 0 < (4 : ℝ) * ‖b i‖⁻¹)).2 hden
  rw [show ((4 : ℝ) * ‖b i‖⁻¹)⁻¹ = ‖b i‖ / 4 by field_simp] at hinv
  exact hinv

private theorem b6t_radius_lt_norm_sub_one_quarter (b : Fin 10 → ℂ) (i : Fin 10)
    (hi : b i ≠ 1) : b6t_radius b < ‖b i - 1‖ / 4 := by
  have hnonneg (k : Fin 10) : 0 ≤ ‖b k‖⁻¹ + ‖b k - 1‖⁻¹ +
      ∑ j : Fin 10, if k = j then 0 else (dist (b k) (b j))⁻¹ := by
    exact add_nonneg (add_nonneg (inv_nonneg.mpr (norm_nonneg _)) (inv_nonneg.mpr (norm_nonneg _)))
      (Finset.sum_nonneg fun j _ ↦ by split <;> positivity)
  apply b6t_radius_lt_quarter_of_inv_le b ‖b i - 1‖ (norm_pos_iff.mpr (sub_ne_zero.mpr hi))
  calc
    ‖b i - 1‖⁻¹ ≤ ‖b i‖⁻¹ + ‖b i - 1‖⁻¹ +
        ∑ j : Fin 10, if i = j then 0 else (dist (b i) (b j))⁻¹ := by
      have hs : 0 ≤ ∑ j : Fin 10, if i = j then 0 else (dist (b i) (b j))⁻¹ :=
        Finset.sum_nonneg fun j _ ↦ by split <;> positivity
      have hn : 0 ≤ ‖b i‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
      linarith
    _ ≤ ∑ k : Fin 10, (‖b k‖⁻¹ + ‖b k - 1‖⁻¹ +
        ∑ j : Fin 10, if k = j then 0 else (dist (b k) (b j))⁻¹) := by
      exact Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin 10 ↦
        ‖b k‖⁻¹ + ‖b k - 1‖⁻¹ + ∑ j : Fin 10,
          if k = j then 0 else (dist (b k) (b j))⁻¹) (fun k _ ↦ hnonneg k) (by simp)

private theorem b6t_radius_lt_dist_quarter (b : Fin 10 → ℂ) (i j : Fin 10)
    (hij : i ≠ j) (hbij : b i ≠ b j) : b6t_radius b < dist (b i) (b j) / 4 := by
  have hdist : 0 < dist (b i) (b j) := dist_pos.mpr hbij
  have hnonneg (k : Fin 10) : 0 ≤ ‖b k‖⁻¹ + ‖b k - 1‖⁻¹ +
      ∑ l : Fin 10, if k = l then 0 else (dist (b k) (b l))⁻¹ := by
    exact add_nonneg (add_nonneg (inv_nonneg.mpr (norm_nonneg _)) (inv_nonneg.mpr (norm_nonneg _)))
      (Finset.sum_nonneg fun l _ ↦ by split <;> positivity)
  apply b6t_radius_lt_quarter_of_inv_le b (dist (b i) (b j)) hdist
  calc
    (dist (b i) (b j))⁻¹ ≤ ∑ l : Fin 10,
        if i = l then 0 else (dist (b i) (b l))⁻¹ := by
      rw [← show (if i = j then 0 else (dist (b i) (b j))⁻¹) =
        (dist (b i) (b j))⁻¹ by simp [hij]]
      apply Finset.single_le_sum (s := Finset.univ) (a := j)
      · intro k hk
        split <;> positivity
      · simp [hij]
    _ ≤ ‖b i‖⁻¹ + ‖b i - 1‖⁻¹ +
        ∑ l : Fin 10, if i = l then 0 else (dist (b i) (b l))⁻¹ := by
      have h₁ : 0 ≤ ‖b i‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
      have h₂ : 0 ≤ ‖b i - 1‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
      linarith
    _ ≤ ∑ k : Fin 10, (‖b k‖⁻¹ + ‖b k - 1‖⁻¹ +
        ∑ l : Fin 10, if k = l then 0 else (dist (b k) (b l))⁻¹) := by
      exact Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin 10 ↦
        ‖b k‖⁻¹ + ‖b k - 1‖⁻¹ + ∑ l : Fin 10,
          if k = l then 0 else (dist (b k) (b l))⁻¹) (fun k _ ↦ hnonneg k) (by simp)

theorem b6t_discs_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    0 < b6t_radius b ∧
      (∀ i : Fin 10, (0 : ℂ) ∉ Metric.closedBall (b i) (b6t_radius b) ∧
        (1 : ℂ) ∉ Metric.closedBall (b i) (b6t_radius b)) ∧
      Pairwise (fun i j : Fin 10 ↦ Disjoint
        (Metric.closedBall (b i) (b6t_radius b))
        (Metric.closedBall (b j) (b6t_radius b))) := by
  have hcoord := (b6_chart_coordinates b).mp hb
  refine ⟨b6t_radius_pos b, ?_, ?_⟩
  · intro i
    constructor
    · intro hmem
      have hle : ‖b i‖ ≤ b6t_radius b := by
        simpa [Metric.mem_closedBall, dist_comm] using hmem
      have hlt := b6t_radius_lt_norm_quarter b i (hcoord.2 i).1
      have hn : 0 < ‖b i‖ := norm_pos_iff.mpr (hcoord.2 i).1
      linarith
    · intro hmem
      have hle : ‖b i - 1‖ ≤ b6t_radius b := by
        simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hmem
      have hlt := b6t_radius_lt_norm_sub_one_quarter b i (hcoord.2 i).2
      have hn : 0 < ‖b i - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hcoord.2 i).2)
      linarith
  · intro i j hij
    apply Metric.closedBall_disjoint_closedBall
    have hlt := b6t_radius_lt_dist_quarter b i j hij (fun h ↦ hij (hcoord.1 h))
    have hd : 0 < dist (b i) (b j) := dist_pos.mpr (fun h ↦ hij (hcoord.1 h))
    linarith

private theorem b6t_singleHomeomorph_eq_self_of_mem_other (b t : Fin 10 → ℂ)
    (hb : b ∈ b6_chart) (i j : Fin 10) (hij : i ≠ j)
    (hi : dist (t i) (b i) < b6t_radius b) {z : ℂ}
    (hz : z ∈ Metric.closedBall (b j) (b6t_radius b)) :
    b6t_singleHomeomorph b t i hi z = z := by
  apply b6t_singleHomeomorph_eq_self_of_not_mem
  intro hzi
  exact Set.disjoint_left.mp ((b6t_discs_aux b hb).2.2 hij) hzi hz

private noncomputable def b6t_composeHomeomorphs (b t : Fin 10 → ℂ)
    (ht : t ∈ b6t_polydisc b) : List (Fin 10) → ℂ ≃ₜ ℂ
  | [] => Homeomorph.refl ℂ
  | i :: l => (b6t_singleHomeomorph b t i (ht i)).trans (b6t_composeHomeomorphs b t ht l)

private theorem b6t_composeHomeomorphs_eq_self_on_other (b t : Fin 10 → ℂ)
    (hb : b ∈ b6_chart) (ht : t ∈ b6t_polydisc b) (i : Fin 10)
    (l : List (Fin 10)) (hil : ∀ j ∈ l, j ≠ i) {z : ℂ}
    (hz : z ∈ Metric.closedBall (b i) (b6t_radius b)) :
    b6t_composeHomeomorphs b t ht l z = z := by
  induction l with
  | nil => rfl
  | cons j l ih =>
      rw [b6t_composeHomeomorphs, Homeomorph.trans_apply,
        b6t_singleHomeomorph_eq_self_of_mem_other b t hb j i (hil j (by simp)) (ht j) hz]
      exact ih (fun k hk ↦ hil k (by simp [hk]))

private theorem b6t_composeHomeomorphs_apply_of_mem (b t : Fin 10 → ℂ)
    (hb : b ∈ b6_chart) (ht : t ∈ b6t_polydisc b) (i : Fin 10)
    (l : List (Fin 10)) (hnodup : l.Nodup) (hi : i ∈ l) {z : ℂ}
    (hz : z ∈ Metric.closedBall (b i) (b6t_radius b)) :
    b6t_composeHomeomorphs b t ht l z = b6t_singleHomeomorph b t i (ht i) z := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hji : j = i
      · subst j
        rw [b6t_composeHomeomorphs, Homeomorph.trans_apply]
        apply b6t_composeHomeomorphs_eq_self_on_other b t hb ht i l
        · intro k hk hki
          subst k
          exact hnodup.1 hk
        · exact b6t_singleHomeomorph_maps_closedBall b t i (ht i) hz
      · rw [b6t_composeHomeomorphs, Homeomorph.trans_apply,
          b6t_singleHomeomorph_eq_self_of_mem_other b t hb j i hji (ht j) hz]
        apply ih hnodup.2
        simpa [Ne.symm hji] using hi

private theorem b6t_composeHomeomorphs_eq_self_of_outside (b t : Fin 10 → ℂ)
    (ht : t ∈ b6t_polydisc b) (l : List (Fin 10)) {z : ℂ}
    (hz : ∀ i, z ∉ Metric.closedBall (b i) (b6t_radius b)) :
    b6t_composeHomeomorphs b t ht l z = z := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [b6t_composeHomeomorphs, Homeomorph.trans_apply,
        b6t_singleHomeomorph_eq_self_of_not_mem b t i (ht i) (hz i), ih]

private noncomputable def b6t_planeHomeomorph (b t : Fin 10 → ℂ)
    (ht : t ∈ b6t_polydisc b) : ℂ ≃ₜ ℂ :=
  b6t_composeHomeomorphs b t ht (List.ofFn fun i : Fin 10 ↦ i)

private theorem b6t_planeHomeomorph_apply (b t : Fin 10 → ℂ)
    (hb : b ∈ b6_chart) (ht : t ∈ b6t_polydisc b) (z : ℂ) :
    b6t_planeHomeomorph b t ht z = b6t_plane b t z := by
  by_cases hz : ∃ i : Fin 10, z ∈ Metric.closedBall (b i) (b6t_radius b)
  · obtain ⟨i, hi⟩ := hz
    rw [b6t_planeHomeomorph, b6t_composeHomeomorphs_apply_of_mem b t hb ht i]
    · rw [show b6t_singleHomeomorph b t i (ht i) z =
          z + b6t_singleShift b t i z from b6t_singleHomeomorph_apply b t i (ht i) z,
        b6t_plane]
      congr 1
      rw [Finset.sum_eq_single i]
      · rfl
      · intro j hj hji
        apply b6t_singleShift_eq_zero_of_not_mem
        intro hjmem
        exact Set.disjoint_left.mp ((b6t_discs_aux b hb).2.2 hji) hjmem hi
      · simp
    · exact (List.nodup_ofFn.mpr fun _ _ h ↦ h)
    · exact List.mem_ofFn.mpr ⟨i, rfl⟩
    · exact hi
  · have hout : ∀ i : Fin 10, z ∉ Metric.closedBall (b i) (b6t_radius b) := by
      simpa only [not_exists] using hz
    rw [b6t_planeHomeomorph, b6t_composeHomeomorphs_eq_self_of_outside b t ht _ hout,
      b6t_plane]
    apply Eq.symm
    rw [add_eq_left]
    change ∑ i : Fin 10, b6t_singleShift b t i z = 0
    exact Finset.sum_eq_zero fun i _ ↦ b6t_singleShift_eq_zero_of_not_mem b t i (hout i)

theorem b6t_polydisc_neighbourhood_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    b ∈ b6t_polydisc b ∧ (b6t_polydisc b).Nonempty ∧
      IsOpen (b6t_polydisc b) ∧ b6t_polydisc b ⊆ b6_chart := by
  have hdiscs := b6t_discs_aux b hb
  have hmem : b ∈ b6t_polydisc b := by
    intro i
    simpa [Metric.mem_ball] using hdiscs.1
  refine ⟨hmem, ⟨b, hmem⟩, ?_, ?_⟩
  · rw [show b6t_polydisc b = ⋂ i : Fin 10,
        (fun t : Fin 10 → ℂ ↦ t i) ⁻¹' Metric.ball (b i) (b6t_radius b) by
      ext t
      simp [b6t_polydisc]]
    exact isOpen_iInter_of_finite fun i ↦
      (Metric.isOpen_ball.preimage (continuous_apply i))
  · intro t ht
    rw [b6_chart_coordinates]
    constructor
    · intro i j heq
      by_contra hij
      have hi : t i ∈ Metric.closedBall (b i) (b6t_radius b) :=
        Metric.ball_subset_closedBall (ht i)
      have hj : t i ∈ Metric.closedBall (b j) (b6t_radius b) := by
        rw [heq]
        exact Metric.ball_subset_closedBall (ht j)
      exact Set.disjoint_left.mp (hdiscs.2.2 hij) hi hj
    · intro i
      constructor
      · intro hi
        apply (hdiscs.2.1 i).1
        rw [← hi]
        exact Metric.ball_subset_closedBall (ht i)
      · intro hi
        apply (hdiscs.2.1 i).2
        rw [← hi]
        exact Metric.ball_subset_closedBall (ht i)

theorem b6t_homeomorph_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) :
    ∃ e : OnePoint ℂ ≃ₜ OnePoint ℂ, ∀ x, e x = b6t_sphere b t x := by
  let e := Homeomorph.onePointCongr (b6t_planeHomeomorph b t ht)
  refine ⟨e, ?_⟩
  intro x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe z =>
      change ((b6t_planeHomeomorph b t ht z : ℂ) : OnePoint ℂ) =
        (b6t_plane b t z : OnePoint ℂ)
      rw [b6t_planeHomeomorph_apply b t hb ht z]

private theorem b6t_plane_eq_self_of_forall_not_mem (b t : Fin 10 → ℂ) (z : ℂ)
    (hz : ∀ i : Fin 10, z ∉ Metric.closedBall (b i) (b6t_radius b)) :
    b6t_plane b t z = z := by
  rw [b6t_plane, add_eq_left]
  apply Finset.sum_eq_zero
  intro i hi
  have hdist : b6t_radius b < dist z (b i) := by
    simpa [Metric.mem_closedBall, not_le] using hz i
  have hratio : 1 - dist z (b i) / b6t_radius b < 0 := by
    have hr := b6t_radius_pos b
    apply sub_neg.mpr
    exact (lt_div_iff₀ hr).mpr (by simpa using hdist)
  simp [max_eq_left (le_of_lt hratio)]

theorem b6t_fixed_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) :
    b6t_sphere b t ((0 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) ∧
      b6t_sphere b t ((1 : ℂ) : OnePoint ℂ) = ((1 : ℂ) : OnePoint ℂ) ∧
      b6t_sphere b t OnePoint.infty = OnePoint.infty ∧
      ∀ x : OnePoint ℂ,
        x ∉ ⋃ i : Fin 10, ((↑) : ℂ → OnePoint ℂ) ''
          Metric.closedBall (b i) (b6t_radius b) → b6t_sphere b t x = x := by
  have hdiscs := b6t_discs_aux b hb
  have hzero : b6t_plane b t 0 = 0 :=
    b6t_plane_eq_self_of_forall_not_mem b t 0 (fun i ↦ (hdiscs.2.1 i).1)
  have hone : b6t_plane b t 1 = 1 :=
    b6t_plane_eq_self_of_forall_not_mem b t 1 (fun i ↦ (hdiscs.2.1 i).2)
  refine ⟨by simpa [b6t_sphere], by simpa [b6t_sphere], rfl, ?_⟩
  intro x hx
  induction x using OnePoint.rec with
  | infty => rfl
  | coe z =>
      have hz : ∀ i : Fin 10, z ∉ Metric.closedBall (b i) (b6t_radius b) := by
        intro i hzi
        apply hx
        simp only [Set.mem_iUnion]
        exact ⟨i, ⟨z, hzi, rfl⟩⟩
      simpa [b6t_sphere, b6t_plane_eq_self_of_forall_not_mem b t z hz]

private theorem b6t_plane_center (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (i : Fin 10) : b6t_plane b t (b i) = t i := by
  have hr : b6t_radius b ≠ 0 := ne_of_gt (b6t_radius_pos b)
  rw [b6t_plane, Finset.sum_eq_single i]
  · simp [hr]
  · intro j hj hji
    have hcoord := (b6_chart_coordinates b).mp hb
    have hlt := b6t_radius_lt_dist_quarter b i j (Ne.symm hji)
      (fun h ↦ Ne.symm hji (hcoord.1 h))
    have hd : 0 < dist (b i) (b j) := dist_pos.mpr (fun h ↦ Ne.symm hji (hcoord.1 h))
    have hdist : b6t_radius b < dist (b i) (b j) := by linarith
    have hratio : 1 - dist (b i) (b j) / b6t_radius b < 0 := by
      apply sub_neg.mpr
      exact (lt_div_iff₀ (b6t_radius_pos b)).mpr (by simpa using hdist)
    simp [max_eq_left (le_of_lt hratio)]
  · simp

theorem b6t_marks_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) :
    ∀ j : Fin 13, b6t_sphere b t (b6_branch b j) = b6_branch t j := by
  have hdiscs := b6t_discs_aux b hb
  have hzero : b6t_plane b t 0 = 0 :=
    b6t_plane_eq_self_of_forall_not_mem b t 0 (fun i ↦ (hdiscs.2.1 i).1)
  have hone : b6t_plane b t 1 = 1 :=
    b6t_plane_eq_self_of_forall_not_mem b t 1 (fun i ↦ (hdiscs.2.1 i).2)
  intro j
  fin_cases j <;>
    simp [b6_branch, Fin.append, Fin.addCases, b6t_sphere, b6t_plane_center b t hb,
      hzero, hone]

private theorem b6t_plane_family_continuous (b : Fin 10 → ℂ) :
    Continuous (fun p : b6t_polydisc b × ℂ ↦ b6t_plane b p.1.val p.2) := by
  unfold b6t_plane
  apply continuous_snd.add
  apply continuous_finset_sum
  intro i hi
  exact (continuous_const.max
    (continuous_const.sub
      (((continuous_snd.dist continuous_const).div_const (b6t_radius b))))).smul
        (((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).sub
          continuous_const)

theorem b6t_continuous_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    Continuous (fun p : b6t_polydisc b × OnePoint ℂ ↦
      b6t_sphere b p.1.val p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t, x⟩
  induction x using OnePoint.rec with
  | coe z =>
      let e : b6t_polydisc b × ℂ → b6t_polydisc b × OnePoint ℂ :=
        Prod.map id ((↑) : ℂ → OnePoint ℂ)
      have he : Topology.IsOpenEmbedding e :=
        (Homeomorph.refl _).isOpenEmbedding.prodMap OnePoint.isOpenEmbedding_coe
      change ContinuousAt (fun p : b6t_polydisc b × OnePoint ℂ ↦
        b6t_sphere b p.1.val p.2) (e (t, z))
      rw [ContinuousAt, ← he.map_nhds_eq (t, z), Filter.tendsto_map'_iff]
      change ContinuousAt (fun p : b6t_polydisc b × ℂ ↦
        ((b6t_plane b p.1.val p.2 : ℂ) : OnePoint ℂ)) (t, z)
      exact (OnePoint.continuous_coe.comp (b6t_plane_family_continuous b)).continuousAt
  | infty =>
      let K : Set ℂ := ⋃ i : Fin 10, Metric.closedBall (b i) (b6t_radius b)
      have hKclosed : IsClosed K :=
        isClosed_iUnion_of_finite fun i ↦ Metric.isClosed_closedBall
      have hKcompact : IsCompact K :=
        isCompact_iUnion fun i ↦ ProperSpace.isCompact_closedBall (b i) (b6t_radius b)
      have hopen : IsOpen (((↑) '' K : Set (OnePoint ℂ))ᶜ) :=
        OnePoint.isOpen_compl_image_coe.mpr ⟨hKclosed, hKcompact⟩
      have hnhds : Set.univ ×ˢ (((↑) '' K : Set (OnePoint ℂ))ᶜ) ∈
          nhds (t, (OnePoint.infty : OnePoint ℂ)) := by
        apply (isOpen_univ.prod hopen).mem_nhds
        simp
      apply continuousAt_snd.congr_of_eventuallyEq
      filter_upwards [hnhds] with p hp
      rcases p with ⟨q, x⟩
      induction x using OnePoint.rec with
      | infty => rfl
      | coe z =>
          have hz : ∀ i : Fin 10,
              z ∉ Metric.closedBall (b i) (b6t_radius b) := by
            intro i hzi
            exact hp.2 ⟨z, Set.mem_iUnion.mpr ⟨i, hzi⟩, rfl⟩
          simp [b6t_sphere, b6t_plane_eq_self_of_forall_not_mem b q.val z hz]

theorem b6t_identity_aux (b : Fin 10 → ℂ) :
    b6t_sphere b b = id := by
  funext x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe z =>
      simp [b6t_sphere, b6t_plane]

theorem b6t_punctured_homeomorph_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) :
    ∃ e : b6t_punctured b ≃ₜ b6t_punctured t,
      ∀ x, (e x : OnePoint ℂ) = b6t_sphere b t x := by
  obtain ⟨e, he⟩ := b6t_homeomorph_aux b hb t ht
  have hmarks : ∀ j : Fin 13, e (b6_branch b j) = b6_branch t j := by
    intro j
    rw [he]
    exact b6t_marks_aux b hb t ht j
  have hiff : ∀ x : OnePoint ℂ, x ∈ b6t_punctured b ↔ e x ∈ b6t_punctured t := by
    intro x
    simp only [b6t_punctured, Set.mem_compl_iff, Set.mem_range, not_exists]
    constructor
    · intro hx j hej
      apply hx j
      apply e.injective
      rw [hmarks j]
      exact hej
    · intro hx j hj
      apply hx j
      rw [← hmarks j, hj]
  let ep := e.subtype hiff
  refine ⟨ep, ?_⟩
  intro x
  change e x = b6t_sphere b t x
  exact he x

theorem b6t_cover_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) (G : Type) [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G) :
    ∃ e : b6t_punctured b ≃ₜ b6t_punctured t,
      (∀ x, (e x : OnePoint ℂ) = b6t_sphere b t x) ∧
      IsQuotientCoveringMap (e ∘ π) G ∧
      (∀ u, ((e ∘ π) u : OnePoint ℂ) = b6t_projection b t π u) ∧
      (∀ a : G, ∀ u : U, b6t_projection b t π (a • u) = b6t_projection b t π u) ∧
      (∀ a : G, ∀ u : U, (Homeomorph.refl U) (a • u) = a • (Homeomorph.refl U) u) := by
  obtain ⟨e, he⟩ := b6t_punctured_homeomorph_aux b hb t ht
  refine ⟨e, he, hπ.homeomorph_comp e, ?_, ?_, ?_⟩
  · intro u
    exact he (π u)
  · intro a u
    simp only [b6t_projection]
    rw [hπ.map_smul]
  · intro a u
    rfl

private theorem fundamentalGroupToMulOpposite_homeomorph_comp
    {X Y U G : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace U]
    [Group G] [MulAction G U] (p : U → X) (hp : IsQuotientCoveringMap p G)
    (e : X ≃ₜ Y) (x : X) (u : p ⁻¹' {x}) :
    ((hp.homeomorph_comp e).fundamentalGroupToMulOpposite
      ⟨u.val, congrArg e u.property⟩).comp
      (FundamentalGroup.map ⟨e, e.continuous⟩ x) =
      hp.fundamentalGroupToMulOpposite u := by
  ext γ
  rw [MonoidHom.comp_apply]
  rw [IsQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_iff]
  let m := hp.isCoveringMap.monodromy γ.asHom u
  let m' : (e ∘ p) ⁻¹' {e x} := ⟨m.val, congrArg e m.property⟩
  change ((hp.fundamentalGroupToMulOpposite u γ).unop • u.val) =
    ((hp.homeomorph_comp e).isCoveringMap.monodromy
      ((FundamentalGroup.map ⟨e, e.continuous⟩ x) γ).asHom
      ⟨u.val, congrArg e u.property⟩).val
  rw [hp.unop_fundamentalGroupToMulOpposite_smul]
  change m.val = _
  have hm : (hp.homeomorph_comp e).isCoveringMap.monodromy
      ((FundamentalGroup.map ⟨e, e.continuous⟩ x) γ).asHom
      ⟨u.val, congrArg e u.property⟩ = m' := by
    apply (hp.homeomorph_comp e).isCoveringMap.monodromy_eq_of_map_eq
      (hp.isCoveringMap.liftPathQuotient γ.asHom u)
    change (hp.isCoveringMap.liftPathQuotient γ.asHom u).map
      ((⟨e, e.continuous⟩ : C(X, Y)).comp ⟨p, hp.continuous⟩) = _
    rw [Path.Homotopic.Quotient.map_comp, hp.isCoveringMap.map_liftPathQuotient]
    exact Path.Homotopic.Quotient.map_cast γ.asHom
  exact congrArg Subtype.val hm.symm

theorem b6t_monodromy_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) (G : Type) [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G) (x₀ : b6t_punctured b) (u₀ : π ⁻¹' {x₀})
    (hx₀ : (x₀ : OnePoint ℂ) ∉ ⋃ i : Fin 10, ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall (b i) (b6t_radius b)) :
    ∃ e : b6t_punctured b ≃ₜ b6t_punctured t,
      (∀ x, (e x : OnePoint ℂ) = b6t_sphere b t x) ∧
      (e x₀ : OnePoint ℂ) = x₀ ∧
      ((hπ.homeomorph_comp e).fundamentalGroupToMulOpposite
        ⟨u₀.val, congrArg e u₀.property⟩).comp
        (FundamentalGroup.map ⟨e, e.continuous⟩ x₀) =
        hπ.fundamentalGroupToMulOpposite u₀ := by
  obtain ⟨e, he⟩ := b6t_punctured_homeomorph_aux b hb t ht
  refine ⟨e, he, ?_, fundamentalGroupToMulOpposite_homeomorph_comp π hπ e x₀ u₀⟩
  rw [he]
  exact (b6t_fixed_aux b hb t ht).2.2.2 (x₀ : OnePoint ℂ) hx₀

end HodgeLean.Foundations.Program
