import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5Defs
import Mathlib.Logic.Encodable.Lattice

/-! # Segment incidence and Hausdorff dimension

This module uses only Mathlib. HC no distance; AV milestone no distance.
-/
noncomputable section
open Set Metric
open scoped ENNReal NNReal MeasureTheory
namespace HodgeLean.Adapters

private theorem bh5_hausdorff_zero_cover {E : Type*} [EMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (q : ℝ≥0) (Z : Set E)
    (hz : μH[q] Z = 0) (r ε : ℝ≥0∞) (hr : 0 < r) (hε : 0 < ε) :
    ∃ t : ℕ → Set E, Z ⊆ ⋃ i, t i ∧ (∀ i, ediam (t i) ≤ r) ∧
      ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (q : ℝ) < ε := by
  rw [MeasureTheory.Measure.hausdorffMeasure_apply] at hz
  have hInf : (⨅ (t : ℕ → Set E) (_ : Z ⊆ ⋃ i, t i)
      (_ : ∀ i, ediam (t i) ≤ r),
      ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (q : ℝ)) = 0 := by
    apply nonpos_iff_eq_zero.mp
    exact (le_iSup₂ r hr).trans_eq hz
  have hlt : (⨅ (t : ℕ → Set E) (_ : Z ⊆ ⋃ i, t i)
      (_ : ∀ i, ediam (t i) ≤ r),
      ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (q : ℝ)) < ε := hInf.trans_lt hε
  rw [iInf_lt_iff] at hlt
  obtain ⟨t, hlt⟩ := hlt
  rw [iInf_lt_iff] at hlt
  obtain ⟨hcov, hlt⟩ := hlt
  rw [iInf_lt_iff] at hlt
  obtain ⟨hdiam, hsum⟩ := hlt
  exact ⟨t, hcov, hdiam, hsum⟩

private theorem bh5_interval_subdivision (δ : ℝ≥0∞) (hδ0 : δ ≠ 0) (hδtop : δ ≠ ∞) :
    ∃ N : ℕ, ∃ u : Fin N → Set ℝ,
      Icc (0 : ℝ) 1 ⊆ ⋃ j, u j ∧ (∀ j, ediam (u j) ≤ δ) ∧
      (N : ℝ≥0∞) ≤ δ⁻¹ + 1 := by
  let a := δ.toReal
  have ha : 0 < a := ENNReal.toReal_pos hδ0 hδtop
  let N := ⌊(1 : ℝ) / a⌋₊ + 1
  let u : Fin N → Set ℝ := fun j ↦ Icc ((j : ℕ) * a) (((j : ℕ) + 1) * a)
  refine ⟨N, u, ?_, ?_, ?_⟩
  · intro x hx
    have hxdiv : 0 ≤ x / a := div_nonneg hx.1 ha.le
    have hmono : x / a ≤ 1 / a := div_le_div_of_nonneg_right hx.2 ha.le
    let j : Fin N := ⟨⌊x / a⌋₊, Nat.lt_succ_of_le (Nat.floor_mono hmono)⟩
    refine mem_iUnion.2 ⟨j, ?_⟩
    change (j : ℕ) * a ≤ x ∧ x ≤ ((j : ℕ) + 1) * a
    constructor
    · exact (le_div_iff₀ ha).mp (Nat.floor_le hxdiv)
    · exact ((div_lt_iff₀ ha).mp (Nat.lt_floor_add_one (x / a))).le
  · intro j
    change ediam (Icc ((j : ℕ) * a) (((j : ℕ) + 1) * a)) ≤ δ
    rw [Real.ediam_Icc]
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_sub_cancel_left]
    rw [ENNReal.ofReal_toReal hδtop]
  · change ((⌊(1 : ℝ) / a⌋₊ + 1 : ℕ) : ℝ≥0∞) ≤ δ⁻¹ + 1
    rw [Nat.cast_add, Nat.cast_one]
    gcongr
    rw [← ENNReal.ofReal_natCast]
    refine (ENNReal.ofReal_le_ofReal
      (Nat.floor_le (div_nonneg (by norm_num) ha.le))).trans_eq ?_
    rw [ENNReal.ofReal_div_of_pos ha, ENNReal.ofReal_one, ENNReal.ofReal_toReal hδtop,
      one_div]

private theorem bh5_ediam_prod_le {E F : Type*} [EMetricSpace E] [EMetricSpace F]
    (s : Set E) (t : Set F) : ediam (s ×ˢ t) ≤ max (ediam s) (ediam t) := by
  apply ediam_le
  rintro ⟨x, y⟩ ⟨hx, hy⟩ ⟨x', y'⟩ ⟨hx', hy'⟩
  rw [Prod.edist_eq]
  exact max_le_max (edist_le_ediam_of_mem hx hx') (edist_le_ediam_of_mem hy hy')

private theorem bh5_subdivision_cost (δ : ℝ≥0∞) (hδ0 : δ ≠ 0) (hδ1 : δ ≤ 1)
    (q d : ℝ) (hqd : q + 1 ≤ d) :
    (δ⁻¹ + 1) * δ ^ d ≤ 2 * δ ^ q := by
  have hδtop : δ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hδ1
  rw [add_mul, one_mul]
  have hinv : δ⁻¹ * δ ^ d = δ ^ (d - 1) := by
    rw [← ENNReal.rpow_neg_one, ← ENNReal.rpow_add (-1) d hδ0 hδtop]
    congr 1
    ring
  rw [hinv, two_mul]
  exact add_le_add
    (ENNReal.rpow_le_rpow_of_exponent_ge hδ1 (by linarith))
    (ENNReal.rpow_le_rpow_of_exponent_ge hδ1 (by linarith))

private theorem bh5_geometric_rpow_tsum_lt_top (q : ℝ) (hq : 0 < q) :
    (∑' i : ℕ, (((2 : ℝ≥0∞)⁻¹) ^ (i + 1)) ^ q) < ∞ := by
  have hr : ((2 : ℝ≥0∞)⁻¹) ^ q < 1 :=
    ENNReal.rpow_lt_one (by norm_num) hq
  have heq : ∀ i : ℕ, (((2 : ℝ≥0∞)⁻¹) ^ (i + 1)) ^ q =
      (((2 : ℝ≥0∞)⁻¹) ^ q) ^ (i + 1) := by
    intro i
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul]
    congr 1
    ring
  simp_rw [heq]
  rw [ENNReal.tsum_geometric_add_one]
  exact (ENNReal.mul_ne_top (ne_top_of_lt (hr.trans ENNReal.one_lt_top))
    (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.mpr hr).ne')).lt_top

private theorem bh5_product_measure_ne_top_of_zero {E : Type*} [EMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace (E × ℝ)] [BorelSpace (E × ℝ)]
    (q d : ℝ≥0) (hq : 0 < q)
    (hqd : (q : ℝ) + 1 ≤ d) (Z : Set E) (hz : μH[q] Z = 0) :
    μH[d] (Z ×ˢ Icc (0 : ℝ) 1) ≠ ∞ := by
  classical
  let G : ℝ≥0∞ := ∑' i : ℕ, (((2 : ℝ≥0∞)⁻¹) ^ (i + 1)) ^ (q : ℝ)
  have hG : G < ∞ := bh5_geometric_rpow_tsum_lt_top q hq
  have hC : 2 * (1 + G) < ∞ := by
    apply (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.add_ne_top.mpr ⟨by norm_num, hG.ne⟩)).lt_top
  apply (show μH[d] (Z ×ˢ Icc (0 : ℝ) 1) ≤ 2 * (1 + G) from ?_).trans_lt hC |>.ne
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  refine iSup₂_le fun r hr ↦ ?_
  let r₀ := min r 1
  have hr₀ : 0 < r₀ := lt_min hr zero_lt_one
  obtain ⟨t, htZ, htr, htsum⟩ :=
    bh5_hausdorff_zero_cover q Z hz r₀ 1 hr₀ zero_lt_one
  let a : ℕ → ℝ≥0∞ := fun i ↦ min r₀ (((2 : ℝ≥0∞)⁻¹) ^ (i + 1))
  let δ : ℕ → ℝ≥0∞ := fun i ↦ max (ediam (t i)) (a i)
  have ha0 : ∀ i, a i ≠ 0 := by
    intro i
    exact (lt_min hr₀
      (pos_iff_ne_zero.mpr (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by norm_num))))).ne'
  have hδ0 : ∀ i, δ i ≠ 0 := fun i ↦
    (lt_of_lt_of_le (lt_of_le_of_ne bot_le (ha0 i).symm) (le_max_right _ _)).ne'
  have hδr : ∀ i, δ i ≤ r₀ := fun i ↦ max_le (htr i) (min_le_left _ _)
  have hδ1 : ∀ i, δ i ≤ 1 := fun i ↦ (hδr i).trans (min_le_right _ _)
  have hδtop : ∀ i, δ i ≠ ∞ := fun i ↦
    ne_top_of_le_ne_top ENNReal.one_ne_top (hδ1 i)
  choose N u hucover hudiam huN using fun i ↦
    bh5_interval_subdivision (δ i) (hδ0 i) (hδtop i)
  let tile : (Σ i, Fin (N i)) → Set (E × ℝ) := fun p ↦ t p.1 ×ˢ u p.1 p.2
  have hcover : Z ×ˢ Icc (0 : ℝ) 1 ⊆ ⋃ p, tile p := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.1 (htZ hx)
    obtain ⟨j, hyj⟩ := mem_iUnion.1 (hucover i hy)
    exact mem_iUnion.2 ⟨⟨i, j⟩, hxi, hyj⟩
  have htile : ∀ p, ediam (tile p) ≤ r := by
    rintro ⟨i, j⟩
    exact (bh5_ediam_prod_le _ _).trans (max_le (le_max_left _ _) (hudiam i j)) |>.trans
      (hδr i) |>.trans (min_le_left _ _)
  let coverN : ℕ → Set (E × ℝ) := fun k ↦
    ⋃ p ∈ Encodable.decode₂ (Σ i, Fin (N i)) k, tile p
  have hcoverN : Z ×ˢ Icc (0 : ℝ) 1 ⊆ ⋃ k, coverN k := by
    rw [Encodable.iUnion_decode₂]
    exact hcover
  have hcoverNdiam : ∀ k, ediam (coverN k) ≤ r := by
    intro k
    rw [ediam_iUnion_mem_option]
    exact iSup₂_le fun p _ ↦ htile p
  refine (iInf₂_le_of_le coverN hcoverN (iInf_le_of_le hcoverNdiam le_rfl)).trans ?_
  calc
    (∑' k, ⨆ _ : (coverN k).Nonempty, ediam (coverN k) ^ (d : ℝ)) =
        ∑' p, ⨆ _ : (tile p).Nonempty, ediam (tile p) ^ (d : ℝ) := by
          dsimp only [coverN]
          exact tsum_iUnion_decode₂
            (fun s : Set (E × ℝ) ↦ ⨆ _ : s.Nonempty, ediam s ^ (d : ℝ)) (by simp) tile
    _ ≤ ∑' p, ediam (tile p) ^ (d : ℝ) :=
      ENNReal.tsum_le_tsum fun p ↦ iSup_le fun _ ↦ le_rfl
    _ = ∑' i, ∑' j, ediam (tile ⟨i, j⟩) ^ (d : ℝ) := ENNReal.tsum_sigma' _
    _ ≤ ∑' i, 2 * δ i ^ (q : ℝ) := ENNReal.tsum_le_tsum fun i ↦ by
      calc
        (∑' j, ediam (tile ⟨i, j⟩) ^ (d : ℝ)) ≤
            ∑' _j : Fin (N i), δ i ^ (d : ℝ) := ENNReal.tsum_le_tsum fun j ↦
              ENNReal.rpow_le_rpow ((bh5_ediam_prod_le _ _).trans
                (max_le (le_max_left _ _) (hudiam i j))) (by positivity)
        _ = (N i : ℝ≥0∞) * δ i ^ (d : ℝ) := by simp
        _ ≤ (δ i ^ (-1 : ℝ) + 1) * δ i ^ (d : ℝ) := by
          gcongr
          simpa [ENNReal.rpow_neg_one] using huN i
        _ ≤ 2 * δ i ^ (q : ℝ) := by
          simpa [ENNReal.rpow_neg_one] using
            bh5_subdivision_cost (δ i) (hδ0 i) (hδ1 i) q d hqd
    _ = 2 * ∑' i, δ i ^ (q : ℝ) := ENNReal.tsum_mul_left
    _ ≤ 2 * (1 + G) := by
      gcongr
      have hplain : (∑' i, ediam (t i) ^ (q : ℝ)) < 1 := by
        convert htsum using 1
        congr 1
        funext i
        by_cases hi : (t i).Nonempty
        · simp [hi]
        · rw [not_nonempty_iff_eq_empty.mp hi, ediam_empty]
          simp [hq]
      calc
        (∑' i, δ i ^ (q : ℝ)) ≤
            ∑' i, (ediam (t i) ^ (q : ℝ) + a i ^ (q : ℝ)) :=
          ENNReal.tsum_le_tsum fun i ↦ by
            rw [show δ i = max (ediam (t i)) (a i) by rfl]
            rcases le_total (ediam (t i)) (a i) with h | h
            · rw [max_eq_right h]
              exact le_add_of_nonneg_left bot_le
            · rw [max_eq_left h]
              exact le_add_of_nonneg_right bot_le
        _ = (∑' i, ediam (t i) ^ (q : ℝ)) + ∑' i, a i ^ (q : ℝ) :=
          ENNReal.tsum_add
        _ ≤ 1 + G := add_le_add hplain.le (ENNReal.tsum_le_tsum fun i ↦
          ENNReal.rpow_le_rpow (min_le_right _ _) hq.le)

private theorem bh5_countable_prod_Icc_dim (n : ℕ) (C : Set (Fin n → ℂ))
    (hC : C.Countable) : dimH (C ×ˢ Icc (0 : ℝ) 1) ≤ 1 := by
  letI := hC.toEncodable
  rw [show C ×ˢ Icc (0 : ℝ) 1 = ⋃ x : C,
      (fun t : ℝ ↦ ((x : Fin n → ℂ), t)) '' Icc (0 : ℝ) 1 by
    ext p
    simp only [mem_prod, mem_iUnion, mem_image]
    constructor
    · rintro ⟨hp1, hp2⟩
      exact ⟨⟨p.1, hp1⟩, p.2, hp2, rfl⟩
    · rintro ⟨x, t, ht, htp⟩
      rw [← htp]
      exact ⟨x.2, ht⟩]
  rw [dimH_iUnion]
  refine iSup_le fun x ↦ (LipschitzWith.prodMk_left x.1).dimH_image_le _ |>.trans ?_
  exact (dimH_mono (subset_univ _)).trans (by
    simpa using (Real.dimH_univ_eq_finrank ℝ).le)

/-- Product with a real unit interval raises Hausdorff dimension by at most one.
Source: Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Chapter 8. -/
theorem bh5_interval_product_dim_aux (n : ℕ) (Z : Set (Fin n → ℂ)) :
    dimH (Z ×ˢ Icc (0 : ℝ) 1) ≤ dimH Z + 1 := by
  have hZtop : dimH Z ≠ ∞ := ne_top_of_le_ne_top (by simp)
    ((dimH_mono (subset_univ Z)).trans_eq (Real.dimH_univ_eq_finrank (Fin n → ℂ)))
  let D : ℝ≥0 := (dimH Z).toNNReal
  rw [← ENNReal.coe_toNNReal hZtop]
  borelize (Fin n → ℂ)
  borelize ((Fin n → ℂ) × ℝ)
  apply dimH_le
  intro d hd
  by_contra! hnot
  let q : ℝ≥0 := (D + (d - 1)) / 2
  have hdD : D + 1 < d := by exact_mod_cast hnot
  have hdDreal : (D : ℝ) + 1 < d := by exact_mod_cast hdD
  have hd1NN : (1 : ℝ≥0) ≤ d := (le_add_of_nonneg_left bot_le).trans hdD.le
  have hqD : D < q := by
    dsimp [q]
    apply NNReal.coe_lt_coe.mp
    push_cast
    rw [NNReal.coe_sub hd1NN]
    norm_num
    linarith
  have hq0 : 0 < q := lt_of_le_of_lt bot_le hqD
  have hqd : (q : ℝ) + 1 ≤ d := by
    dsimp [q]
    push_cast
    rw [NNReal.coe_sub hd1NN]
    norm_num
    linarith
  have hz : μH[q] Z = 0 := hausdorffMeasure_of_dimH_lt (by
    rw [← ENNReal.coe_toNNReal hZtop]
    exact_mod_cast hqD)
  exact (bh5_product_measure_ne_top_of_zero q d hq0 hqd Z hz) hd

/-- The incidence set is the image of an explicit globally Lipschitz affine map.
Source: the definition of segment incidence and the norm inequalities for affine maps. -/
theorem bh5_segment_image_aux (n : ℕ) (Z : Set (Fin n → ℂ)) (a v : Fin n → ℂ) :
    (∃ K : ℝ≥0, LipschitzWith K
      (fun p : (Fin n → ℂ) × ℝ ↦ p.1 - a - p.2 • v)) ∧
    bh5_segmentIncidence n Z a v =
      (fun p : (Fin n → ℂ) × ℝ ↦ p.1 - a - p.2 • v) '' (Z ×ˢ Icc (0 : ℝ) 1) := by
  constructor
  · exact ⟨_, (LipschitzWith.prod_fst.sub (LipschitzWith.const a)).sub
      ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v).lipschitzWith.comp
        LipschitzWith.prod_snd)⟩
  · ext z
    constructor
    · rintro ⟨t, ht, hz⟩
      exact ⟨(z + a + t • v, t), ⟨hz, ht⟩, by dsimp; abel⟩
    · rintro ⟨⟨w, t⟩, ⟨hw, ht⟩, rfl⟩
      refine ⟨t, ht, ?_⟩
      convert hw using 1
      dsimp
      abel

/-- Sweeping by one compact real segment increases Hausdorff dimension by at most one.
Source: Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Chapter 8,
product with an interval and Lipschitz images. -/
theorem bh5_segment_dim_aux (n : ℕ) (Z : Set (Fin n → ℂ)) (a v : Fin n → ℂ) :
    dimH (bh5_segmentIncidence n Z a v) ≤ dimH Z + 1 := by
  obtain ⟨⟨K, hK⟩, he⟩ := bh5_segment_image_aux n Z a v
  rw [he]
  exact (hK.dimH_image_le _).trans (bh5_interval_product_dim_aux n Z)


example : dimH (({0} : Set (Fin 1 → ℂ)) ×ˢ Icc (0 : ℝ) 1) ≤
    dimH ({0} : Set (Fin 1 → ℂ)) + 1 := bh5_interval_product_dim_aux 1 {0}

example : dimH (({0} : Set (Fin 2 → ℂ)) ×ˢ Icc (0 : ℝ) 1) ≤
    dimH ({0} : Set (Fin 2 → ℂ)) + 1 := bh5_interval_product_dim_aux 2 {0}

example : bh5_segmentIncidence 1 {0} 0 1 =
    (fun p : (Fin 1 → ℂ) × ℝ ↦ p.1 - 0 - p.2 • (1 : Fin 1 → ℂ)) ''
      (({0} : Set (Fin 1 → ℂ)) ×ˢ Icc (0 : ℝ) 1) :=
  (bh5_segment_image_aux 1 {0} 0 1).2

example : bh5_segmentIncidence 2 {0} 0 1 =
    (fun p : (Fin 2 → ℂ) × ℝ ↦ p.1 - 0 - p.2 • (1 : Fin 2 → ℂ)) ''
      (({0} : Set (Fin 2 → ℂ)) ×ˢ Icc (0 : ℝ) 1) :=
  (bh5_segment_image_aux 2 {0} 0 1).2

end HodgeLean.Adapters
