import Mathlib
import HodgeLean.Foundations.Program.RelativeFrameOperatorSectors

set_option maxHeartbeats 400000

noncomputable section
open Set Filter Topology
open scoped BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

open Polynomial

def rf4_unitRoots (n : ℕ) : Finset ℂ :=
  (X ^ n - C (1 : ℂ)).roots.toFinset

theorem rf4_mem_unitRoots (n : ℕ) (hn : 0 < n) (z : ℂ) :
    z ∈ rf4_unitRoots n ↔ z ^ n = 1 := by
  classical
  rw [rf4_unitRoots, Multiset.mem_toFinset,
    Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero hn (1 : ℂ))]
  simp only [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero]

theorem rf4_card_unitRoots (n : ℕ) (hn : 0 < n) : (rf4_unitRoots n).card = n := by
  classical
  have hsep : (X ^ n - C (1 : ℂ)).Separable :=
    Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hn.ne') one_ne_zero
  rw [rf4_unitRoots, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
    IsAlgClosed.card_roots_eq_natDegree]
  exact Polynomial.natDegree_X_pow_sub_C

def rf4_sectorInterpolant (n : ℕ) (f : ℂ → ℂ) (v : ℂ) : Polynomial ℂ :=
  Lagrange.interpolate (rf4_unitRoots n) id (fun ζ ↦ f (v * ζ))

def rf4_sectorValue (n : ℕ) (f : ℂ → ℂ) (v : ℂ) (j : Fin n) : ℂ :=
  (rf4_sectorInterpolant n f v).coeff j / v ^ (j : ℕ)

theorem rf4_sectorValue_recover (n : ℕ) (hn : 0 < n) (f : ℂ → ℂ)
    (v : ℂ) (hv : v ≠ 0) (w : ℂ) (hw : w ^ n = v ^ n) :
    ∑ j : Fin n, w ^ (j : ℕ) * rf4_sectorValue n f v j = f w := by
  classical
  have hm : w / v ∈ rf4_unitRoots n := by
    rw [rf4_mem_unitRoots n hn, div_pow, hw, div_self (pow_ne_zero _ hv)]
  have heval : (rf4_sectorInterpolant n f v).eval (w / v) = f w := by
    have h := Lagrange.eval_interpolate_at_node (fun ζ : ℂ ↦ f (v * ζ))
      Function.injective_id.injOn hm
    simpa only [id_eq, mul_div_cancel₀ _ hv, rf4_sectorInterpolant] using h
  have hdeg : (rf4_sectorInterpolant n f v).natDegree < n := by
    by_cases hp : rf4_sectorInterpolant n f v = 0
    · simpa only [hp, natDegree_zero] using hn
    · apply (Polynomial.natDegree_lt_iff_degree_lt hp).mpr
      have h := Lagrange.degree_interpolate_lt (fun ζ : ℂ ↦ f (v * ζ))
        (Function.injective_id.injOn (s := (rf4_unitRoots n : Set ℂ)))
      simpa only [rf4_sectorInterpolant, rf4_card_unitRoots n hn] using h
  rw [Polynomial.eval_eq_sum_range' hdeg, ← Fin.sum_univ_eq_sum_range] at heval
  convert heval using 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [rf4_sectorValue, div_pow]
  ring

theorem rf4_sectorValue_independent (n : ℕ) (hn : 0 < n) (f : ℂ → ℂ)
    (v : ℂ) (hv : v ≠ 0) (v' : ℂ) (hv' : v' ≠ 0) (hp : v ^ n = v' ^ n) :
    rf4_sectorValue n f v = rf4_sectorValue n f v' := by
  have h := rf4_polynomial_sectors n hn (v ^ n) (pow_ne_zero _ hv)
    (fun j ↦ rf4_sectorValue n f v j - rf4_sectorValue n f v' j) (by
      intro w hw
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, rf4_sectorValue_recover n hn f v hv w hw,
        rf4_sectorValue_recover n hn f v' hv' w (hw.trans hp), sub_self])
  funext j
  exact sub_eq_zero.mp (congrFun h j)

theorem rf4_sectorInterpolant_coeff (n : ℕ) (f : ℂ → ℂ) (v : ℂ) (j : ℕ) :
    (rf4_sectorInterpolant n f v).coeff j =
      ∑ ζ ∈ rf4_unitRoots n, f (v * ζ) * (Lagrange.basis (rf4_unitRoots n) id ζ).coeff j := by
  classical
  simp only [rf4_sectorInterpolant, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul]

def rf4_interpolationBound (n j : ℕ) : ℝ :=
  ∑ ζ ∈ rf4_unitRoots n, ‖(Lagrange.basis (rf4_unitRoots n) id ζ).coeff j‖

theorem rf4_sectorInterpolant_bound (n : ℕ) (f : ℂ → ℂ) (v : ℂ) (j : ℕ) (B : ℝ)
    (hB : ∀ ζ ∈ rf4_unitRoots n, ‖f (v * ζ)‖ ≤ B) :
    ‖(rf4_sectorInterpolant n f v).coeff j‖ ≤ B * rf4_interpolationBound n j := by
  classical
  rw [rf4_sectorInterpolant_coeff]
  calc
    _ ≤ ∑ ζ ∈ rf4_unitRoots n, ‖f (v * ζ) *
        (Lagrange.basis (rf4_unitRoots n) id ζ).coeff j‖ := norm_sum_le _ _
    _ ≤ ∑ ζ ∈ rf4_unitRoots n, B *
        ‖(Lagrange.basis (rf4_unitRoots n) id ζ).coeff j‖ := by
      apply Finset.sum_le_sum
      intro ζ hζ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB ζ hζ) (norm_nonneg _)
    _ = B * rf4_interpolationBound n j := (Finset.mul_sum _ _ _).symm

theorem rf4_sectorValue_differentiableAt (n : ℕ) (f v : ℂ → ℂ) (j : Fin n) (x : ℂ)
    (hv : DifferentiableAt ℂ v x) (hv0 : v x ≠ 0)
    (hf : ∀ ζ ∈ rf4_unitRoots n, DifferentiableAt ℂ f (v x * ζ)) :
    DifferentiableAt ℂ (fun y ↦ rf4_sectorValue n f (v y) j) x := by
  classical
  simp_rw [rf4_sectorValue, rf4_sectorInterpolant_coeff]
  apply DifferentiableAt.div _ (hv.pow _) (pow_ne_zero _ hv0)
  apply DifferentiableAt.fun_sum
  intro ζ hζ
  exact ((hf ζ hζ).comp x (hv.mul_const ζ)).mul_const _

def rf4_powerRoot (n : ℕ) (y : ℂ) : ℂ := y ^ ((n : ℂ)⁻¹)

theorem rf4_powerRoot_pow (n : ℕ) (hn : 0 < n) (y : ℂ) :
    rf4_powerRoot n y ^ n = y :=
  Complex.cpow_nat_inv_pow y hn.ne'

theorem rf4_powerRoot_continuousAt_zero (n : ℕ) (hn : 0 < n) :
    ContinuousAt (rf4_powerRoot n) 0 := by
  apply Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simp))
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
    using (inv_pos.mpr hnreal)

def rf4_rawSector (n : ℕ) (f : ℂ → ℂ) (j : Fin n) (y : ℂ) : ℂ :=
  rf4_sectorValue n f (rf4_powerRoot n y) j

theorem rf4_rawSector_root (n : ℕ) (hn : 0 < n) (f : ℂ → ℂ) (j : Fin n)
    (y : ℂ) (hy : y ≠ 0) (v : ℂ) (hv : v ^ n = y) :
    rf4_rawSector n f j y = rf4_sectorValue n f v j := by
  have hv0 : v ≠ 0 := by
    intro h
    apply hy
    rw [← hv, h, zero_pow hn.ne']
  have hr0 : rf4_powerRoot n y ≠ 0 := by
    intro h
    apply hy
    rw [← rf4_powerRoot_pow n hn y, h, zero_pow hn.ne']
  exact congrFun (rf4_sectorValue_independent n hn f (rf4_powerRoot n y) hr0 v hv0
    ((rf4_powerRoot_pow n hn y).trans hv.symm)) j

theorem rf4_rawSector_differentiableAt (n : ℕ) (hn : 0 < n) (U : Set ℂ) (hU : IsOpen U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f ((fun w : ℂ ↦ w ^ n) ⁻¹' U))
    (j : Fin n) (y : ℂ) (hy : y ∈ U) (hy0 : y ≠ 0) :
    DifferentiableAt ℂ (rf4_rawSector n f j) y := by
  let v : ℂ → ℂ := fun z ↦ rf4_powerRoot n y * rf4_powerRoot n (z / y)
  have hvpow : ∀ z, v z ^ n = z := by
    intro z
    dsimp only [v]
    rw [mul_pow, rf4_powerRoot_pow n hn, rf4_powerRoot_pow n hn]
    field_simp
  have hv0 : v y ≠ 0 := by
    intro h
    apply hy0
    rw [← hvpow y, h, zero_pow hn.ne']
  have hv : DifferentiableAt ℂ v y := by
    dsimp only [v, rf4_powerRoot]
    apply (differentiableAt_const _).mul
    exact (differentiableAt_id.div_const y).cpow_const (by simp only [div_self hy0,
      Complex.one_mem_slitPlane])
  have hd := rf4_sectorValue_differentiableAt n f v j y hv hv0 (by
    intro ζ hζ
    have hm : (v y * ζ) ^ n ∈ U := by
      rw [mul_pow, hvpow y, (rf4_mem_unitRoots n hn ζ).mp hζ, mul_one]
      exact hy
    exact (hf _ hm).differentiableAt ((hU.preimage (continuous_pow n)).mem_nhds hm))
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hy0] with z hz
  exact rf4_rawSector_root n hn f j z hz (v z) (hvpow z)

theorem rf4_rawSector_growth (n : ℕ) (hn : 0 < n) (U : Set ℂ) (f : ℂ → ℂ)
    (B : ℝ) (hB : ∀ w : ℂ, w ^ n ∈ U → ‖f w‖ ≤ B) (j : Fin n)
    (y : ℂ) (hy : y ∈ U) (hy0 : y ≠ 0) :
    ‖y * rf4_rawSector n f j y‖ ≤
      ‖rf4_powerRoot n y‖ ^ (n - (j : ℕ)) * (B * rf4_interpolationBound n j) := by
  let v := rf4_powerRoot n y
  have hvpow : v ^ n = y := rf4_powerRoot_pow n hn y
  have hv0 : v ≠ 0 := by
    intro h
    apply hy0
    rw [← hvpow, h, zero_pow hn.ne']
  have hcoeff : ‖(rf4_sectorInterpolant n f v).coeff j‖ ≤
      B * rf4_interpolationBound n j := by
    apply rf4_sectorInterpolant_bound
    intro ζ hζ
    apply hB
    rw [mul_pow, hvpow, (rf4_mem_unitRoots n hn ζ).mp hζ, mul_one]
    exact hy
  have hpow : v ^ n = v ^ (n - (j : ℕ)) * v ^ (j : ℕ) := by
    rw [← pow_add, Nat.sub_add_cancel j.isLt.le]
  have heq : y * rf4_rawSector n f j y =
      v ^ (n - (j : ℕ)) * (rf4_sectorInterpolant n f v).coeff j := by
    change y * ((rf4_sectorInterpolant n f v).coeff j / v ^ (j : ℕ)) = _
    rw [← hvpow, hpow]
    field_simp [pow_ne_zero _ hv0]
  rw [heq, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left hcoeff (pow_nonneg (norm_nonneg _) _)

theorem rf4_rawSector_mul_tendsto_zero (n : ℕ) (hn : 0 < n) (U : Set ℂ)
    (hU0 : U ∈ 𝓝 (0 : ℂ)) (f : ℂ → ℂ) (B : ℝ)
    (hB : ∀ w : ℂ, w ^ n ∈ U → ‖f w‖ ≤ B) (j : Fin n) :
    Tendsto (fun y ↦ y * rf4_rawSector n f j y) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  have hr0 : rf4_powerRoot n 0 = 0 :=
    (pow_eq_zero_iff hn.ne').mp (rf4_powerRoot_pow n hn 0)
  have hlim : Tendsto (fun y : ℂ ↦ ‖rf4_powerRoot n y‖ ^ (n - (j : ℕ)) *
      (B * rf4_interpolationBound n j)) (𝓝[≠] 0) (𝓝 0) := by
    have h := (((rf4_powerRoot_continuousAt_zero n hn).norm.pow
      (n - (j : ℕ))).tendsto).mul_const (B * rf4_interpolationBound n j)
    simpa only [Pi.pow_apply, hr0, norm_zero, zero_pow (show n - (j : ℕ) ≠ 0 by omega), zero_mul]
      using h.mono_left (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply squeeze_zero_norm' _ hlim
  have hev : ∀ᶠ y in 𝓝[≠] (0 : ℂ), y ∈ U := mem_nhdsWithin_of_mem_nhds hU0
  filter_upwards [hev, self_mem_nhdsWithin] with y hy hy0
  exact rf4_rawSector_growth n hn U f B hB j y hy hy0

theorem rf4_rawSector_littleO (n : ℕ) (hn : 0 < n) (U : Set ℂ)
    (hU0 : U ∈ 𝓝 (0 : ℂ)) (f : ℂ → ℂ) (B : ℝ)
    (hB : ∀ w : ℂ, w ^ n ∈ U → ‖f w‖ ≤ B) (j : Fin n) :
    (fun y ↦ rf4_rawSector n f j y - rf4_rawSector n f j 0) =o[𝓝[≠] (0 : ℂ)]
      (fun y ↦ (y - 0)⁻¹) := by
  apply (Asymptotics.isLittleO_iff_tendsto (fun y hy ↦ by
    have hy0 : y = 0 := by simpa only [sub_zero, inv_eq_zero] using hy
    simp only [hy0, sub_self])).mpr
  have hlin : Tendsto (fun y : ℂ ↦ y * rf4_rawSector n f j 0)
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [id_eq, zero_mul] using
      (continuousAt_id.tendsto.mul_const (rf4_rawSector n f j 0)).mono_left
        (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have heq : (fun y : ℂ ↦ (rf4_rawSector n f j y - rf4_rawSector n f j 0) / (y - 0)⁻¹) =
      (fun y ↦ y * rf4_rawSector n f j y - y * rf4_rawSector n f j 0) := by
    funext y
    simp only [sub_zero, div_inv_eq_mul]
    ring
  rw [heq]
  simpa only [sub_zero] using (rf4_rawSector_mul_tendsto_zero n hn U hU0 f B hB j).sub hlin

def rf4_descendedSector (n : ℕ) (f : ℂ → ℂ) (j : Fin n) : ℂ → ℂ :=
  Function.update (rf4_rawSector n f j) 0 (limUnder (𝓝[≠] (0 : ℂ)) (rf4_rawSector n f j))

theorem rf4_descendedSector_differentiableOn (n : ℕ) (hn : 0 < n) (U : Set ℂ)
    (hU : IsOpen U) (hU0 : (0 : ℂ) ∈ U) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ((fun w : ℂ ↦ w ^ n) ⁻¹' U)) (B : ℝ)
    (hB : ∀ w : ℂ, w ^ n ∈ U → ‖f w‖ ≤ B) (j : Fin n) :
    DifferentiableOn ℂ (rf4_descendedSector n f j) U := by
  apply Complex.differentiableOn_update_limUnder_of_isLittleO (hU.mem_nhds hU0)
  · intro y hy
    exact (rf4_rawSector_differentiableAt n hn U hU f hf j y hy.1 hy.2).differentiableWithinAt
  · exact rf4_rawSector_littleO n hn U (hU.mem_nhds hU0) f B hB j

theorem rf4_powerRoot_lower_bound (n : ℕ) (hn : 0 < n) (d : ℝ) (y : ℂ)
    (hy : d ≤ ‖y‖) : min 1 d ≤ ‖rf4_powerRoot n y‖ := by
  by_cases h : 1 ≤ ‖rf4_powerRoot n y‖
  · exact (min_le_left _ _).trans h
  · have hp : ‖y‖ ≤ ‖rf4_powerRoot n y‖ := by
      calc
        ‖y‖ = ‖rf4_powerRoot n y‖ ^ n := by rw [← norm_pow, rf4_powerRoot_pow n hn]
        _ ≤ ‖rf4_powerRoot n y‖ :=
          pow_le_of_le_one (norm_nonneg _) (le_of_not_ge h) hn.ne'
    exact (min_le_right _ _).trans (hy.trans hp)

theorem rf4_descendedSector_bddAbove (n : ℕ) (hn : 0 < n) (U : Set ℂ)
    (hU : IsOpen U) (hU0 : (0 : ℂ) ∈ U) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ((fun w : ℂ ↦ w ^ n) ⁻¹' U)) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ w : ℂ, w ^ n ∈ U → ‖f w‖ ≤ B) (j : Fin n) :
    BddAbove ((fun y ↦ ‖rf4_descendedSector n f j y‖) '' U) := by
  classical
  have hG := rf4_descendedSector_differentiableOn n hn U hU hU0 f hf B hB j
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hU0)
  have hKU : Metric.closedBall (0 : ℂ) (δ / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith : δ / 2 < δ)).trans hδU
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : ℂ) (δ / 2)).exists_bound_of_continuousOn
    (hG.continuousOn.mono hKU)
  let d : ℝ := min 1 (δ / 2)
  let K : ℝ := B * rf4_interpolationBound n j
  have hd : 0 < d := lt_min zero_lt_one (half_pos hδ)
  have hK : 0 ≤ K := mul_nonneg hB0 (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
  refine ⟨max A (K / d ^ (j : ℕ)), ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  by_cases hnear : ‖y‖ ≤ δ / 2
  · exact (hA y (by simpa only [Metric.mem_closedBall, dist_zero_right] using hnear)).trans
      (le_max_left _ _)
  · have hy0 : y ≠ 0 := by
      intro h
      subst y
      simp only [norm_zero] at hnear
      exact hnear (half_pos hδ).le
    have hroot : d ≤ ‖rf4_powerRoot n y‖ :=
      rf4_powerRoot_lower_bound n hn (δ / 2) y (le_of_lt (lt_of_not_ge hnear))
    have hcoeff : ‖(rf4_sectorInterpolant n f (rf4_powerRoot n y)).coeff j‖ ≤ K := by
      apply rf4_sectorInterpolant_bound
      intro ζ hζ
      apply hB
      rw [mul_pow, rf4_powerRoot_pow n hn, (rf4_mem_unitRoots n hn ζ).mp hζ, mul_one]
      exact hy
    change ‖rf4_descendedSector n f j y‖ ≤ max A (K / d ^ (j : ℕ))
    rw [rf4_descendedSector, Function.update_of_ne hy0]
    calc
      _ = ‖(rf4_sectorInterpolant n f (rf4_powerRoot n y)).coeff j‖ /
          ‖rf4_powerRoot n y‖ ^ (j : ℕ) := by
        simp only [rf4_rawSector, rf4_sectorValue, norm_div, norm_pow]
      _ ≤ K / ‖rf4_powerRoot n y‖ ^ (j : ℕ) :=
        div_le_div_of_nonneg_right hcoeff (by positivity)
      _ ≤ K / d ^ (j : ℕ) := div_le_div_of_nonneg_left hK (pow_pos hd _)
        (pow_le_pow_left₀ hd.le hroot _)
      _ ≤ max A (K / d ^ (j : ℕ)) := le_max_right _ _

theorem rf4_descendedSector_recover (n : ℕ) (hn : 0 < n) (U : Set ℂ)
    (hU : IsOpen U) (hU0 : (0 : ℂ) ∈ U) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ((fun w : ℂ ↦ w ^ n) ⁻¹' U)) (B : ℝ)
    (hB : ∀ w : ℂ, w ^ n ∈ U → ‖f w‖ ≤ B) (w : ℂ) (hw : w ^ n ∈ U) :
    f w = ∑ j : Fin n, w ^ (j : ℕ) * rf4_descendedSector n f j (w ^ n) := by
  classical
  have hf' : ContinuousAt f w :=
    ((hf w hw).differentiableAt ((hU.preimage (continuous_pow n)).mem_nhds hw)).continuousAt
  have hsum : ContinuousAt (fun z : ℂ ↦
      ∑ j : Fin n, z ^ (j : ℕ) * rf4_descendedSector n f j (z ^ n)) w := by
    apply DifferentiableAt.continuousAt (𝕜 := ℂ)
    apply DifferentiableAt.fun_sum
    intro j _
    have hG := rf4_descendedSector_differentiableOn n hn U hU hU0 f hf B hB j
    exact (differentiableAt_pow _).mul
      ((hG.differentiableAt (hU.mem_nhds hw)).comp w (differentiableAt_pow n))
  apply sub_eq_zero.mp
  apply (hf'.sub hsum).continuousWithinAt.eq_const_of_mem_closure
    ((dense_compl_singleton (0 : ℂ)) w)
  intro z hz0
  have hy0 : z ^ n ≠ 0 := pow_ne_zero _ hz0
  have hr0 : rf4_powerRoot n (z ^ n) ≠ 0 := by
    intro h
    apply hy0
    rw [← rf4_powerRoot_pow n hn (z ^ n), h, zero_pow hn.ne']
  have hrec := rf4_sectorValue_recover n hn f (rf4_powerRoot n (z ^ n)) hr0 z
    (rf4_powerRoot_pow n hn (z ^ n)).symm
  have heq : ∀ j : Fin n, rf4_descendedSector n f j (z ^ n) =
      rf4_sectorValue n f (rf4_powerRoot n (z ^ n)) j := by
    intro j
    rw [rf4_descendedSector, Function.update_of_ne hy0]
    rfl
  change f z - ∑ j : Fin n, z ^ (j : ℕ) * rf4_descendedSector n f j (z ^ n) = 0
  simp_rw [heq]
  exact sub_eq_zero.mpr hrec.symm

def rf4_bddHolOfBddAbove (U : Set ℂ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (hb : BddAbove ((fun z ↦ ‖f z‖) '' U)) : b63r_bddHol U :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroup (fun z : U ↦ f z)
    hf.continuousOn.domRestrict (Classical.choose hb)
    (fun z ↦ Classical.choose_spec hb (Set.mem_image_of_mem _ z.property)),
    ⟨f, hf, fun _ ↦ rfl⟩⟩

theorem rf4_bddHolOfBddAbove_apply (U : Set ℂ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (hb : BddAbove ((fun z ↦ ‖f z‖) '' U)) (z : U) :
    ((rf4_bddHolOfBddAbove U f hf hb : b63r_bddHol U) : U →ᵇ ℂ) z = f z := rfl

theorem rf4_sector_surjective_core (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) (c ε : ℂ)
    (hε : ‖ε‖ < r) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (rf4_innerDisc n r ε))
    (hb : BddAbove ((fun w ↦ ‖f w‖) '' rf4_innerDisc n r ε)) :
    ∃ g : Fin n → b63r_bddHol (Metric.ball c (2 * r)), ∀ w ∈ rf4_innerDisc n r ε,
      f w = rf4_sectorCoeff n (fun j ↦ rf4_extendBdd (g j)) (c + ε) w := by
  classical
  have hn0 : 0 < n := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  let U : Set ℂ := {y | ‖y + ε‖ < 2 * r}
  have hU : IsOpen U := isOpen_lt ((continuous_id.add continuous_const).norm) continuous_const
  have hU0 : (0 : ℂ) ∈ U := by
    change ‖0 + ε‖ < 2 * r
    rw [zero_add]
    linarith
  have hfU : DifferentiableOn ℂ f ((fun w : ℂ ↦ w ^ n) ⁻¹' U) := hf
  obtain ⟨B, hB⟩ := hb
  have hbound : ∀ w : ℂ, w ^ n ∈ U → ‖f w‖ ≤ max 0 B := by
    intro w hw
    exact (hB (Set.mem_image_of_mem _ (show w ∈ rf4_innerDisc n r ε from hw))).trans
      (le_max_right _ _)
  let H : Fin n → b63r_bddHol U := fun j ↦
    rf4_bddHolOfBddAbove U (rf4_descendedSector n f j)
      (rf4_descendedSector_differentiableOn n hn0 U hU hU0 f hfU (max 0 B) hbound j)
      (rf4_descendedSector_bddAbove n hn0 U hU hU0 f hfU (max 0 B) (le_max_left _ _) hbound j)
  let ψ : ℂ → ℂ := fun z ↦ z - (c + ε)
  have hψ : DifferentiableOn ℂ ψ (Metric.ball c (2 * r)) :=
    (differentiable_id.sub_const (c + ε)).differentiableOn
  have hmaps : MapsTo ψ (Metric.ball c (2 * r)) U := by
    intro z hz
    change ‖z - (c + ε) + ε‖ < 2 * r
    rw [show z - (c + ε) + ε = z - c by ring]
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  let g : Fin n → b63r_bddHol (Metric.ball c (2 * r)) :=
    fun j ↦ (n : ℂ)⁻¹ • b63r_bddHol_comp ψ hψ hmaps (H j)
  have hg : ∀ (j : Fin n) (z : ℂ) (hz : z ∈ Metric.ball c (2 * r)),
      rf4_extendBdd (g j) z = (n : ℂ)⁻¹ * rf4_descendedSector n f j (ψ z) := by
    intro j z hz
    rw [rf4_extendBdd, dite_eq_left hz]
    rfl
  refine ⟨g, ?_⟩
  intro w hw
  have hz : c + ε + w ^ n ∈ Metric.ball c (2 * r) := by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show c + ε + w ^ n - c = w ^ n + ε by ring]
    exact hw
  have heval : ∀ j : Fin n, rf4_extendBdd (g j) (c + ε + w ^ n) =
      (n : ℂ)⁻¹ * rf4_descendedSector n f j (w ^ n) := by
    intro j
    rw [hg j _ hz, show ψ (c + ε + w ^ n) = w ^ n by dsimp only [ψ]; ring]
  rw [rf4_sectorCoeff]
  simp_rw [heval]
  rw [Finset.mul_sum, rf4_descendedSector_recover n hn0 U hU hU0 f hfU (max 0 B) hbound w hw]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [hnC]

end HodgeLean.Foundations.Program
