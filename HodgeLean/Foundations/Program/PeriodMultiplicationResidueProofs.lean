import HodgeLean.Foundations.Program.PeriodMultiplicationScalarProofs
import HodgeLean.Ported.TauCeti.TauCeti.Analysis.Contour.Residue.LogDeriv

noncomputable section
open Set Filter Topology Manifold
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

attribute [local instance] b3Forms_isManifold_real

theorem b66m_rs_clm_apply (L : ℂ →L[ℂ] ℂ) (v : ℂ) : L v = v * L 1 := by
  have : v = v • (1 : ℂ) := by simp
  conv_lhs => rw [this]
  rw [map_smul, smul_eq_mul]

theorem b66m_rs_transition_hasDerivAt (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (z : ℂ)
    (hz : (t.val, z) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source) :
    HasDerivAt (fun w => b66k_transition R a b (t.val, w))
      (fderiv ℂ (b66k_transition R a b) (t.val, z) (0, 1)) z := by
  have hd := (b66k_transition_analytic R a b _ hz).differentiableAt.hasFDerivAt
  have hi : HasDerivAt (fun w : ℂ => ((t.val, w) : (Fin 10 → ℂ) × ℂ)) (0, 1) z :=
    (hasDerivAt_const z t.val).prodMk (hasDerivAt_id z)
  exact hd.comp_hasDerivAt z hi

theorem b66m_rs_slice_change (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (p : rf8_fibre R.C t)
    (ha : p.val ∈ (R.atlas.A a).source) (hb : p.val ∈ (R.atlas.A b).source) (v : ℂ) :
    b66m_sc_sliceD R t b p v = b66k_vertical R t a b p.val.2 * b66m_sc_sliceD R t a p v := by
  set g : ℂ → ℂ := fun w => b66k_transition R a b (t.val, w)
  have hpa := b66m_sc_slice_value R t a p ha
  have hz : (t.val, b66m_sc_slice R t a p) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨?_, ?_⟩
    · change (t.val, (R.atlas.A a p.val).2) ∈ (R.atlas.A a).target
      rw [← hpa]
      exact (R.atlas.A a).map_source ha
    · change (R.atlas.A a).symm (t.val, (R.atlas.A a p.val).2) ∈ (R.atlas.A b).source
      rw [← hpa, (R.atlas.A a).left_inv ha]
      exact hb
  have hg := b66m_rs_transition_hasDerivAt R t a b _ hz
  have hopen : IsOpen {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A a).source} :=
    (R.atlas.A a).open_source.preimage continuous_subtype_val
  have heq : b66m_sc_slice R t b =ᶠ[𝓝 p] g ∘ b66m_sc_slice R t a := by
    filter_upwards [hopen.mem_nhds ha] with y hy
    change (R.atlas.A b y.val).2 =
      (R.atlas.A b ((R.atlas.A a).symm (t.val, (R.atlas.A a y.val).2))).2
    rw [← b66m_sc_slice_value R t a y hy, (R.atlas.A a).left_inv hy]
  have hmg : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (b66m_sc_slice R t a p) :=
    mdifferentiableAt_iff_differentiableAt.mpr hg.differentiableAt
  have hma : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66m_sc_slice R t a) p :=
    (b66m_sc_slice_contMDiffAt R t a p ha).mdifferentiableAt (by simp)
  have hH : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66m_sc_slice R t b) p
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        (fderiv ℂ (b66k_transition R a b) (t.val, b66m_sc_slice R t a p) (0, 1))).comp
        (b66m_sc_sliceD R t a p)) :=
    (HasMFDerivAt.comp (g := g) (f := b66m_sc_slice R t a) p hg.hasFDerivAt.hasMFDerivAt
      hma.hasMFDerivAt).congr_of_eventuallyEq_abuse heq
  unfold b66m_sc_sliceD at hH ⊢
  rw [hH.mfderiv]
  have hv : fderiv ℂ (b66k_transition R a b) (t.val, b66m_sc_slice R t a p) (0, 1) =
      b66k_vertical R t a b p.val.2 := by
    change _ = fderiv ℂ (b66k_transition R a b) (R.atlas.A a (t, p.val.2)) (0, 1)
    rw [← b66m_sc_fibre_val R t p]
    exact congrArg (fun u => fderiv ℂ (b66k_transition R a b) u (0, 1)) hpa.symm
  rw [← hv]
  exact mul_comm (b66m_sc_sliceD R t a p v) _

theorem b66m_rs_mem_source (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (p : rf8_fibre R.C t) :
    p.val ∈ (R.atlas.A a).source ↔ (t, p.val.2) ∈ (R.atlas.A a).source := by
  rw [← b66m_sc_fibre_val R t p]

theorem b66m_rs_chartD_vec (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (x₀ y : rf8_fibre R.C t) (hy : y ∈ (extChartAt 𝓘(ℂ, ℂ) x₀).source) (u : ℂ) :
    b66m_sc_chartD R t x₀ y (b4cov_vec x₀ y u) = u :=
  (b4cov_triv_eq_mfderiv x₀ y hy (b4cov_vec x₀ y u)).symm.trans (b4cov_triv_vec x₀ y hy u)

theorem b66m_rs_dslope_analytic {D : ℂ → ℂ} {z₀ : ℂ} (hD : AnalyticAt ℂ D z₀) :
    AnalyticAt ℂ (dslope D z₀) z₀ := by
  obtain ⟨p, hp⟩ := hD
  exact hp.has_fpower_series_dslope_fslope.analyticAt

theorem b66m_rs_taylor {φ : ℂ → ℂ} {w₀ : ℂ} (hφ : AnalyticAt ℂ φ w₀) (N : ℕ) :
    ∃ (a : Fin N → ℂ) (ρ : ℂ → ℂ), AnalyticAt ℂ ρ w₀ ∧
      ∀ w, φ w = ∑ i : Fin N, a i * (w - w₀) ^ (i : ℕ) + (w - w₀) ^ N * ρ w := by
  induction N with
  | zero => exact ⟨Fin.elim0, φ, hφ, fun w => by simp⟩
  | succ N ih =>
    obtain ⟨a, ρ, hρ, h⟩ := ih
    refine ⟨Fin.snoc a (ρ w₀), dslope ρ w₀, b66m_rs_dslope_analytic hρ, fun w => ?_⟩
    rw [h w, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    have hs := sub_smul_dslope ρ w₀ w
    rw [smul_eq_mul] at hs
    have : ρ w = ρ w₀ + (w - w₀) * dslope ρ w₀ w := by rw [hs]; ring
    rw [this, pow_succ]
    ring

theorem b66m_rs_principal_part {f : ℂ → ℂ} {w₀ : ℂ} (hf : MeromorphicAt f w₀) :
    ∃ (N : ℕ) (c : Fin N → ℂ) (ρ : ℂ → ℂ), AnalyticAt ℂ ρ w₀ ∧
      ∀ᶠ w in 𝓝[≠] w₀, f w = ρ w + ∑ k : Fin N, c k / (w - w₀) ^ (k.val + 1) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ((-(N : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f w₀ := by
    rcases eq_or_ne (meromorphicOrderAt f w₀) ⊤ with h | h
    · exact ⟨0, by rw [h]; exact le_top⟩
    · set a := (meromorphicOrderAt f w₀).untop₀
      have ha : meromorphicOrderAt f w₀ = (a : WithTop ℤ) :=
        (WithTop.coe_untop₀_of_ne_top h).symm
      refine ⟨(-a).toNat, ?_⟩
      rw [ha, WithTop.coe_le_coe]
      omega
  obtain ⟨φ, hφ, hfφ⟩ := TauCeti.Contour.exists_analyticAt_eventuallyEq_zpow_smul hf hN
  obtain ⟨a, ρ, hρ, hφe⟩ := b66m_rs_taylor hφ N
  refine ⟨N, fun k => a (Fin.rev k), ρ, hρ, ?_⟩
  filter_upwards [hfφ, self_mem_nhdsWithin] with w hw hne
  have he : w - w₀ ≠ 0 := sub_ne_zero.mpr hne
  rw [hw, hφe w, smul_eq_mul, mul_add, Finset.mul_sum]
  have hre := Equiv.sum_comp Fin.revPerm (fun k : Fin N => a (Fin.rev k) / (w - w₀) ^ (k.val + 1))
  simp only [Fin.revPerm_apply, Fin.rev_rev] at hre
  rw [← hre, zpow_neg, zpow_natCast, add_comm]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (Fin.rev i).val + 1 + i.val = N := by
      rw [Fin.val_rev]
      omega
    have hpow : (w - w₀) ^ N = (w - w₀) ^ ((Fin.rev i).val + 1) * (w - w₀) ^ (i : ℕ) := by
      rw [← pow_add, hi]
    rw [hpow]
    field_simp

theorem b66m_rs_residue_simple {D : ℂ → ℂ} {z₀ : ℂ} (hD : AnalyticAt ℂ D z₀)
    (hD' : deriv D z₀ ≠ 0) :
    TauCeti.Contour.residue (fun z => deriv D z / (D z - D z₀) ^ (0 + 1)) z₀ = 1 := by
  have hm : MeromorphicAt (fun z => D z - D z₀) z₀ := (hD.sub analyticAt_const).meromorphicAt
  have hord : meromorphicOrderAt (fun z => D z - D z₀) z₀ = ((1 : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_eq_int_iff hm]
    refine ⟨dslope D z₀, b66m_rs_dslope_analytic hD, by rwa [dslope_same], ?_⟩
    exact Filter.Eventually.of_forall fun z => by
      rw [zpow_one, sub_smul_dslope]
  have h := TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt hm hord
  rw [Int.cast_one] at h
  rw [← h]
  congr 1
  funext z
  simp only [logDeriv_apply, zero_add, pow_one]
  rw [deriv_sub_const]

theorem b66m_rs_residue_higher {D : ℂ → ℂ} {z₀ : ℂ} (hD : AnalyticAt ℂ D z₀)
    (hD' : deriv D z₀ ≠ 0) (i : ℕ) :
    TauCeti.Contour.residue (fun z => deriv D z / (D z - D z₀) ^ (i + 1 + 1)) z₀ = 0 := by
  have hψ0 : dslope D z₀ z₀ ≠ 0 := by rwa [dslope_same]
  set ψ := dslope D z₀
  have hψ : AnalyticAt ℂ ψ z₀ := b66m_rs_dslope_analytic hD
  have hDψ : ∀ z, D z - D z₀ = (z - z₀) * ψ z := fun z => by
    rw [← smul_eq_mul, sub_smul_dslope]
  have hDfun : D = fun z => D z₀ + (z - z₀) * ψ z := by
    funext z
    rw [← hDψ z]
    ring
  set χ : ℂ → ℂ := fun z => (ψ z ^ (i + 1))⁻¹
  have hχ : AnalyticAt ℂ χ z₀ := (hψ.pow (i + 1)).inv (pow_ne_zero _ hψ0)
  have hev : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ ψ z ∧ ψ z ≠ 0 :=
    hψ.eventually_analyticAt.and (hψ.continuousAt.eventually_ne hψ0)
  have hkey : (fun z => deriv D z / (D z - D z₀) ^ (i + 1 + 1)) =ᶠ[𝓝[≠] z₀]
      (fun z => (z - z₀) ^ (-((i + 2 : ℕ) : ℤ)) • χ z) +
      (fun z => (z - z₀) ^ (-((i + 1 : ℕ) : ℤ)) •
        ((-(1 / ((i : ℂ) + 1))) * deriv χ z)) := by
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with z ⟨hza, hzn⟩ hz
    have he : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    have hdD : deriv D z = ψ z + (z - z₀) * deriv ψ z := by
      rw [hDfun]
      have h1 : HasDerivAt (fun z => D z₀ + (z - z₀) * ψ z)
          (1 * ψ z + (z - z₀) * deriv ψ z) z :=
        (((hasDerivAt_id z).sub_const z₀).mul hza.differentiableAt.hasDerivAt).const_add _
      rw [h1.deriv, one_mul]
    have hdχ : deriv χ z = -(((i + 1 : ℕ) : ℂ) * ψ z ^ i * deriv ψ z) /
        (ψ z ^ (i + 1)) ^ 2 := by
      have h2 := ((hza.differentiableAt.hasDerivAt.pow (i + 1)).inv (pow_ne_zero _ hzn)).deriv
      simp only [Pi.pow_apply, Nat.add_sub_cancel] at h2
      exact h2
    simp only [Pi.add_apply, smul_eq_mul, χ]
    rw [hdD, hdχ, hDψ z, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_pow]
    push_cast
    field_simp
    ring
  rw [TauCeti.Contour.residue_congr_nhdsNE hkey]
  have hm1 : MeromorphicAt (fun z => (z - z₀) ^ (-((i + 2 : ℕ) : ℤ)) • χ z) z₀ :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow _).smul hχ.meromorphicAt
  have hχd : AnalyticAt ℂ (fun z => (-(1 / ((i : ℂ) + 1))) * deriv χ z) z₀ :=
    analyticAt_const.mul hχ.deriv
  have hm2 : MeromorphicAt (fun z => (z - z₀) ^ (-((i + 1 : ℕ) : ℤ)) •
      ((-(1 / ((i : ℂ) + 1))) * deriv χ z)) z₀ :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow _).smul hχd.meromorphicAt
  rw [TauCeti.Contour.residue_add hm1 hm2,
    TauCeti.Contour.residue_eq_of_eventuallyEq_zpow_smul (by omega) hχ
      (Filter.Eventually.of_forall fun _ => rfl),
    TauCeti.Contour.residue_eq_of_eventuallyEq_zpow_smul (by omega) hχd
      (Filter.Eventually.of_forall fun _ => rfl)]
  have ht1 : (-1 - (-((i + 2 : ℕ) : ℤ))).toNat = i + 1 := by omega
  have ht2 : (-1 - (-((i + 1 : ℕ) : ℤ))).toNat = i := by omega
  rw [ht1, ht2, iteratedDeriv_const_mul_field, ← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  have hf : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hi : (i : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
  field_simp
  ring

theorem b66m_rs_residue_comp {D f : ℂ → ℂ} {z₀ : ℂ} (hD : AnalyticAt ℂ D z₀)
    (hD' : deriv D z₀ ≠ 0) (hf : MeromorphicAt f (D z₀)) :
    TauCeti.Contour.residue (fun z => f (D z) * deriv D z) z₀ =
      TauCeti.Contour.residue f (D z₀) := by
  obtain ⟨N, c, ρ, hρ, hfe⟩ := b66m_rs_principal_part hf
  rw [TauCeti.Contour.residue_of_laurent_expansion hρ hfe]
  have hT := hD.differentiableAt.hasDerivAt.tendsto_nhdsNE hD'
  have hcomp : (fun z => f (D z) * deriv D z) =ᶠ[𝓝[≠] z₀]
      (fun z => ρ (D z) * deriv D z) +
        ∑ k : Fin N, fun z => c k * (deriv D z / (D z - D z₀) ^ (k.val + 1)) := by
    filter_upwards [hT.eventually hfe] with z hz
    rw [hz, Pi.add_apply, Finset.sum_apply, add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hmk : ∀ k : Fin N, MeromorphicAt
      (fun z => c k * (deriv D z / (D z - D z₀) ^ (k.val + 1))) z₀ := fun k =>
    analyticAt_const.meromorphicAt.mul (hD.deriv.meromorphicAt.div
      ((hD.sub analyticAt_const).pow _).meromorphicAt)
  have hρD : AnalyticAt ℂ (fun z => ρ (D z) * deriv D z) z₀ :=
    (AnalyticAt.comp (f := D) hρ hD).mul hD.deriv
  rw [TauCeti.Contour.residue_congr_nhdsNE hcomp,
    TauCeti.Contour.residue_add hρD.meromorphicAt
      (MeromorphicAt.sum fun k _ => hmk k),
    TauCeti.Contour.residue_eq_zero_of_analyticAt hρD, zero_add,
    TauCeti.Contour.residue_sum _ fun k _ => hmk k]
  simp only [TauCeti.Contour.residue_const_mul]
  have hval : ∀ k : Fin N, TauCeti.Contour.residue
      (fun z => deriv D z / (D z - D z₀) ^ (k.val + 1)) z₀ = if k.val = 0 then 1 else 0 := by
    intro k
    rcases Nat.eq_zero_or_eq_succ_pred k.val with h | h
    · rw [ite_eq_left h, h]
      exact b66m_rs_residue_simple hD hD'
    · rw [ite_eq_right (by omega), h]
      exact b66m_rs_residue_higher hD hD' _
  simp only [hval, mul_ite, mul_one, mul_zero]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  · rw [dite_eq_left hN, Finset.sum_eq_single ⟨0, hN⟩]
    · simp
    · intro k _ hk
      exact ite_eq_right fun h0 => hk (Fin.ext h0)
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem b66m_rs_lineEquiv_apply (τ : ℂ) :
    b4cov_lineEquiv (Module.finrank_self ℂ) τ = τ * b4cov_lineEquiv (Module.finrank_self ℂ) 1 := by
  rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

def b66m_rs_cform (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (C : b66k_Index R → ℂ → ℂ) : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ := fun q =>
  C q.proj.val (R.atlas.A q.proj.val q.proj.val).2 * b66m_sc_sliceD R t q.proj.val q.proj q.2

theorem b66m_rs_cform_apply (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (C : b66k_Index R → ℂ → ℂ)
    (hlaw : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      C a (R.atlas.A a (t, x)).2 = b66k_vertical R t a b x * C b (R.atlas.A b (t, x)).2)
    (p : rf8_fibre R.C t) (hp : p.val.2 ∉ S) (a : b66k_Index R)
    (ha : p.val ∈ (R.atlas.A a).source) (w : ℂ) :
    b66m_rs_cform R t C ⟨p, w⟩ = C a (R.atlas.A a p.val).2 * b66m_sc_sliceD R t a p w := by
  have hc : p.val ∈ (R.atlas.A p.val).source := (R.atlas.hA p.val).1
  have hl := hlaw a p.val p.val.2 hp ((b66m_rs_mem_source R t a p).mp ha)
    ((b66m_rs_mem_source R t p.val p).mp hc)
  rw [← b66m_sc_fibre_val R t p] at hl
  change C p.val (R.atlas.A p.val p.val).2 * b66m_sc_sliceD R t p.val p w = _
  rw [b66m_rs_slice_change R t a p.val p ha hc w, hl]
  ring

theorem b66m_rs_cform_lin (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (C : b66k_Index R → ℂ → ℂ) (x : rf8_fibre R.C t) (c u w : ℂ) :
    b66m_rs_cform R t C ⟨x, c * u + w⟩ =
      c * b66m_rs_cform R t C ⟨x, u⟩ + b66m_rs_cform R t C ⟨x, w⟩ := by
  unfold b66m_rs_cform
  simp only
  rw [b66m_rs_clm_apply (b66m_sc_sliceD R t x.val x) (c * u + w),
    b66m_rs_clm_apply (b66m_sc_sliceD R t x.val x) u, b66m_rs_clm_apply (b66m_sc_sliceD R t x.val x) w]
  ring

theorem b66m_rs_cform_loc (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (C : b66k_Index R → ℂ → ℂ)
    (hlaw : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      C a (R.atlas.A a (t, x)).2 = b66k_vertical R t a b x * C b (R.atlas.A b (t, x)).2)
    (x₀ : rf8_fibre R.C t) :
    HurwitzPrymRR_loc (Module.finrank_self ℂ) (b66m_rs_cform R t C) x₀ =ᶠ[𝓝[≠] 0]
      fun τ => C x₀.val
        ((b66m_sc_slice R t x₀.val ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
          (extChartAt 𝓘(ℂ, ℂ) x₀ x₀ + τ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)) *
        deriv (fun σ => (b66m_sc_slice R t x₀.val ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
          (extChartAt 𝓘(ℂ, ℂ) x₀ x₀ + σ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)) τ := by
  set e := extChartAt 𝓘(ℂ, ℂ) x₀
  set a₀ := x₀.val
  set c₀ := b4cov_lineEquiv (Module.finrank_self ℂ) 1
  set hh := b66m_sc_slice R t a₀ ∘ e.symm
  have hc₀ : c₀ ≠ 0 := by
    intro h0
    have := (b4cov_lineEquiv (Module.finrank_self ℂ)).injective (h0.trans (map_zero _).symm)
    exact one_ne_zero this
  have hx₀e : x₀ ∈ e.source := mem_extChartAt_source x₀
  have hex : e x₀ ∈ e.target := e.map_source hx₀e
  have ha₀ : x₀.val ∈ (R.atlas.A a₀).source := (R.atlas.hA a₀).1
  have hopen := b66m_sc_open_source R t a₀
  set B : Set (rf8_fibre R.C t) :=
    (fun x : R.C => (⟨(t, x), rfl⟩ : rf8_fibre R.C t)) '' (↑S : Set R.C) \ {x₀}
  have hBf : B.Finite := (S.finite_toSet.image _).sdiff
  have hBc : Bᶜ ∈ 𝓝 x₀ := by
    refine (hBf.isClosed.isOpen_compl).mem_nhds ?_
    intro hx
    exact hx.2 rfl
  have hsc : Tendsto (fun τ : ℂ => e x₀ + τ * c₀) (𝓝 0) (𝓝 (e x₀)) := by
    have : Continuous (fun τ : ℂ => e x₀ + τ * c₀) := by fun_prop
    simpa using this.tendsto 0
  have hsymc : Tendsto (fun τ : ℂ => e.symm (e x₀ + τ * c₀)) (𝓝 0) (𝓝 x₀) := by
    have := (continuousAt_extChartAt_symm'' hex).tendsto.comp hsc
    rwa [e.left_inv hx₀e] at this
  have hev1 : ∀ᶠ τ in 𝓝 (0 : ℂ), e x₀ + τ * c₀ ∈ e.target :=
    hsc.eventually (extChartAt_target_mem_nhds' hex)
  have hev2 : ∀ᶠ τ in 𝓝 (0 : ℂ), e.symm (e x₀ + τ * c₀) ∈
      {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A a₀).source} :=
    hsymc.eventually (hopen.mem_nhds ha₀)
  have hev3 : ∀ᶠ τ in 𝓝 (0 : ℂ), e.symm (e x₀ + τ * c₀) ∈ Bᶜ :=
    hsymc.eventually hBc
  filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, nhdsWithin_le_nhds hev3,
    self_mem_nhdsWithin] with τ h1 h2 h3 h4
  set y := e.symm (e x₀ + τ * c₀)
  have hy : y ∈ e.source := e.map_target h1
  have hyx : y ≠ x₀ := by
    intro hyx
    have := e.right_inv h1
    rw [show e.symm (e x₀ + τ * c₀) = y from rfl, hyx] at this
    have h5 : τ * c₀ = 0 := by linear_combination -this
    exact h4 (mul_eq_zero.mp h5 |>.resolve_right hc₀)
  have hyS : y.val.2 ∉ S := fun hS => h3 ⟨⟨y.val.2, hS, b66m_sc_fibre_mk R t y⟩, hyx⟩
  obtain ⟨hyan, _, hD⟩ := b66m_sc_slice_chart R t a₀ x₀ y hy h2
  have hey : e y = e x₀ + τ * c₀ := e.right_inv h1
  have hdΦ : deriv (fun σ => hh (e x₀ + σ * c₀)) τ = deriv hh (e x₀ + τ * c₀) * c₀ := by
    rw [hey] at hyan
    have hs : HasDerivAt (fun σ : ℂ => e x₀ + σ * c₀) c₀ τ := by
      simpa using ((hasDerivAt_id τ).mul_const c₀).const_add (e x₀)
    exact (hyan.differentiableAt.hasDerivAt.comp τ hs).deriv
  change b4cov_coef (b66m_rs_cform R t C) x₀ c₀
    (e x₀ + b4cov_lineEquiv (Module.finrank_self ℂ) τ) = _
  rw [b66m_rs_lineEquiv_apply τ]
  unfold b4cov_coef
  change b66m_rs_cform R t C ⟨y, b4cov_vec x₀ y c₀⟩ = _
  refine (b66m_rs_cform_apply R t S C hlaw y hyS a₀ h2 (b4cov_vec x₀ y c₀)).trans ?_
  have hk : b66m_sc_sliceD R t a₀ y (b4cov_vec x₀ y c₀) = deriv hh (e x₀ + τ * c₀) * c₀ := by
    refine (hD _).trans ?_
    rw [b66m_rs_chartD_vec R t x₀ y hy, hey]
  rw [hk, hdΦ]
  rfl

theorem b66m_rs_cform_res (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (C : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (C a) z)
    (hlaw : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      C a (R.atlas.A a (t, x)).2 = b66k_vertical R t a b x * C b (R.atlas.A b (t, x)).2)
    (x₀ : rf8_fibre R.C t) :
    MeromorphicAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) (b66m_rs_cform R t C) x₀) 0 ∧
    TauCeti.Contour.residue
      (HurwitzPrymRR_loc (Module.finrank_self ℂ) (b66m_rs_cform R t C) x₀) 0 =
      TauCeti.Contour.residue (C x₀.val) (R.atlas.A x₀.val x₀.val).2 := by
  have hloc := b66m_rs_cform_loc R t S C hlaw x₀
  set e := extChartAt 𝓘(ℂ, ℂ) x₀
  set c₀ := b4cov_lineEquiv (Module.finrank_self ℂ) 1
  set hh := b66m_sc_slice R t x₀.val ∘ e.symm
  set Φ : ℂ → ℂ := fun σ => hh (e x₀ + σ * c₀)
  have hc₀ : c₀ ≠ 0 := by
    intro h0
    have := (b4cov_lineEquiv (Module.finrank_self ℂ)).injective (h0.trans (map_zero _).symm)
    exact one_ne_zero this
  have ha₀ : x₀.val ∈ (R.atlas.A x₀.val).source := (R.atlas.hA x₀.val).1
  obtain ⟨hhan, hhd, _⟩ := b66m_sc_slice_chart R t x₀.val x₀ x₀ (mem_extChartAt_source x₀) ha₀
  have hs : HasDerivAt (fun σ : ℂ => e x₀ + σ * c₀) c₀ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const c₀).const_add (e x₀)
  have hsa : AnalyticAt ℂ (fun σ : ℂ => e x₀ + σ * c₀) 0 := by fun_prop
  have hh0 : (fun σ : ℂ => e x₀ + σ * c₀) 0 = e x₀ := by simp
  have hhan' : AnalyticAt ℂ hh ((fun σ : ℂ => e x₀ + σ * c₀) 0) := by
    rw [hh0]
    exact hhan
  have hΦ : AnalyticAt ℂ Φ 0 := AnalyticAt.comp (f := fun σ : ℂ => e x₀ + σ * c₀) hhan' hsa
  have hΦd : deriv Φ 0 ≠ 0 := by
    change deriv (hh ∘ fun σ : ℂ => e x₀ + σ * c₀) 0 ≠ 0
    rw [(hhan'.differentiableAt.hasDerivAt.comp 0 hs).deriv]
    simp only [zero_mul, add_zero]
    exact mul_ne_zero hhd hc₀
  have hΦ0 : Φ 0 = (R.atlas.A x₀.val x₀.val).2 := by
    simp only [Φ, hh, zero_mul, add_zero, Function.comp_apply,
      e.left_inv (mem_extChartAt_source x₀)]
    rfl
  have hm := hmero x₀.val _ (b66m_sc_slice_domain R t x₀.val x₀ ha₀)
  change MeromorphicAt (C x₀.val) (R.atlas.A x₀.val x₀.val).2 at hm
  rw [← hΦ0] at hm
  have hcm : MeromorphicAt (fun τ => C x₀.val (Φ τ) * deriv Φ τ) 0 :=
    (hm.comp_analyticAt hΦ).mul hΦ.deriv.meromorphicAt
  refine ⟨hcm.congr hloc.symm, ?_⟩
  rw [TauCeti.Contour.residue_congr_nhdsNE hloc, ← hΦ0]
  exact b66m_rs_residue_comp hΦ hΦd hm

theorem b66m_rs_cform_residue_sum (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (C : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (C a) z)
    (hreg : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (C a) z)
    (hlaw : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      C a (R.atlas.A a (t, x)).2 = b66k_vertical R t a b x * C b (R.atlas.A b (t, x)).2) :
    ∑ x ∈ S, TauCeti.Contour.residue (C (t, x)) (R.atlas.A (t, x) (t, x)).2 = 0 := by
  set θ := b66m_rs_cform R t C
  have hres := b66m_rs_cform_res R t S C hmero hlaw
  have hlin : HurwitzPrymRR_IsLinear θ := fun x c u w => b66m_rs_cform_lin R t C x c u w
  let w : b4c_MeroForm ℂ (rf8_fibre R.C t) (Module.finrank_self ℂ) :=
    ⟨θ, hlin, fun x => (hres x).1⟩
  have hsum := b4c_residue_sum (Module.finrank_self ℂ) w
  have hsupp : Function.support (fun x => b4c_res (hE := Module.finrank_self ℂ)
      (w : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ) x) ⊆ ↑(S.map (b66m_sc_pt R t)) := by
    intro p hp
    by_contra hnot
    apply hp
    have hpS : p.val.2 ∉ S := by
      intro hm
      apply hnot
      refine Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨p.val.2, hm, ?_⟩)
      exact b66m_sc_fibre_mk R t p
    change TauCeti.Contour.residue (HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p) 0 = 0
    rw [(hres p).2]
    apply TauCeti.Contour.residue_eq_zero_of_analyticAt
    have ha : p.val ∈ (R.atlas.A p.val).source := (R.atlas.hA p.val).1
    apply hreg p.val _ (b66m_sc_slice_domain R t p.val p ha)
    rw [b66m_sc_inv_slice R t p.val p ha]
    exact hpS
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_map] at hsum
  refine Eq.trans ?_ hsum
  refine Finset.sum_congr rfl fun x _ => ?_
  exact ((hres (b66m_sc_pt R t x)).2).symm


theorem b66m_rs_overlap_eventually (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_refinementDomain R t 1 a b) :
    ∀ᶠ w in 𝓝 z,
      (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source ∧
      R.atlas.A a (t, ((R.atlas.A a).symm (t.val, w)).2) = (t.val, w) ∧
      (R.atlas.A b (t, ((R.atlas.A a).symm (t.val, w)).2)).2 =
        b66k_transition R a b (t.val, w) := by
  have hi := b66k_inverse_slice R t a z hz.1
  have hm : (t.val, z) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨hz.1, ?_⟩
    change (R.atlas.A a).symm (t.val, z) ∈ (R.atlas.A b).source
    simpa only [one_smul, hi] using hz.2
  have hopen := ((R.atlas.A a).symm.trans (R.atlas.A b)).open_source
  have hev := (continuous_const.prodMk continuous_id).continuousAt
    (hopen.mem_nhds hm)
  filter_upwards [hev] with w hw
  change (t.val, w) ∈ (R.atlas.A a).target ∧
    (R.atlas.A a).symm (t.val, w) ∈ (R.atlas.A b).source at hw
  have hiw := b66k_inverse_slice R t a w hw.1
  rw [hiw]
  exact ⟨⟨(R.atlas.A a).map_target hw.1, hw.2⟩, (R.atlas.A a).right_inv hw.1, rfl⟩


theorem b66m_rs_transition_mem (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_refinementDomain R t 1 a b) :
    (t.val, z) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source ∧
    b66k_transition R a b (t.val, z) ∈ b66k_domain R t b ∧
    AnalyticAt ℂ (fun w => b66k_transition R a b (t.val, w)) z ∧
    AnalyticAt ℂ (fun w => fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1)) z := by
  have hi := b66k_inverse_slice R t a z hz.1
  have hm : (t.val, z) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨hz.1, ?_⟩
    change (R.atlas.A a).symm (t.val, z) ∈ (R.atlas.A b).source
    simpa only [one_smul, hi] using hz.2
  have hd : ContDiffAt ℂ ω (b66k_transition R a b) (t.val, z) :=
    (b66k_transition_analytic R a b _ hm).contDiffAt
  have hd' : ContDiffAt ℂ ω
      (fun u => fderiv ℂ (b66k_transition R a b) u (0, 1)) (t.val, z) :=
    (hd.fderiv_right (by simp)).clm_apply contDiffAt_const
  refine ⟨hm, ?_, ?_, ?_⟩
  · have hy : (R.atlas.A a).symm (t.val, z) ∈ (R.atlas.A b).source := hm.2
    change (t.val, (R.atlas.A b ((R.atlas.A a).symm (t.val, z))).2) ∈ (R.atlas.A b).target
    have h1 : (R.atlas.A b ((R.atlas.A a).symm (t.val, z))).1 = t.val := by
      rw [R.atlas.hparam b _ hy, b66k_inverse_parameter R a _ hz.1]
    convert (R.atlas.A b).map_source hy using 1
    exact Prod.ext h1.symm rfl
  · exact (b66k_transition_analytic R a b _ hm).comp
      (analyticAt_const.prod analyticAt_id)
  · exact (hd'.comp z (contDiffAt_const.prodMk contDiffAt_id)).analyticAt


theorem b66m_rs_forms_spec (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (m : ℕ)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) :
    (∀ a, AnalyticOnNhd ℂ (fun z => q a ((R.atlas.A a).symm (t.val, z)).2)
      (b66k_domain R t a)) ∧
    (∀ a b x, (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      q a x = b66k_vertical R t a b x ^ m * q b x) ∧
    ∀ a x, (t, x) ∉ (R.atlas.A a).source → q a x = 0 := by
  induction hq using Submodule.span_induction with
  | mem q hq => exact hq
  | zero =>
    refine ⟨fun a z _ => analyticAt_const, fun _ _ _ _ _ => by simp, fun _ _ _ => rfl⟩
  | add q r _ _ hq hr =>
    refine ⟨fun a => (hq.1 a).add (hr.1 a), fun a b x ha hb => ?_, fun a x hx => ?_⟩
    · simp only [Pi.add_apply]
      rw [hq.2.1 a b x ha hb, hr.2.1 a b x ha hb]
      ring
    · simp only [Pi.add_apply]
      rw [hq.2.2 a x hx, hr.2.2 a x hx, add_zero]
  | smul k q _ hq =>
    refine ⟨fun a => ?_, fun a b x ha hb => ?_, fun a x hx => ?_⟩
    · exact (hq.1 a).const_smul (c := k)
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hq.2.1 a b x ha hb]
      ring
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hq.2.2 a x hx, mul_zero]


theorem b66m_rs_holomorphic_spec (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {u : b66k_Cochain R} (hu : u ∈ b66k_holomorphicCochains R t) :
    (∀ a b, AnalyticOnNhd ℂ
      (fun z => u a b ((R.atlas.A a).symm (t.val, z)).2)
      (b66k_refinementDomain R t 1 a b)) ∧
    ∀ a b x, (t, x) ∉ (R.atlas.A a).source ∩ (R.atlas.A b).source → u a b x = 0 := by
  induction hu using Submodule.span_induction with
  | mem u hu => exact hu
  | zero => exact ⟨fun a b z _ => analyticAt_const, fun _ _ _ _ => rfl⟩
  | add u w _ _ hu hw =>
    refine ⟨fun a b => (hu.1 a b).add (hw.1 a b), fun a b x hx => ?_⟩
    simp only [Pi.add_apply]
    rw [hu.2 a b x hx, hw.2 a b x hx, add_zero]
  | smul k u _ hu =>
    refine ⟨fun a b => ?_, fun a b x hx => ?_⟩
    · exact (hu.1 a b).const_smul (c := k)
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hu.2 a b x hx, mul_zero]


theorem b66m_rs_kernel_spec (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {u : b66k_Cochain R} (hu : u ∈ LinearMap.ker (b66k_differential R t))
    (a b c : b66k_Index R) (x : R.C) (ha : (t, x) ∈ (R.atlas.A a).source)
    (hb : (t, x) ∈ (R.atlas.A b).source) (hc : (t, x) ∈ (R.atlas.A c).source) :
    u a c x = u b c x + b66k_vertical R t b c x * u a b x := by
  have h := congrFun (congrFun (congrFun (congrFun (LinearMap.mem_ker.mp hu) a) b) c) x
  simp only [b66k_differential, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply,
    ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source ∩
      (R.atlas.A c).source from ⟨⟨ha, hb⟩, hc⟩)] at h
  linear_combination h


theorem b66m_rs_chart_slice (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (b : b66k_Index R) (x : R.C) (hb : (t, x) ∈ (R.atlas.A b).source) :
    R.atlas.A b (t, x) = (t.val, (R.atlas.A b (t, x)).2) ∧
    ((R.atlas.A b).symm (t.val, (R.atlas.A b (t, x)).2)).2 = x := by
  have h1 : R.atlas.A b (t, x) = (t.val, (R.atlas.A b (t, x)).2) :=
    Prod.ext (R.atlas.hparam b _ hb) rfl
  refine ⟨h1, ?_⟩
  rw [← h1, (R.atlas.A b).left_inv hb]


theorem b66m_rs_target_coefficient (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : b66g_Coeff R) (a b : b66k_Index R) (z : ℂ)
    (hz : z ∈ b66k_refinementDomain R t 1 a b)
    (hq : AnalyticOnNhd ℂ (fun z => q b ((R.atlas.A b).symm (t.val, z)).2)
      (b66k_domain R t b)) :
    AnalyticAt ℂ (fun w => q b ((R.atlas.A a).symm (t.val, w)).2) z := by
  obtain ⟨_, hdom, han, _⟩ := b66m_rs_transition_mem R t a b z hz
  have h1 : AnalyticAt ℂ (fun w =>
      q b ((R.atlas.A b).symm (t.val, b66k_transition R a b (t.val, w))).2) z :=
    AnalyticAt.comp (f := fun w => b66k_transition R a b (t.val, w)) (hq _ hdom) han
  apply h1.congr
  filter_upwards [b66m_rs_overlap_eventually R t a b z hz] with w ⟨hmem, _, hb⟩
  rw [← hb, (b66m_rs_chart_slice R t b _ hmem.2).2]


theorem b66m_rs_contract_mem (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) {u : b66k_Cochain R}
    (hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t)) :
    b66g_contract R q u ∈ b66g_scalarCycles R t := by
  obtain ⟨hqa, hql, _⟩ := b66m_rs_forms_spec R t 1 hq
  obtain ⟨hua, huz⟩ := b66m_rs_holomorphic_spec R t hu.1
  apply Submodule.subset_span
  refine ⟨fun a b z hz => ?_, fun a b x hx => ?_, fun a b c x ha hb hc => ?_⟩
  · exact (b66m_rs_target_coefficient R t q a b z hz (hqa b)).mul (hua a b z hz)
  · simp only [b66g_contract, huz a b x hx, mul_zero]
  · simp only [b66g_contract]
    rw [b66m_rs_kernel_spec R t hu.2 a b c x ha hb hc, hql b c x hb hc, pow_one]
    ring


theorem b66m_rs_slice_ne (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (p : rf8_fibre R.C t) (ha : p.val ∈ (R.atlas.A a).source) :
    b66m_sc_sliceD R t a p 1 ≠ 0 := by
  intro h0
  apply (b66g_slice_coordinate R t a).2 p ha
  apply ContinuousLinearMap.ext
  intro (v : ℂ)
  have hz : b66m_sc_sliceD R t a p = 0 :=
    ContinuousLinearMap.ext_ring (by rw [h0]; rfl)
  exact congrArg (fun L : ℂ →L[ℂ] ℂ => L v) hz


theorem b66m_rs_residueSum_extend (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S T : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hreg : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (hST : S ⊆ T) :
    b66g_residueSum R t T v q = b66g_residueSum R t S v q := by
  obtain ⟨hqa, _, _⟩ := b66m_rs_forms_spec R t m hq
  unfold b66g_residueSum
  symm
  refine Finset.sum_subset hST fun x _ hx => ?_
  have hxa : (t, x) ∈ (R.atlas.A (t, x)).source := (R.atlas.hA _).1
  have hdom : (R.atlas.A (t, x) (t, x)).2 ∈ b66k_domain R t (t, x) := by
    show (t.val, (R.atlas.A (t, x) (t, x)).2) ∈ (R.atlas.A (t, x)).target
    rw [← (b66m_rs_chart_slice R t (t, x) x hxa).1]
    exact (R.atlas.A (t, x)).map_source hxa
  apply TauCeti.Contour.residue_eq_zero_of_analyticAt
  refine (hreg (t, x) _ hdom ?_).mul (hqa (t, x) _ hdom)
  rw [(b66m_rs_chart_slice R t (t, x) x hxa).2]
  exact hx


theorem b66m_rs_residueSum_smul (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ) (c : ℂ) (q : b66g_Coeff R) :
    b66g_residueSum R t S v (c • q) = c * b66g_residueSum R t S v q := by
  unfold b66g_residueSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← TauCeti.Contour.residue_const_mul]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  ring


theorem b66m_rs_residueSum_sum (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    {ι : Type} (s : Finset ι) (q : ι → b66g_Coeff R) (hq : ∀ i, q i ∈ b66g_forms R t 1) :
    b66g_residueSum R t S v (∑ i ∈ s, q i) = ∑ i ∈ s, b66g_residueSum R t S v (q i) := by
  unfold b66g_residueSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hxa : (t, x) ∈ (R.atlas.A (t, x)).source := (R.atlas.hA _).1
  have hdom : (R.atlas.A (t, x) (t, x)).2 ∈ b66k_domain R t (t, x) := by
    show (t.val, (R.atlas.A (t, x) (t, x)).2) ∈ (R.atlas.A (t, x)).target
    rw [← (b66m_rs_chart_slice R t (t, x) x hxa).1]
    exact (R.atlas.A (t, x)).map_source hxa
  have hm : ∀ i ∈ s, MeromorphicAt (fun z => v (t, x) z *
      q i (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2) (R.atlas.A (t, x) (t, x)).2 :=
    fun i _ => (hmero (t, x) _ hdom).mul
      ((b66m_rs_forms_spec R t 1 (hq i)).1 (t, x) _ hdom).meromorphicAt
  rw [← TauCeti.Contour.residue_sum s hm]
  congr 1
  funext z
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum]


theorem b66m_rs_principalClass_top {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (x₀ : C) : ∃ m : ℕ, LinearMap.range (RiemannRochAna_principalClassLinear
      (Module.finrank_self ℂ) (Finsupp.single x₀ (m : ℤ)) : _ →ₗ[ℂ] b4c_Dolbeault01 ℂ C) = ⊤ := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  obtain ⟨m, hm⟩ := RiemannRochAna_exists_single_holResidueKernel_bot (C := C) hE x₀
  refine ⟨m, ?_⟩
  set D : C →₀ ℤ := Finsupp.single x₀ (m : ℤ)
  have hD : ∀ y, 0 ≤ D y := by
    intro y
    simp only [D, Finsupp.single_apply]
    split_ifs <;> positivity
  have : Module.Finite ℂ (b4c_Dolbeault01 ℂ C) := (b4c_dolbeault_finite_aux (E := ℂ) (C := C) hE).1
  have h1 := RiemannRochAna_principalResidue_rank_add_holKernel (C := C) hE D
  rw [hm, finrank_bot, add_zero] at h1
  have hk := RiemannRochAna_principalClass_kernel_eq_residueKernel_effective hE D hD x₀
  have hc := (RiemannRochAna_principalClassLinear hE D).finrank_range_add_finrank_ker
  have hr := (RiemannRochAna_principalResidueLinear hE D).finrank_range_add_finrank_ker
  rw [hk] at hc
  apply Submodule.eq_top_of_finrank_eq
  rw [(b4c_dolbeault_finite_aux (E := ℂ) (C := C) hE).2]
  omega


theorem b66m_rs_mittagLeffler {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (γ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) (hγ : γ ∈ b4c_Smooth01 ℂ C) (x₀ : C) :
    ∃ F P : C → ℂ, ∃ N : ℕ, ∃ c : Fin N → ℂ,
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F ∧
      (∀ y, y ≠ x₀ → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ P y) ∧
      (∀ y, y ≠ x₀ → ∀ v : ℂ, b4c_dbar ℂ C (F + P) ⟨y, v⟩ = γ ⟨y, v⟩) ∧
      (∀ᶠ y in 𝓝 x₀, ∀ v : ℂ, b4c_dbar ℂ C F ⟨y, v⟩ = γ ⟨y, v⟩) ∧
      P =ᶠ[𝓝 x₀] fun y => ∑ n, c n /
        RiemannRochAna_coordinate (Module.finrank_self ℂ) x₀ y ^ ((n : ℕ) + 1) := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  obtain ⟨m, hm⟩ := b66m_rs_principalClass_top (C := C) x₀
  set D : C →₀ ℤ := Finsupp.single x₀ (m : ℤ)
  let g : b4c_Smooth01 ℂ C := ⟨γ, hγ⟩
  have hg : (Submodule.mkQ _ g : b4c_Dolbeault01 ℂ C) ∈
      LinearMap.range (RiemannRochAna_principalClassLinear hE D) := by
    rw [hm]
    trivial
  obtain ⟨c', hc'⟩ := hg
  have hdiff : g - RiemannRochAna_principalObstructionLinear hE D c' ∈
      (Submodule.span ℂ (b4c_dbar ℂ C '' (b4c_SmoothFun ℂ C : Set (C → ℂ)))).comap
        (b4c_Smooth01 ℂ C).subtype := by
    rw [← Submodule.Quotient.eq]
    exact hc'.symm
  have hmem : γ - (RiemannRochAna_principalObstructionLinear hE D c').1 ∈
      b4c_dbar ℂ C '' (b4c_SmoothFun ℂ C : Set (C → ℂ)) := by
    rw [← b4c_dbar_image_eq hE]
    exact hdiff
  obtain ⟨F, hF, hFd⟩ := hmem
  have hsupp : ∀ i : D.support, i.1 = x₀ := by
    intro i
    have := Finsupp.support_single_subset i.2
    simpa using this
  refine ⟨F, RiemannRochAna_principalScalar hE D c', ?_⟩
  have hoff : ∀ y, y ≠ x₀ → y ∉ D.support := fun y hy hyD => hy (hsupp ⟨y, hyD⟩)
  have hP : ∀ y, y ≠ x₀ → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (RiemannRochAna_principalScalar hE D c') y := fun y hy =>
    RiemannRochAna_principalScalar_smooth_off_support hE D c' y (hoff y hy)
  have hdF : ∀ q, b4c_dbar ℂ C F q = γ q - (RiemannRochAna_principalObstructionLinear hE D c').1 q :=
    fun q => congrFun hFd q
  have hnear : ∀ᶠ y in 𝓝 x₀, ∀ v : ℂ,
      (RiemannRochAna_principalObstructionLinear hE D c').1 ⟨y, v⟩ = 0 := by
    have hall : ∀ᶠ y in 𝓝 x₀, ∀ (i : D.support) (n : Fin (Int.toNat (D i.1))) (v : ℂ),
        RiemannRochAna_principalObstructionPow hE i.1
          (RiemannRochAna_divisorCutoff hE D i) n ⟨y, v⟩ = 0 := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro n
      have h := RiemannRochAna_principalObstructionPow_zero_germ hE i.1
        (RiemannRochAna_divisorCutoff hE D i) n (RiemannRochAna_divisorCutoff_spec hE D i).2.1
      have hx : (i : C) = x₀ := hsupp i
      exact hx ▸ h
    filter_upwards [hall] with y hy v
    rw [RiemannRochAna_principalObstructionLinear_apply]
    simp only [hy, mul_zero, Finset.sum_const_zero]
  by_cases hx : x₀ ∈ D.support
  · let i : D.support := ⟨x₀, hx⟩
    refine ⟨Int.toNat (D x₀), c' i, hF, hP, fun y hy v => ?_, ?_, ?_⟩
    · have hFm : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F y := (hF y).mdifferentiableAt (by simp)
      have hPm := (hP y hy).mdifferentiableAt (by simp)
      rw [RiemannRochAna_dbar_add_at _ _ y hFm hPm v, hdF,
        RiemannRochAna_principalScalar_dbar hE D c' y (hoff y hy) v]
      ring
    · filter_upwards [hnear] with y hy v
      rw [hdF, hy v, sub_zero]
    · exact RiemannRochAna_principalScalar_germ hE D c' i
  · have hzero : RiemannRochAna_principalScalar hE D c' = 0 := by
      funext y
      apply Finset.sum_eq_zero
      intro i _
      exact absurd (hsupp i ▸ i.2) hx
    refine ⟨0, Fin.elim0, hF, hP, fun y hy v => ?_, ?_, ?_⟩
    · rw [hzero, add_zero, hdF]
      have := RiemannRochAna_principalScalar_dbar hE D c' y (hoff y hy) v
      rw [hzero] at this
      rw [← this]
      have h0 := RiemannRochAna_dbar_const_germ (E := ℂ) (C := C) (u := (0 : C → ℂ)) (x := y)
        (a := 0) (Filter.EventuallyEq.refl _ _) v
      rw [h0, sub_zero]
    · filter_upwards [hnear] with y hy v
      rw [hdF, hy v, sub_zero]
    · rw [hzero]
      exact Filter.Eventually.of_forall fun y => by simp


theorem b66m_rs_pt_continuous (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_domain R t a) :
    ContinuousAt (fun w => b66m_sc_pt R t ((R.atlas.A a).symm (t.val, w)).2) z := by
  have hc : ContinuousAt (fun w : ℂ => (R.atlas.A a).symm (t.val, w)) z :=
    ((R.atlas.A a).continuousAt_symm hz).comp (continuous_const.prodMk continuous_id).continuousAt
  exact (b6m_coordinate mr_base R.C t).symm.continuous.continuousAt.comp
    (continuous_snd.continuousAt.comp hc)


theorem b66m_rs_scalar_split (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {s : b66k_Cochain R} (hs : s ∈ b66g_scalarCycles R t) :
    ∃ (x₀ : R.C) (h : b66k_Index R → ℂ → ℂ),
      (∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (h a) z) ∧
      (∀ a z, z ∈ b66k_domain R t a → ((R.atlas.A a).symm (t.val, z)).2 ≠ x₀ →
        AnalyticAt ℂ (h a) z) ∧
      ∀ a b x, (t, x) ∈ (R.atlas.A a).source → (t, x) ∈ (R.atlas.A b).source →
        s a b x = h a (R.atlas.A a (t, x)).2 - h b (R.atlas.A b (t, x)).2 := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℂ))
    (M := rf8_fibre R.C t) isClosed_univ
    (fun c => {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A c).source})
    (fun c => b66m_sc_open_source R t c)
    (fun y _ => mem_iUnion.mpr ⟨y.val, (R.atlas.hA y.val).1⟩)
  obtain ⟨y₀⟩ : Nonempty (rf8_fibre R.C t) := inferInstance
  obtain ⟨F, P, N, c, hF, hP, hFP, hFnear, hPg⟩ :=
    b66m_rs_mittagLeffler (b66m_sc_gamma R t ρ s) (b66m_sc_gamma_mem R t ρ hρ hs) y₀
  let H : b66k_Index R → rf8_fibre R.C t → ℂ := fun a => b66m_sc_tau R t ρ s a - (F + P)
  have hpt : ∀ a z, z ∈ b66k_domain R t a →
      (b66m_sc_pt R t ((R.atlas.A a).symm (t.val, z)).2).val ∈ (R.atlas.A a).source := by
    intro a z hz
    change (t, ((R.atlas.A a).symm (t.val, z)).2) ∈ (R.atlas.A a).source
    rw [b66k_inverse_slice R t a z hz]
    exact (R.atlas.A a).map_target hz
  have hAn : ∀ a z, z ∈ b66k_domain R t a → ((R.atlas.A a).symm (t.val, z)).2 ≠ y₀.val.2 →
      AnalyticAt ℂ (fun w => H a (b66m_sc_pt R t ((R.atlas.A a).symm (t.val, w)).2)) z := by
    intro a z hz hne
    apply b66m_sc_coord_analytic R t (H a) a z hz
    set y := b66m_sc_pt R t ((R.atlas.A a).symm (t.val, z)).2
    have hya := hpt a z hz
    have hyne : y ≠ y₀ := fun h => hne (by rw [← h]; rfl)
    apply RiemannRochAna_analyticAt_of_dbar_germ hE (H a) y
    have hopen : IsOpen ({y' : rf8_fibre R.C t | y'.val ∈ (R.atlas.A a).source} ∩ {y₀}ᶜ) :=
      (b66m_sc_open_source R t a).inter isOpen_compl_singleton
    filter_upwards [hopen.mem_nhds ⟨hya, hyne⟩] with y' hy'
    have hτ := b66m_sc_tau_smooth R t ρ hρ hs a y' hy'.1
    have hFP' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (F + P) y' := (hF y').add (hP y' hy'.2)
    refine ⟨hτ.sub hFP', fun v => ?_⟩
    rw [RiemannRochAna_dbar_sub_at _ _ y' (hτ.mdifferentiableAt (by simp))
      (hFP'.mdifferentiableAt (by simp)) v, hFP y' hy'.2 v,
      ← (b66m_sc_gamma_local R t ρ hρ hs a y' hy'.1).self_of_nhds v, sub_self]
  refine ⟨y₀.val.2, fun a w => H a (b66m_sc_pt R t ((R.atlas.A a).symm (t.val, w)).2),
    fun a z hz => ?_, hAn, fun a b x ha hb => ?_⟩
  · by_cases hne : ((R.atlas.A a).symm (t.val, z)).2 ≠ y₀.val.2
    · exact (hAn a z hz hne).meromorphicAt
    push Not at hne
    have hy : b66m_sc_pt R t ((R.atlas.A a).symm (t.val, z)).2 = y₀ := by
      rw [hne]
      exact b66m_sc_fibre_mk R t y₀
    have hya : y₀.val ∈ (R.atlas.A a).source := hy ▸ hpt a z hz
    have hG1 : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b66m_sc_tau R t ρ s a - F) y₀ := by
      apply RiemannRochAna_analyticAt_of_dbar_germ hE _ y₀
      filter_upwards [(b66m_sc_open_source R t a).mem_nhds hya, hFnear,
        b66m_sc_gamma_local R t ρ hρ hs a y₀ hya] with y' h1 h2 h3
      have hτ := b66m_sc_tau_smooth R t ρ hρ hs a y' h1
      refine ⟨hτ.sub (hF y'), fun v => ?_⟩
      rw [RiemannRochAna_dbar_sub_at _ _ y' (hτ.mdifferentiableAt (by simp))
        ((hF y').mdifferentiableAt (by simp)) v, h2 v, h3 v, sub_self]
    have hk := RiemannRochAna_coordinate_analytic hE y₀ y₀ (mem_extChartAt_source y₀)
    have hA1 : AnalyticAt ℂ (fun w => b66m_sc_tau R t ρ s a
        (b66m_sc_pt R t ((R.atlas.A a).symm (t.val, w)).2) -
        F (b66m_sc_pt R t ((R.atlas.A a).symm (t.val, w)).2)) z :=
      b66m_sc_coord_analytic R t (b66m_sc_tau R t ρ s a - F) a z hz (by rw [hy]; exact hG1)
    have hA2 : AnalyticAt ℂ (fun w => RiemannRochAna_coordinate hE y₀
        (b66m_sc_pt R t ((R.atlas.A a).symm (t.val, w)).2)) z :=
      b66m_sc_coord_analytic R t _ a z hz (by rw [hy]; exact hk)
    have hM : MeromorphicAt (fun w => (b66m_sc_tau R t ρ s a
        (b66m_sc_pt R t ((R.atlas.A a).symm (t.val, w)).2) -
        F (b66m_sc_pt R t ((R.atlas.A a).symm (t.val, w)).2)) -
        ∑ n, c n / RiemannRochAna_coordinate hE y₀
          (b66m_sc_pt R t ((R.atlas.A a).symm (t.val, w)).2) ^ ((n : ℕ) + 1)) z :=
      hA1.meromorphicAt.sub (MeromorphicAt.fun_sum (s := Finset.univ)
        fun n _ => (MeromorphicAt.const (c n) z).div (hA2.meromorphicAt.pow ((n : ℕ) + 1)))
    apply hM.congr
    have htend := (b66m_rs_pt_continuous R t a z hz).tendsto
    rw [hy] at htend
    filter_upwards [nhdsWithin_le_nhds (htend.eventually hPg)] with w hw
    simp only [H, Pi.sub_apply, Pi.add_apply, hw]
    ring
  · change s a b x = H a (b66m_sc_pt R t ((R.atlas.A a).symm (t.val, (R.atlas.A a (t, x)).2)).2) -
      H b (b66m_sc_pt R t ((R.atlas.A b).symm (t.val, (R.atlas.A b (t, x)).2)).2)
    rw [(b66m_rs_chart_slice R t a x ha).2, (b66m_rs_chart_slice R t b x hb).2]
    have := b66m_sc_tau_sub R t ρ hρ hs a b (b66m_sc_pt R t x) ha hb
    simp only [H, Pi.sub_apply, Pi.add_apply]
    change _ = s a b x at this
    linear_combination -this


theorem b66m_rs_form_exists (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ∃ q : b66g_Coeff R, q ∈ b66g_forms R t 1 ∧ q ≠ 0 := by
  have h6 := (b66g_primitive_comparison R t).2
  have hne : b66g_primitiveForms R t ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h6
    norm_num at h6
  obtain ⟨q, hq, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨q, (inf_le_left : b66g_primitiveForms R t ≤ b66g_forms R t 1) hq, hq0⟩


theorem b66m_rs_vertical_ne (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (x : R.C) (ha : (t, x) ∈ (R.atlas.A a).source)
    (hb : (t, x) ∈ (R.atlas.A b).source) : b66k_vertical R t a b x ≠ 0 := by
  have hch := b66m_rs_slice_change R t a b ⟨(t, x), rfl⟩ ha hb 1
  have hnb := b66m_rs_slice_ne R t b ⟨(t, x), rfl⟩ hb
  rw [hch] at hnb
  exact left_ne_zero_of_mul hnb


theorem b66m_rs_form_zero_iff (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (a : b66k_Index R)
    (y : rf8_fibre R.C t) (ha : y.val ∈ (R.atlas.A a).source) :
    q a y.val.2 = 0 ↔ q y.val y.val.2 = 0 := by
  have hb : y.val ∈ (R.atlas.A y.val).source := (R.atlas.hA y.val).1
  have ha' := (b66m_rs_mem_source R t a y).mp ha
  have hb' := (b66m_rs_mem_source R t y.val y).mp hb
  have hlaw := (b66m_rs_forms_spec R t m hq).2.1 a y.val y.val.2 ha' hb'
  have hV := pow_ne_zero m (b66m_rs_vertical_ne R t a y.val y.val.2 ha' hb')
  rw [hlaw]
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hV, fun h => by rw [h, mul_zero]⟩


theorem b66m_rs_form_dichotomy (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (y : rf8_fibre R.C t) :
    (∀ᶠ y' in 𝓝 y, q y'.val y'.val.2 = 0) ∨
      ∃ W ∈ 𝓝 y, ∀ y' ∈ W, y' ≠ y → q y'.val y'.val.2 ≠ 0 := by
  set a := y.val
  have ha : y.val ∈ (R.atlas.A a).source := (R.atlas.hA a).1
  have hf : AnalyticAt ℂ (fun z => q a ((R.atlas.A a).symm (t.val, z)).2)
      (b66m_sc_slice R t a y) :=
    (b66m_rs_forms_spec R t m hq).1 a _ (b66m_sc_slice_domain R t a y ha)
  have hs := (b66m_sc_slice_contMDiffAt R t a y ha).continuousAt.tendsto
  rcases hf.eventually_eq_zero_or_eventually_ne_zero with h0 | h1
  · left
    filter_upwards [hs.eventually h0, (b66m_sc_open_source R t a).mem_nhds ha] with y' h1 h2
    rw [← b66m_rs_form_zero_iff R t hq a y' h2]
    simpa only [b66m_sc_inv_slice R t a y' h2] using h1
  · right
    refine ⟨b66m_sc_slice R t a ⁻¹' {z | z ≠ b66m_sc_slice R t a y →
        q a ((R.atlas.A a).symm (t.val, z)).2 ≠ 0} ∩
        {y' | y'.val ∈ (R.atlas.A a).source}, inter_mem
        (hs.eventually (eventually_nhdsWithin_iff.mp h1))
        ((b66m_sc_open_source R t a).mem_nhds ha), fun y' hy' hne => ?_⟩
    have hsl : b66m_sc_slice R t a y' ≠ b66m_sc_slice R t a y := by
      intro heq
      apply hne
      apply Subtype.ext
      apply (R.atlas.A a).injOn hy'.2 ha
      rw [b66m_sc_slice_value R t a y' hy'.2, b66m_sc_slice_value R t a y ha]
      exact congrArg (fun z => (t.val, z)) heq
    have h := hy'.1 hsl
    rw [b66m_sc_inv_slice R t a y' hy'.2] at h
    exact fun hz => h ((b66m_rs_form_zero_iff R t hq a y' hy'.2).mpr hz)


theorem b66m_rs_form_isolated (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (hq0 : q ≠ 0) (y : rf8_fibre R.C t) :
    ∃ W ∈ 𝓝 y, ∀ y' ∈ W, y' ≠ y → q y'.val y'.val.2 ≠ 0 := by
  let A : Set (rf8_fibre R.C t) := {y | ∀ᶠ y' in 𝓝 y, q y'.val y'.val.2 = 0}
  have hopen : IsOpen A := isOpen_iff_mem_nhds.mpr fun y hy => hy.eventually_nhds
  have hclosed : IsClosed A := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    rcases b66m_rs_form_dichotomy R t hq y with h | ⟨W, hW, hiso⟩
    · exact absurd h hy
    filter_upwards [hW] with y' hy' hA'
    by_cases he : y' = y
    · exact hy (he ▸ hA')
    · exact hiso y' hy' he hA'.self_of_nhds
  rcases isClopen_iff.mp ⟨hclosed, hopen⟩ with hA | hA
  · rcases b66m_rs_form_dichotomy R t hq y with h | h
    · have : y ∈ A := h
      rw [hA] at this
      exact absurd this (notMem_empty y)
    · exact h
  · exfalso
    apply hq0
    funext a x
    by_cases hax : (t, x) ∈ (R.atlas.A a).source
    · have hy : b66m_sc_pt R t x ∈ A := hA ▸ mem_univ _
      exact (b66m_rs_form_zero_iff R t hq a (b66m_sc_pt R t x) hax).mpr hy.self_of_nhds
    · exact (b66m_rs_forms_spec R t m hq).2.2 a x hax


theorem b66m_rs_form_zeros_finite (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (hq0 : q ≠ 0) :
    ∃ T : Finset R.C, ∀ x, q (t, x) x = 0 → x ∈ T := by
  choose W hW hiso using b66m_rs_form_isolated R t hq hq0
  obtain ⟨T, hT⟩ := isCompact_univ.elim_nhds_subcover W (fun y _ => hW y)
  refine ⟨T.image fun y => y.val.2, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hT.2 (mem_univ (b66m_sc_pt R t x)))
  by_cases he : b66m_sc_pt R t x = y
  · exact Finset.mem_image.mpr ⟨y, hy, by rw [← he]; rfl⟩
  · exact absurd hx (hiso y _ hxy he)


theorem b66m_rs_own_domain (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (x : R.C) :
    (R.atlas.A (t, x) (t, x)).2 ∈ b66k_domain R t (t, x) := by
  have hxa : (t, x) ∈ (R.atlas.A (t, x)).source := (R.atlas.hA _).1
  show (t.val, (R.atlas.A (t, x) (t, x)).2) ∈ (R.atlas.A (t, x)).target
  rw [← (b66m_rs_chart_slice R t (t, x) x hxa).1]
  exact (R.atlas.A (t, x)).map_source hxa


theorem b66m_rs_residueSum_sub (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (v v' : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hmero' : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v' a) z)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) :
    b66g_residueSum R t S v q - b66g_residueSum R t S v' q =
      ∑ x ∈ S, TauCeti.Contour.residue
        (fun z => (v (t, x) z - v' (t, x) z) * q (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2)
        (R.atlas.A (t, x) (t, x)).2 := by
  obtain ⟨hqa, _, _⟩ := b66m_rs_forms_spec R t m hq
  unfold b66g_residueSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hdom := b66m_rs_own_domain R t x
  have hq' := (hqa (t, x) _ hdom).meromorphicAt
  have h1 : MeromorphicAt (fun z => v (t, x) z * q (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2)
      (R.atlas.A (t, x) (t, x)).2 := (hmero _ _ hdom).mul hq'
  have h2 : MeromorphicAt (fun z => v' (t, x) z * q (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2)
      (R.atlas.A (t, x) (t, x)).2 := (hmero' _ _ hdom).mul hq'
  rw [← TauCeti.Contour.residue_sub h1 h2]
  congr 1
  funext z
  simp only [Pi.sub_apply]
  ring


theorem b66m_rs_residueSum_add (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (v v' : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hmero' : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v' a) z)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) :
    b66g_residueSum R t S (v + v') q =
      b66g_residueSum R t S v q + b66g_residueSum R t S v' q := by
  obtain ⟨hqa, _, _⟩ := b66m_rs_forms_spec R t m hq
  unfold b66g_residueSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hdom := b66m_rs_own_domain R t x
  have hq' := (hqa (t, x) _ hdom).meromorphicAt
  have h1 : MeromorphicAt (fun z => v (t, x) z * q (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2)
      (R.atlas.A (t, x) (t, x)).2 := (hmero _ _ hdom).mul hq'
  have h2 : MeromorphicAt (fun z => v' (t, x) z * q (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2)
      (R.atlas.A (t, x) (t, x)).2 := (hmero' _ _ hdom).mul hq'
  rw [← TauCeti.Contour.residue_add h1 h2]
  congr 1
  funext z
  simp only [Pi.add_apply]
  ring


theorem b66m_rs_residueSum_vsmul (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ) (c : ℂ) (q : b66g_Coeff R) :
    b66g_residueSum R t S (c • v) q = c * b66g_residueSum R t S v q := by
  unfold b66g_residueSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← TauCeti.Contour.residue_const_mul]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  ring


theorem b66m_rs_residueSum_qadd (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    {q r : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) (hr : r ∈ b66g_forms R t 1) :
    b66g_residueSum R t S v (q + r) =
      b66g_residueSum R t S v q + b66g_residueSum R t S v r := by
  have h := b66m_rs_residueSum_sum R t S v hmero (Finset.univ : Finset (Fin 2)) ![q, r]
    (fun i => by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h


theorem b66m_rs_scalar_split_unique (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : b66k_Cochain R) (S S' : Finset R.C) (v v' : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hreg : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66g_scalarBoundary R t v a b x)
    (hmero' : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v' a) z)
    (hreg' : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S' → AnalyticAt ℂ (v' a) z)
    (hv' : ∀ a b x, x ∉ S' → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66g_scalarBoundary R t v' a b x)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) :
    b66g_residueSum R t S v q = b66g_residueSum R t S' v' q := by
  obtain ⟨hqa, hql, _⟩ := b66m_rs_forms_spec R t 1 hq
  set T := S ∪ S'
  rw [← b66m_rs_residueSum_extend R t S T v hreg hq Finset.subset_union_left,
    ← b66m_rs_residueSum_extend R t S' T v' hreg' hq Finset.subset_union_right,
    ← sub_eq_zero, b66m_rs_residueSum_sub R t T v v' hmero hmero' hq]
  apply b66m_rs_cform_residue_sum R t T
    (fun a z => (v a z - v' a z) * q a ((R.atlas.A a).symm (t.val, z)).2)
  · intro a z hz
    exact ((hmero a z hz).sub (hmero' a z hz)).mul (hqa a z hz).meromorphicAt
  · intro a z hz hT
    have h1 : ((R.atlas.A a).symm (t.val, z)).2 ∉ S := fun h => hT (Finset.mem_union_left _ h)
    have h2 : ((R.atlas.A a).symm (t.val, z)).2 ∉ S' := fun h => hT (Finset.mem_union_right _ h)
    exact ((hreg a z hz h1).sub (hreg' a z hz h2)).mul (hqa a z hz)
  · intro a b x hx ha hb
    have hxS : x ∉ S := fun h => hx (Finset.mem_union_left _ h)
    have hxS' : x ∉ S' := fun h => hx (Finset.mem_union_right _ h)
    have e1 := hv a b x hxS ha hb
    have e2 := hv' a b x hxS' ha hb
    simp only [b66g_scalarBoundary, ite_eq_left (show (t, x) ∈
      (R.atlas.A a).source ∩ (R.atlas.A b).source from ⟨ha, hb⟩)] at e1 e2
    rw [(b66m_rs_chart_slice R t a x ha).2, (b66m_rs_chart_slice R t b x hb).2,
      hql a b x ha hb, pow_one]
    linear_combination (b66k_vertical R t a b x * q b x) * (e2 - e1)

theorem b66m_rs_scalar_splitting (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : b66k_Cochain R) (hu : u ∈ b66g_scalarCycles R t) :
    ∃ (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ),
      (∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z) ∧
      (∀ a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z) ∧
      ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source → u a b x = b66g_scalarBoundary R t v a b x := by
  obtain ⟨p, v, hm, hr, hs⟩ := b66m_rs_scalar_split R t hu
  refine ⟨{p}, v, hm, ?_, ?_⟩
  · intro a z hz hx
    exact hr a z hz (by simpa only [Finset.mem_singleton] using hx)
  · intro a b x hx ha hb
    rw [b66g_scalarBoundary, ite_eq_left (show (t, x) ∈
      (R.atlas.A a).source ∩ (R.atlas.A b).source from ⟨ha, hb⟩)]
    exact hs a b x ha hb

theorem b66m_rs_product_ne_zero (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q r : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) (hr : r ∈ b66g_forms R t 1)
    (hq0 : q ≠ 0) (hr0 : r ≠ 0) : b66g_product R q r ≠ 0 := by
  obtain ⟨T, hT⟩ := b66m_rs_form_zeros_finite R t hq hq0
  obtain ⟨U, hU⟩ := b66m_rs_form_zeros_finite R t hr hr0
  obtain ⟨p⟩ : Nonempty (rf8_fibre R.C t) := inferInstance
  obtain ⟨y, hy⟩ := RiemannRochAna_exists_unmarked (Module.finrank_self ℂ) p
    (fun x : ↥(T ∪ U) => b66m_sc_pt R t x.val)
  have hx : y.val.2 ∉ T ∪ U := by
    intro hx
    apply hy
    exact ⟨⟨y.val.2, hx⟩, b66m_sc_fibre_mk R t y⟩
  intro hz
  have hp := congrFun (congrFun hz (t, y.val.2)) y.val.2
  change q (t, y.val.2) y.val.2 * r (t, y.val.2) y.val.2 = 0 at hp
  rcases mul_eq_zero.mp hp with hqz | hrz
  · exact hx (Finset.mem_union_left _ (hT _ hqz))
  · exact hx (Finset.mem_union_right _ (hU _ hrz))

theorem b66m_rs_scalarBoundary_add (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (v w : b66k_Index R → ℂ → ℂ) :
    b66g_scalarBoundary R t (v + w) = b66g_scalarBoundary R t v + b66g_scalarBoundary R t w := by
  funext a b x
  simp only [b66g_scalarBoundary, Pi.add_apply]
  split_ifs <;> ring

theorem b66m_rs_scalarBoundary_smul (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (c : ℂ) (v : b66k_Index R → ℂ → ℂ) :
    b66g_scalarBoundary R t (c • v) = c • b66g_scalarBoundary R t v := by
  funext a b x
  simp only [b66g_scalarBoundary, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem b66m_rs_scalarBoundary_representation (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (u : b66k_Cochain R) (hu : u ∈ b66g_scalarBoundaries R t) :
    ∃ v : b66k_Index R → ℂ → ℂ,
      (∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a)) ∧ u = b66g_scalarBoundary R t v := by
  induction hu using Submodule.span_induction with
  | mem u hu => exact hu
  | zero =>
    refine ⟨0, fun a z hz => analyticAt_const, ?_⟩
    funext a b x
    simp [b66g_scalarBoundary]
  | add u w hu hw ihu ihw =>
    obtain ⟨v, hv, rfl⟩ := ihu
    obtain ⟨v', hv', rfl⟩ := ihw
    exact ⟨v + v', fun a => (hv a).add (hv' a), (b66m_rs_scalarBoundary_add R t v v').symm⟩
  | smul c u hu ihu =>
    obtain ⟨v, hv, rfl⟩ := ihu
    refine ⟨c • v, ?_, (b66m_rs_scalarBoundary_smul R t c v).symm⟩
    intro a
    simpa only [Pi.smul_apply] using (hv a).const_smul (c := c)

def b66m_rs_resPair (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : ↥(b66g_scalarCycles R t))
    (q : b66g_Coeff R) : ℂ :=
  b66g_residueSum R t (Classical.choose (b66m_rs_scalar_splitting R t u.val u.property))
    (Classical.choose (Classical.choose_spec
      (b66m_rs_scalar_splitting R t u.val u.property))) q


theorem b66m_rs_resPair_eq (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : ↥(b66g_scalarCycles R t))
    (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hreg : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u.val a b x = b66g_scalarBoundary R t v a b x)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) :
    b66m_rs_resPair R t u q = b66g_residueSum R t S v q := by
  have h := Classical.choose_spec (Classical.choose_spec
    (b66m_rs_scalar_splitting R t u.val u.property))
  exact b66m_rs_scalar_split_unique R t u.val _ S _ v h.1 h.2.1 h.2.2 hmero hreg hv hq


theorem b66m_rs_resPair_split (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : ↥(b66g_scalarCycles R t)) :
    ∃ (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ),
      (∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z) ∧
      (∀ a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z) ∧
      (∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source → u.val a b x = b66g_scalarBoundary R t v a b x) :=
  b66m_rs_scalar_splitting R t u.val u.property


theorem b66m_rs_resPair_add (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u w : ↥(b66g_scalarCycles R t))
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) :
    b66m_rs_resPair R t (u + w) q = b66m_rs_resPair R t u q + b66m_rs_resPair R t w q := by
  obtain ⟨S, v, h1, h2, h3⟩ := b66m_rs_resPair_split R t u
  obtain ⟨S', v', h1', h2', h3'⟩ := b66m_rs_resPair_split R t w
  rw [b66m_rs_resPair_eq R t u S v h1 h2 h3 hq, b66m_rs_resPair_eq R t w S' v' h1' h2' h3' hq,
    ← b66m_rs_residueSum_extend R t S (S ∪ S') v h2 hq Finset.subset_union_left,
    ← b66m_rs_residueSum_extend R t S' (S ∪ S') v' h2' hq Finset.subset_union_right,
    ← b66m_rs_residueSum_add R t _ v v' h1 h1' hq]
  apply b66m_rs_resPair_eq R t (u + w) (S ∪ S') (v + v')
    (fun a z hz => (h1 a z hz).add (h1' a z hz))
    (fun a z hz hS => (h2 a z hz fun h => hS (Finset.mem_union_left _ h)).add
      (h2' a z hz fun h => hS (Finset.mem_union_right _ h)))
    (fun a b x hx ha hb => ?_) hq
  rw [b66m_rs_scalarBoundary_add, Pi.add_apply, Pi.add_apply, Pi.add_apply,
    ← h3 a b x (fun h => hx (Finset.mem_union_left _ h)) ha hb,
    ← h3' a b x (fun h => hx (Finset.mem_union_right _ h)) ha hb]
  rfl


theorem b66m_rs_resPair_smul (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (c : ℂ)
    (u : ↥(b66g_scalarCycles R t))
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) :
    b66m_rs_resPair R t (c • u) q = c * b66m_rs_resPair R t u q := by
  obtain ⟨S, v, h1, h2, h3⟩ := b66m_rs_resPair_split R t u
  rw [b66m_rs_resPair_eq R t u S v h1 h2 h3 hq, ← b66m_rs_residueSum_vsmul]
  apply b66m_rs_resPair_eq R t (c • u) S (c • v)
    (fun a z hz => (h1 a z hz).const_smul c)
    (fun a z hz hS => (h2 a z hz hS).const_smul (c := c))
    (fun a b x hx ha hb => ?_) hq
  rw [b66m_rs_scalarBoundary_smul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
    ← h3 a b x hx ha hb]
  rfl


theorem b66m_rs_resPair_boundary (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : ↥(b66g_scalarCycles R t))
    (hb : u.val ∈ b66g_scalarBoundaries R t) {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) :
    b66m_rs_resPair R t u q = 0 := by
  obtain ⟨v, hv, hu⟩ := b66m_rs_scalarBoundary_representation R t u.val hb
  rw [b66m_rs_resPair_eq R t u ∅ v (fun a z hz => (hv a z hz).meromorphicAt)
    (fun a z hz _ => hv a z hz) (fun a b x _ _ _ => by rw [hu]) hq]
  simp [b66g_residueSum]


theorem b66m_rs_serre_functional (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ∃ E : b66g_H1O R t →ₗ[ℂ] Module.Dual ℂ (b66g_forms R t 1),
      ∀ (u : b66k_Cochain R)
      (_hu : u ∈ b66g_scalarCycles R t)
      (c : b66g_H1O R t) (_hc : c.val = (b66g_scalarBoundaries R t).mkQ u)
      (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
      (_hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
      (_hreg : ∀ a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
      (_hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source →
        u a b x = b66g_scalarBoundary R t v a b x) (q : b66g_forms R t 1),
      E c q = b66g_residueSum R t S v q.val := by
  let Z := b66g_scalarCycles R t
  let Φ : Z →ₗ[ℂ] Module.Dual ℂ (b66g_forms R t 1) :=
    LinearMap.mk₂ ℂ (fun (u : Z) (q : b66g_forms R t 1) => b66m_rs_resPair R t u q.val)
      (fun u w q => b66m_rs_resPair_add R t u w q.property)
      (fun c u q => b66m_rs_resPair_smul R t c u q.property)
      (fun u q r => by
        obtain ⟨S, v, h1, h2, h3⟩ := b66m_rs_resPair_split R t u
        change b66m_rs_resPair R t u (q.val + r.val) = _
        rw [b66m_rs_resPair_eq R t u S v h1 h2 h3 (add_mem q.property r.property),
          b66m_rs_resPair_eq R t u S v h1 h2 h3 q.property,
          b66m_rs_resPair_eq R t u S v h1 h2 h3 r.property]
        exact b66m_rs_residueSum_qadd R t S v h1 q.property r.property)
      (fun c u q => by
        obtain ⟨S, v, h1, h2, h3⟩ := b66m_rs_resPair_split R t u
        change b66m_rs_resPair R t u (c • q.val) = c * _
        rw [b66m_rs_resPair_eq R t u S v h1 h2 h3 (Submodule.smul_mem _ c q.property),
          b66m_rs_resPair_eq R t u S v h1 h2 h3 q.property]
        exact b66m_rs_residueSum_smul R t S v c q.val)
  let f : Z →ₗ[ℂ] b66g_scalarQuotient R t := (b66g_scalarBoundaries R t).mkQ ∘ₗ Z.subtype
  have hker : LinearMap.ker f ≤ LinearMap.ker Φ := by
    intro u hu
    have hb : u.val ∈ b66g_scalarBoundaries R t :=
      (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.mem_ker.mp hu)
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro q
    exact b66m_rs_resPair_boundary R t u hb q.property
  have hrange : LinearMap.range f = b66g_H1O R t := by
    simp only [f, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  refine ⟨(LinearMap.ker f).liftQ Φ hker ∘ₗ f.quotKerEquivRange.symm.toLinearMap ∘ₗ
    (LinearEquiv.ofEq _ _ hrange.symm).toLinearMap, ?_⟩
  intro u hu c hc S v hmero hreg hv q
  have he : f.quotKerEquivRange.symm (LinearEquiv.ofEq _ _ hrange.symm c) =
      (LinearMap.ker f).mkQ ⟨u, hu⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    simp only [LinearEquiv.coe_ofEq_apply, Submodule.mkQ_apply,
      LinearMap.quotKerEquivRange_apply_mk]
    exact hc
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he,
    Submodule.liftQ_apply, Submodule.mkQ_apply]
  exact b66m_rs_resPair_eq R t ⟨u, hu⟩ S v hmero hreg hv q.property


end HodgeLean.Foundations.Program
