import HodgeLean.Foundations.AnalyticGermExtension
import HodgeLean.Foundations.AnalyticDivisorAlgebraic20Proofs
import Mathlib.Analysis.Normed.Field.Approximation

/-! # Continuation toward point extension

Implication from bounded holomorphy off a hypersurface to analytic continuation,
and from dense parameter sets to closure of monic zero loci.
Adapted projection and mixed-relation exactness at the missing point remain deferred.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Polynomial
namespace HodgeLean.Foundations

namespace Adim8Extension

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic18
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open HodgeLean.Foundations.AnalyticDivisorAlgebraic12

open HodgeLean.Foundations.AnalyticDivisorAlgebraic18
open HodgeLean.Foundations.AnalyticDivisorAlgebraic19
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic17
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7

private theorem adim8_bounded_mul_square_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {D c : E → ℂ} {x : E} (hD : DifferentiableAt ℂ D x) (hDx : D x = 0)
    (hc : ∃ C : ℝ, ∀ᶠ y in nhds x, D y ≠ 0 → ‖c y‖ ≤ C) :
    HasFDerivAt (fun y ↦ D y ^ 2 * c y) (0 : E →L[ℂ] ℂ) x := by
  obtain ⟨C, hC⟩ := hc
  have hbound : (fun y ↦ D y ^ 2 * c y) =O[nhds x] (fun y ↦ D y ^ 2) := by
    apply Asymptotics.IsBigO.of_bound (max C 0)
    filter_upwards [hC] with y hy
    by_cases hDy : D y = 0
    · simp only [hDy, zero_pow (by decide : 2 ≠ 0), zero_mul, norm_zero, mul_zero, le_refl]
    · rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left ((hy hDy).trans (le_max_left C 0))
        (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hlinear : D =O[nhds x] (fun y ↦ ‖y - x‖) := by
    simpa only [hDx, sub_zero] using hD.isBigO_sub.norm_right
  exact (hbound.trans (hlinear.pow 2)).hasFDerivAt (by decide : 1 < 2)

private theorem adim8_analytic_bounded_mul_square
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} {D c : E → ℂ} (hU : IsOpen U) (hD : AnalyticOnNhd ℂ D U)
    (hc : AnalyticOnNhd ℂ c {x ∈ U | D x ≠ 0})
    (hb : ∀ x ∈ U, ∃ C : ℝ, ∀ᶠ y in nhds x, D y ≠ 0 → ‖c y‖ ≤ C) :
    AnalyticOnNhd ℂ (fun y ↦ D y ^ 2 * c y) U := by
  apply HodgeLean.Foundations.AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn hU
  intro x hx
  by_cases hDx : D x = 0
  · exact (adim8_bounded_mul_square_derivative (hD x hx).differentiableAt hDx
      (hb x hx)).differentiableAt.differentiableWithinAt
  · exact (((hD x hx).pow 2).mul (hc x ⟨hx, hDx⟩)).differentiableAt.differentiableWithinAt

private theorem adim8_eventually_frequently_nonzero {n : ℕ}
    {D : (Fin n → ℂ) → ℂ} {p : Fin n → ℂ} (hD : AnalyticAt ℂ D p)
    (hnz : ¬ ∀ᶠ z in nhds p, D z = 0) :
    ∀ᶠ y in nhds p, ∃ᶠ z in nhds y, D z ≠ 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hD.eventually_analyticAt
  have hgp : @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) D ≠ 0 := by
    intro h
    exact hnz (Filter.Germ.coe_eq.mp h)
  filter_upwards [Metric.ball_mem_nhds p hr] with y hy
  have hgy := HodgeLean.Foundations.AnalyticDivisorAlgebraic12.spec_germ_ne_zero_of_preconnected
    D (Metric.ball p r) Metric.isOpen_ball (convex_ball p r).isPreconnected
    hball p y (Metric.mem_ball_self hr) hy hgp
  apply Filter.not_eventually.mp
  intro h
  exact hgy (Filter.Germ.coe_eq.mpr h)

private theorem adim8_extend_norm_bound {n : ℕ}
    {D f g : (Fin n → ℂ) → ℂ} {p : Fin n → ℂ} {C : ℝ}
    (hD : AnalyticAt ℂ D p) (hnz : ¬ ∀ᶠ z in nhds p, D z = 0)
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hb : ∀ᶠ z in nhds p, D z ≠ 0 → ‖f z‖ ≤ C * ‖g z‖) :
    ∀ᶠ z in nhds p, ‖f z‖ ≤ C * ‖g z‖ := by
  filter_upwards [adim8_eventually_frequently_nonzero hD hnz,
    hf.eventually_analyticAt, hg.eventually_analyticAt, hb.eventually_nhds]
      with y hy hfy hgy hby
  exact le_of_tendsto_of_tendsto_of_frequently hfy.continuousAt.norm
    (continuousAt_const.mul hgy.continuousAt.norm)
    ((hy.and_eventually hby).mono fun z hz ↦ hz.2 hz.1)

open HodgeLean.Foundations.AnalyticDivisorAlgebraic11 in
private theorem adim8_irreducible_representative {n : ℕ} {p : Fin n → ℂ}
    (A : AnalyticGermAt n p) (hA : Irreducible A) :
    ∃ a : (Fin n → ℂ) → ℂ, ∃ ha : AnalyticAt ℂ a p,
      A = ⟨Filter.Germ.ofFun a, a, ha, rfl⟩ ∧ IsIrreducibleAt a p := by
  obtain ⟨a, ha, har⟩ := A.2
  have hAr : A = ⟨Filter.Germ.ofFun a, a, ha, rfl⟩ := Subtype.ext har.symm
  subst A
  refine ⟨a, ha, rfl, ?_, ?_⟩
  · by_contra hap
    apply hA.not_isUnit
    apply isUnit_iff_exists_inv.mpr
    let B : AnalyticGermAt n p :=
      ⟨Filter.Germ.ofFun (fun z ↦ (a z)⁻¹), fun z ↦ (a z)⁻¹, ha.inv hap, rfl⟩
    refine ⟨B, Subtype.ext ?_⟩
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [ha.continuousAt.eventually_ne hap] with z hz
    exact mul_inv_cancel₀ hz
  · intro b c hb hc hfac
    let B : AnalyticGermAt n p := ⟨Filter.Germ.ofFun b, b, hb, rfl⟩
    let C : AnalyticGermAt n p := ⟨Filter.Germ.ofFun c, c, hc, rfl⟩
    have hAC : (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ : AnalyticGermAt n p) = B * C :=
      Subtype.ext (Filter.Germ.coe_eq.mpr hfac)
    rcases hA.isUnit_or_isUnit hAC with hB | hC
    · left
      intro hbp
      exact (hB.map (analyticGermAtValue n p)).ne_zero
        (by change (Filter.Germ.ofFun b).value = 0
            rw [Filter.Germ.value_ofFun, hbp])
    · right
      intro hcp
      exact (hC.map (analyticGermAtValue n p)).ne_zero
        (by change (Filter.Germ.ofFun c).value = 0
            rw [Filter.Germ.value_ofFun, hcp])

open HodgeLean.Foundations.AnalyticDivisorAlgebraic11 in
private theorem adim8_germ_dvd_of_norm_bound {n : ℕ} {p : Fin n → ℂ}
    (G : AnalyticGermAt n p) :
    ∀ (g : (Fin n → ℂ) → ℂ) (hg : AnalyticAt ℂ g p),
      (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p) = G →
      ∀ (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p) (C : ℝ),
      (∀ᶠ z in nhds p, ‖f z‖ ≤ C * ‖g z‖) →
      G ∣ (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p) := by
  obtain ⟨e, -, -⟩ := spec_germ_translation_equiv n p
  let : UniqueFactorizationMonoid (AnalyticGermAt n p) :=
    e.symm.toMulEquiv.uniqueFactorizationMonoid (spec_analyticGerm_ufd n)
  induction G using WfDvdMonoid.induction_on_irreducible with
  | zero =>
      intro g hg hg0 f hf C hb
      have hgz : ∀ᶠ z in nhds p, g z = 0 :=
        Filter.Germ.coe_eq.mp (congrArg Subtype.val hg0)
      have hfz : (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p) = 0 := by
        apply Subtype.ext
        apply Filter.Germ.coe_eq.mpr
        filter_upwards [hb, hgz] with z hz hzg
        simpa only [hzg, norm_zero, mul_zero, norm_le_zero_iff] using hz
      rw [hfz]
  | unit G hG =>
      intro g hg heq f hf C hb
      exact hG.dvd
  | mul A I hA hI ih =>
      intro g hg hgG f hf C hb
      obtain ⟨a, ha, har⟩ := A.2
      have haA : (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ : AnalyticGermAt n p) = A :=
        Subtype.ext har
      obtain ⟨i, hi, hIi, hirr⟩ := adim8_irreducible_representative I hI
      have hgi : g =ᶠ[nhds p] fun z ↦ i z * a z := by
        apply Filter.Germ.coe_eq.mp
        exact congrArg Subtype.val (hgG.trans (by rw [hIi, ← haA]))
      have hz : ∀ᶠ z in nhds p, i z = 0 → f z = 0 := by
        filter_upwards [hb, hgi] with z hzb hzgi hzi
        rw [hzgi, hzi, zero_mul, norm_zero, mul_zero] at hzb
        exact norm_le_zero_iff.mp hzb
      obtain ⟨c, hc, hfc⟩ := spec_hypersurface_nullstellensatz n p i f hi hf hirr hz
      have hinz : ¬ ∀ᶠ z in nhds p, i z = 0 := by
        intro h
        apply hI.ne_zero
        rw [hIi]
        exact Subtype.ext (Filter.Germ.coe_eq.mpr h)
      have hbc : ∀ᶠ z in nhds p, ‖c z‖ ≤ C * ‖a z‖ := by
        apply adim8_extend_norm_bound hi hinz hc ha
        filter_upwards [hb, hgi, hfc] with z hzb hzgi hzfc hzi
        rw [hzfc, hzgi, norm_mul, norm_mul] at hzb
        rw [← mul_assoc, mul_comm C ‖i z‖, mul_assoc] at hzb
        exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hzi)).mp hzb
      have hac := ih a ha haA c hc C hbc
      have hfI : (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p) =
          I * ⟨Filter.Germ.ofFun c, c, hc, rfl⟩ := by
        rw [hIi]
        exact Subtype.ext (Filter.Germ.coe_eq.mpr hfc)
      rw [hfI]
      exact mul_dvd_mul_left I hac

open HodgeLean.Foundations.AnalyticDivisorAlgebraic11 in
private theorem adim8_analytic_division_of_norm_bound {n : ℕ} {p : Fin n → ℂ}
    {f g : (Fin n → ℂ) → ℂ} (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    {C : ℝ} (hb : ∀ᶠ z in nhds p, ‖f z‖ ≤ C * ‖g z‖) :
    ∃ q : (Fin n → ℂ) → ℂ, AnalyticAt ℂ q p ∧
      f =ᶠ[nhds p] fun z ↦ g z * q z := by
  obtain ⟨Q, hQ⟩ := adim8_germ_dvd_of_norm_bound
    (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p) g hg rfl f hf C hb
  obtain ⟨q, hq, hqr⟩ := Q.2
  refine ⟨q, hq, Filter.Germ.coe_eq.mp ?_⟩
  have hQq : Q = (⟨Filter.Germ.ofFun q, q, hq, rfl⟩ : AnalyticGermAt n p) :=
    Subtype.ext hqr.symm
  exact congrArg Subtype.val (hQ.trans (by rw [hQq]))

private theorem adim8_bounded_holomorphic_extension {n : ℕ}
    {U : Set (Fin n → ℂ)} {D c : (Fin n → ℂ) → ℂ}
    (hU : IsOpen U) (hD : AnalyticOnNhd ℂ D U)
    (hc : AnalyticOnNhd ℂ c {x ∈ U | D x ≠ 0})
    (hb : ∀ x ∈ U, ∃ C : ℝ, ∀ᶠ y in nhds x, D y ≠ 0 → ‖c y‖ ≤ C)
    {p : Fin n → ℂ} (hp : p ∈ U) :
    ∃ q : (Fin n → ℂ) → ℂ, AnalyticAt ℂ q p ∧
      ∀ᶠ z in nhds p, D z ≠ 0 → q z = c z := by
  have hH := adim8_analytic_bounded_mul_square hU hD hc hb p hp
  obtain ⟨C, hC⟩ := hb p hp
  have hbound : ∀ᶠ z in nhds p, ‖D z ^ 2 * c z‖ ≤ C * ‖D z ^ 2‖ := by
    filter_upwards [hC] with z hz
    by_cases hDz : D z = 0
    · simp only [hDz, zero_pow (by decide : 2 ≠ 0), zero_mul, norm_zero, mul_zero, le_refl]
    · rw [norm_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hz hDz) (norm_nonneg _)
  obtain ⟨q, hq, heq⟩ := adim8_analytic_division_of_norm_bound hH ((hD p hp).pow 2) hbound
  refine ⟨q, hq, heq.mono fun z hz hDz ↦ ?_⟩
  exact (mul_left_cancel₀ (pow_ne_zero 2 hDz) hz).symm

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5 in
private theorem adim8_monic_factor_coeff_bounded {n d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} {p : Fin n → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) p) :
    ∃ C : ℝ, ∀ᶠ z in nhds p, ∀ Q : Polynomial ℂ,
      Q.Monic → Q ∣ monicPoly a z → ∀ k, ‖Q.coeff k‖ ≤ C := by
  let B : (Fin n → ℂ) → ℝ := fun z ↦
    2 ^ d * ∑ j ∈ Finset.range (d + 1), ‖(monicPoly a z).coeff j‖
  have hB : ContinuousAt B p := by
    apply continuousAt_const.mul
    exact tendsto_finsetSum _ fun j _ ↦
      (gaga5b_analyticAt_coeff_monicPoly ha j).continuousAt.norm
  refine ⟨B p + 1, ?_⟩
  filter_upwards [hB.eventually (gt_mem_nhds (by linarith : B p < B p + 1))]
    with z hz Q hQ hdiv k
  have hbound := Polynomial.norm_coeff_le_of_monic_dvd (spec_monicPoly a z).1 hQ hdiv k
  rw [(spec_monicPoly a z).2.1] at hbound
  exact hbound.trans hz.le

private theorem adim8_bounded_holomorphic_extension_on {n : ℕ}
    {U : Set (Fin n → ℂ)} {D c : (Fin n → ℂ) → ℂ}
    (hU : IsOpen U) (hD : AnalyticOnNhd ℂ D U)
    (hnz : ∀ x ∈ U, ¬ ∀ᶠ y in nhds x, D y = 0)
    (hc : AnalyticOnNhd ℂ c {x ∈ U | D x ≠ 0})
    (hb : ∀ x ∈ U, ∃ C : ℝ, ∀ᶠ y in nhds x, D y ≠ 0 → ‖c y‖ ≤ C) :
    ∃ Q : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ Q U ∧
      ∀ x ∈ U, D x ≠ 0 → Q x = c x := by
  classical
  have hlocal := fun x : U ↦ adim8_bounded_holomorphic_extension hU hD hc hb x.property
  choose q hq hqc using hlocal
  let Q : (Fin n → ℂ) → ℂ := fun z ↦ if hz : z ∈ U then q ⟨z, hz⟩ z else 0
  refine ⟨Q, ?_, ?_⟩
  · intro x hx
    apply (hq ⟨x, hx⟩).congr
    filter_upwards [hU.mem_nhds hx, (hq ⟨x, hx⟩).eventually_analyticAt,
      (hqc ⟨x, hx⟩).eventually_nhds] with y hy hqy hqcy
    have heq : q ⟨x, hx⟩ y = q ⟨y, hy⟩ y := by
      apply tendsto_nhds_unique_of_frequently_eq hqy.continuousAt (hq ⟨y, hy⟩).continuousAt
      have hfreq : ∃ᶠ z in nhds y, D z ≠ 0 := Filter.not_eventually.mp (hnz y hy)
      exact ((hfreq.and_eventually hqcy).and_eventually (hqc ⟨y, hy⟩)).mono
        fun z hz ↦ (hz.1.2 hz.1.1).trans (hz.2 hz.1.1).symm
    simpa only [Q, dite_eq_left hy] using heq
  · intro x hx hDx
    simpa only [Q, dite_eq_left hx] using (hqc ⟨x, hx⟩).self_of_nhds hDx


end Adim8Extension

private def adim8MonicPolynomial {d k : ℕ}
    (a : Fin k → (Fin d → ℂ) → ℂ) (w : Fin d → ℂ) : ℂ[X] :=
  X ^ k + ∑ i : Fin k, C (a i w) * X ^ (i : ℕ)

private lemma adim8MonicPolynomial_monic {d k : ℕ}
    (a : Fin k → (Fin d → ℂ) → ℂ) (w : Fin d → ℂ) :
    (adim8MonicPolynomial a w).Monic := by
  exact monic_X_pow_add (degree_sum_fin_lt fun i ↦ a i w)

private lemma adim8MonicPolynomial_eval {d k : ℕ}
    (a : Fin k → (Fin d → ℂ) → ℂ) (w : Fin d → ℂ) (t : ℂ) :
    (adim8MonicPolynomial a w).eval t =
      t ^ k + ∑ i : Fin k, a i w * t ^ (i : ℕ) := by
  simp [adim8MonicPolynomial, eval_finsetSum]

private lemma adim8MonicPolynomial_natDegree {d k : ℕ}
    (a : Fin k → (Fin d → ℂ) → ℂ) (w : Fin d → ℂ) :
    (adim8MonicPolynomial a w).natDegree = k := by
  rw [adim8MonicPolynomial, natDegree_add_eq_left_of_degree_lt (by
    simpa using (degree_sum_fin_lt fun i ↦ a i w)), natDegree_X_pow]

private lemma adim8_root_nearby {k : ℕ} (hk : 0 < k) (f g : ℂ[X]) (z : ℂ)
    (hf : f.Monic) (hg : g.Monic) (hfn : f.natDegree = k) (hgn : g.natDegree = k)
    (hz : f.eval z = 0) {e : ℝ} (he : 0 < e)
    (hcoeff : ∀ n : ℕ,
      ‖g.coeff n - f.coeff n‖ <
        (e / max ‖z‖ 1) ^ k / (2 * (k + 1))) :
    ∃ y : ℂ, g.eval y = 0 ∧ ‖z - y‖ < e := by
  have hdeg : g.natDegree = f.natDegree := by
    rw [hgn, hfn]
  have heta : 0 < (e / max ‖z‖ 1) ^ k / (2 * (k + 1)) := by positivity
  obtain ⟨y, hyroot, hy⟩ :=
    exists_roots_norm_sub_lt_of_norm_coeff_sub_lt heta hz hf hg hdeg hcoeff
      (IsAlgClosed.splits g)
  refine ⟨y, (mem_roots'.mp hyroot).2, hy.trans ?_⟩
  have hr : 0 < e / max ‖z‖ 1 := div_pos he (by positivity)
  have hbase :
      (f.natDegree + 1) * ((e / max ‖z‖ 1) ^ k / (2 * (k + 1))) <
        (e / max ‖z‖ 1) ^ k := by
    rw [hfn]
    have hp : 0 < (e / max ‖z‖ 1) ^ k := pow_pos hr k
    field_simp
    nlinarith
  have hpow := Real.rpow_lt_rpow (by positivity) hbase (by positivity : 0 < (k : ℝ)⁻¹)
  rw [hfn, Real.pow_rpow_inv_natCast hr.le hk.ne'] at hpow
  calc
    ((f.natDegree + 1) * ((e / max ‖z‖ 1) ^ k / (2 * (k + 1)))) ^
          (f.natDegree : ℝ)⁻¹ * max ‖z‖ 1
        < (e / max ‖z‖ 1) * max ‖z‖ 1 :=
      by rw [hfn]; exact mul_lt_mul_of_pos_right hpow (by positivity)
    _ = e := div_mul_cancel₀ e (by positivity)

/-- Source: Gunning--Rossi, Analytic Functions of Several Complex Variables, III.C, Riemann extension theorem across an analytic subset; Chirka, Complex Analytic Sets, §4. -/
theorem adim8_hypersurface_extension_aux (d : ℕ) (V : Set (Fin (d + 1) → ℂ))
    (hV : IsOpen V) (δ f : (Fin (d + 1) → ℂ) → ℂ)
    (hδ : AnalyticOnNhd ℂ δ V)
    (hnz : ∀ x ∈ V, ¬ (δ =ᶠ[𝓝 x] fun _ ↦ 0))
    (hf : AnalyticOnNhd ℂ f (V \ {x | δ x = 0}))
    (C : ℝ) (hb : ∀ x ∈ V \ {x | δ x = 0}, ‖f x‖ ≤ C) :
    ∃ F : (Fin (d + 1) → ℂ) → ℂ,
      AnalyticOnNhd ℂ F V ∧ Set.EqOn F f (V \ {x | δ x = 0}) ∧
      (∀ x ∈ V, ‖F x‖ ≤ C) ∧
      ∀ G : (Fin (d + 1) → ℂ) → ℂ,
        ContinuousOn G V → Set.EqOn G f (V \ {x | δ x = 0}) → Set.EqOn G F V := by
  classical
  have hlocal : ∀ x ∈ V, ∃ C' : ℝ, ∀ᶠ y in nhds x, δ y ≠ 0 → ‖f y‖ ≤ C' := by
    intro x hx
    refine ⟨C, ?_⟩
    filter_upwards [hV.mem_nhds hx] with y hy hδy
    exact hb y ⟨hy, hδy⟩
  obtain ⟨F, hF, hFf⟩ := Adim8Extension.adim8_bounded_holomorphic_extension_on
    hV hδ hnz hf hlocal
  refine ⟨F, hF, ?_, ?_, ?_⟩
  · intro x hx
    exact hFf x hx.1 hx.2
  · intro x hx
    have hevent : ∀ᶠ y in nhds x, δ y ≠ 0 → ‖F y‖ ≤ C := by
      filter_upwards [hV.mem_nhds hx] with y hy hδy
      rw [hFf y hy hδy]
      exact hb y ⟨hy, hδy⟩
    simpa using (Adim8Extension.adim8_extend_norm_bound (D := δ) (f := F)
      (g := fun _ ↦ 1) (C := C) (hδ x hx) (hnz x hx)
      (hF x hx) analyticAt_const (by simpa using hevent)).self_of_nhds
  · intro G hG hGf x hx
    apply tendsto_nhds_unique_of_frequently_eq
      (hG.continuousAt (hV.mem_nhds hx)).tendsto
      (hF x hx).continuousAt.tendsto
    have hfreq := Filter.not_eventually.mp (hnz x hx)
    exact (hfreq.and_eventually (hV.mem_nhds hx)).mono fun y hy ↦
      (hGf ⟨hy.2, hy.1⟩).trans (hFf y hy.2 hy.1).symm

/-- Source: Gunning--Rossi, III.C and V, continuation of coefficients; adim6_bounded_point_extension. -/
theorem adim8_coefficient_extension_aux (d k : ℕ) (U : Set (Fin (d + 1) → ℂ))
    (hU : IsOpen U) (hU0 : (0 : Fin (d + 1) → ℂ) ∈ U)
    (δ : (Fin (d + 1) → ℂ) → ℂ)
    (hδ : AnalyticOnNhd ℂ δ (U \ {0}))
    (hnz : ∀ x ∈ U \ {0}, ¬ (δ =ᶠ[𝓝 x] fun _ ↦ 0))
    (a : Fin k → (Fin (d + 1) → ℂ) → ℂ)
    (ha : ∀ i, AnalyticOnNhd ℂ (a i) ((U \ {0}) \ {x | δ x = 0}))
    (C : Fin k → ℝ)
    (hb : ∀ i x, x ∈ (U \ {0}) \ {x | δ x = 0} → ‖a i x‖ ≤ C i) :
    ∃ b : Fin k → (Fin (d + 1) → ℂ) → ℂ,
      (∀ i, AnalyticOnNhd ℂ (b i) U) ∧
      (∀ i, Set.EqOn (b i) (a i) ((U \ {0}) \ {x | δ x = 0})) ∧
      (∀ i x, x ∈ U → ‖b i x‖ ≤ C i) := by
  have hU' : IsOpen (U \ {(0 : Fin (d + 1) → ℂ)}) := hU.sdiff isClosed_singleton
  choose f hf hfa hfb huniq using fun i ↦
    adim8_hypersurface_extension_aux d (U \ {0}) hU' δ (a i) hδ hnz (ha i) (C i)
      (hb i)
  let b : Fin k → (Fin (d + 1) → ℂ) → ℂ := fun i ↦
    Function.update (f i) 0 (limUnder (𝓝[≠] 0) (f i))
  have hb_analytic : ∀ i, AnalyticOnNhd ℂ (b i) U := by
    intro i
    exact adim6_bounded_point_extension d U hU hU0 (f i) (hf i) ⟨C i, hfb i⟩
  refine ⟨b, hb_analytic, ?_, ?_⟩
  · intro i x hx
    have hx0 : x ≠ 0 := by simpa using hx.1.2
    rw [show b i x = f i x by simp [b, hx0]]
    exact hfa i hx
  · intro i x hx
    by_cases hx0 : x = 0
    · subst x
      have hcont : ContinuousAt (b i) 0 := (hb_analytic i 0 hU0).continuousAt
      have hevent : ∀ᶠ z in 𝓝[≠] (0 : Fin (d + 1) → ℂ), ‖b i z‖ ≤ C i := by
        filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hU0),
          self_mem_nhdsWithin] with z hzU hz0
        have hz0' : z ≠ 0 := by simpa using hz0
        simpa [b, hz0'] using hfb i z ⟨hzU, hz0'⟩
      exact le_of_tendsto (hcont.norm.tendsto.mono_left nhdsWithin_le_nhds) hevent
    · simpa [b, hx0] using hfb i x ⟨hx, hx0⟩

/-- Source: Gunning--Rossi, I.A, argument principle and continuity of roots of monic polynomials; III.C, finite hypersurface projections. -/
theorem adim8_monic_closure_aux (d k : ℕ) (U D : Set (Fin d → ℂ))
    (hU : IsOpen U) (hDU : D ⊆ U) (hdense : U ⊆ closure D)
    (a : Fin k → (Fin d → ℂ) → ℂ) (ha : ∀ i, ContinuousOn (a i) U) :
    ∀ p : (Fin d → ℂ) × ℂ, p.1 ∈ U →
      (p ∈ closure {q : (Fin d → ℂ) × ℂ |
        q.1 ∈ D ∧ q.2 ^ k + ∑ i : Fin k, a i q.1 * q.2 ^ (i : ℕ) = 0} ↔
        p.2 ^ k + ∑ i : Fin k, a i p.1 * p.2 ^ (i : ℕ) = 0) := by
  intro p hp
  let Z : Set ((Fin d → ℂ) × ℂ) := {q |
    q.1 ∈ D ∧ q.2 ^ k + ∑ i : Fin k, a i q.1 * q.2 ^ (i : ℕ) = 0}
  let F : ((Fin d → ℂ) × ℂ) → ℂ := fun q ↦
    q.2 ^ k + ∑ i : Fin k, a i q.1 * q.2 ^ (i : ℕ)
  have hF : ContinuousOn F {q | q.1 ∈ U} := by
    apply ContinuousOn.add (continuousOn_snd.pow k)
      (continuousOn_finsetSum Finset.univ fun i _ ↦ ?_)
    exact ((ha i).comp continuousOn_fst (fun q hq ↦ hq)).mul (continuousOn_snd.pow i)
  constructor
  · intro hpZ
    have hcont : ContinuousWithinAt F Z p :=
      (hF p hp).mono (fun q hq ↦ hDU hq.1)
    have := hcont.eq_const_of_mem_closure hpZ (fun q hq ↦ hq.2)
    simpa [F, adim8MonicPolynomial_eval] using this
  · intro hz
    by_cases hk0 : k = 0
    · subst k
      simp at hz
    have hk : 0 < k := Nat.pos_of_ne_zero hk0
    rw [← adim8MonicPolynomial_eval] at hz
    rw [Metric.mem_closure_iff]
    intro e he
    let η : ℝ := (e / 2 / max ‖p.2‖ 1) ^ k / (2 * (k + 1))
    have hη : 0 < η := by dsimp [η]; positivity
    have hnear : ∀ i : Fin k,
        Filter.Eventually (fun w ↦ ‖a i w - a i p.1‖ < η) (nhds p.1) := by
      intro i
      have hi := ((ha i p.1 hp).continuousAt (hU.mem_nhds hp)).tendsto.eventually
        (Metric.ball_mem_nhds (a i p.1) hη)
      simpa [Metric.mem_ball, dist_eq_norm] using hi
    have hevent : Filter.Eventually
        (fun w ↦ dist w p.1 < e / 2 ∧ ∀ i : Fin k, ‖a i w - a i p.1‖ < η)
        (nhds p.1) := by
      have he' : Filter.Eventually (fun w ↦ dist w p.1 < e / 2) (nhds p.1) := by
        filter_upwards [Metric.ball_mem_nhds p.1 (half_pos he)] with w hw
        simpa [Metric.mem_ball, dist_comm] using hw
      filter_upwards [he',
        Filter.eventually_all.2 hnear] with w hw hwi
      exact ⟨hw, hwi⟩
    obtain ⟨w, hw, hwD⟩ := mem_closure_iff_nhds.mp (hdense hp)
      {w | dist w p.1 < e / 2 ∧ ∀ i : Fin k, ‖a i w - a i p.1‖ < η} hevent
    have hcoeff : ∀ n : ℕ,
        ‖(adim8MonicPolynomial a w).coeff n -
          (adim8MonicPolynomial a p.1).coeff n‖ < η := by
      intro n
      by_cases hn : n < k
      · have hs : ∀ v, (∑ x : Fin k, if n = (x : ℕ) then a x v else 0) = a ⟨n, hn⟩ v := by
          intro v
          rw [Finset.sum_eq_single ⟨n, hn⟩]
          · simp
          · intro b _ hb
            rw [if_neg]
            intro hnb
            apply hb
            exact Fin.ext hnb.symm
          · simp
        simpa [adim8MonicPolynomial, coeff_add, hn, ne_of_lt hn, hs] using hw.2 ⟨n, hn⟩
      · have hzero : ∀ i : Fin k, (i : ℕ) ≠ n := fun i hin ↦ hn (hin ▸ i.isLt)
        simp [adim8MonicPolynomial, coeff_add, hn, hzero, Ne.symm, hη]
    obtain ⟨t, ht, htp⟩ := adim8_root_nearby hk
      (adim8MonicPolynomial a p.1) (adim8MonicPolynomial a w) p.2
      (adim8MonicPolynomial_monic a p.1) (adim8MonicPolynomial_monic a w)
      (adim8MonicPolynomial_natDegree a p.1) (adim8MonicPolynomial_natDegree a w)
      hz (half_pos he) (by simpa [η] using hcoeff)
    refine ⟨(w, t), ⟨hwD, ?_⟩, ?_⟩
    · simpa [← adim8MonicPolynomial_eval] using ht
    · rw [Prod.dist_eq]
      exact max_lt (by simpa [dist_comm] using hw.1.trans_le (half_le_self he.le))
        (by simpa [dist_eq_norm] using htp.trans_le (half_le_self he.le))

end HodgeLean.Foundations
