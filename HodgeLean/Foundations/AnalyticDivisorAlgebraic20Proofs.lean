import HodgeLean.Foundations.AnalyticDivisorAlgebraic20Defs
import HodgeLean.Foundations.Port.Analysis.Complex.Polynomial.FactorGrowth

/-! # Analytic divisor gluing: proof obligations

The declarations in this file isolate the analytic inputs for stage twenty.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic20

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic18
open HodgeLean.Foundations.AnalyticDivisorAlgebraic19
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic17
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7

private theorem gaga20_bounded_mul_square_derivative
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

private theorem gaga20_analytic_bounded_mul_square
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} {D c : E → ℂ} (hU : IsOpen U) (hD : AnalyticOnNhd ℂ D U)
    (hc : AnalyticOnNhd ℂ c {x ∈ U | D x ≠ 0})
    (hb : ∀ x ∈ U, ∃ C : ℝ, ∀ᶠ y in nhds x, D y ≠ 0 → ‖c y‖ ≤ C) :
    AnalyticOnNhd ℂ (fun y ↦ D y ^ 2 * c y) U := by
  apply HodgeLean.Foundations.AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn hU
  intro x hx
  by_cases hDx : D x = 0
  · exact (gaga20_bounded_mul_square_derivative (hD x hx).differentiableAt hDx
      (hb x hx)).differentiableAt.differentiableWithinAt
  · exact (((hD x hx).pow 2).mul (hc x ⟨hx, hDx⟩)).differentiableAt.differentiableWithinAt

private theorem gaga20_eventually_frequently_nonzero {n : ℕ}
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

private theorem gaga20_extend_norm_bound {n : ℕ}
    {D f g : (Fin n → ℂ) → ℂ} {p : Fin n → ℂ} {C : ℝ}
    (hD : AnalyticAt ℂ D p) (hnz : ¬ ∀ᶠ z in nhds p, D z = 0)
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hb : ∀ᶠ z in nhds p, D z ≠ 0 → ‖f z‖ ≤ C * ‖g z‖) :
    ∀ᶠ z in nhds p, ‖f z‖ ≤ C * ‖g z‖ := by
  filter_upwards [gaga20_eventually_frequently_nonzero hD hnz,
    hf.eventually_analyticAt, hg.eventually_analyticAt, hb.eventually_nhds]
      with y hy hfy hgy hby
  exact le_of_tendsto_of_tendsto_of_frequently hfy.continuousAt.norm
    (continuousAt_const.mul hgy.continuousAt.norm)
    ((hy.and_eventually hby).mono fun z hz ↦ hz.2 hz.1)

open HodgeLean.Foundations.AnalyticDivisorAlgebraic11 in
private theorem gaga20_irreducible_representative {n : ℕ} {p : Fin n → ℂ}
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
private theorem gaga20_germ_dvd_of_norm_bound {n : ℕ} {p : Fin n → ℂ}
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
      obtain ⟨i, hi, hIi, hirr⟩ := gaga20_irreducible_representative I hI
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
        apply gaga20_extend_norm_bound hi hinz hc ha
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
private theorem gaga20_analytic_division_of_norm_bound {n : ℕ} {p : Fin n → ℂ}
    {f g : (Fin n → ℂ) → ℂ} (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    {C : ℝ} (hb : ∀ᶠ z in nhds p, ‖f z‖ ≤ C * ‖g z‖) :
    ∃ q : (Fin n → ℂ) → ℂ, AnalyticAt ℂ q p ∧
      f =ᶠ[nhds p] fun z ↦ g z * q z := by
  obtain ⟨Q, hQ⟩ := gaga20_germ_dvd_of_norm_bound
    (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p) g hg rfl f hf C hb
  obtain ⟨q, hq, hqr⟩ := Q.2
  refine ⟨q, hq, Filter.Germ.coe_eq.mp ?_⟩
  have hQq : Q = (⟨Filter.Germ.ofFun q, q, hq, rfl⟩ : AnalyticGermAt n p) :=
    Subtype.ext hqr.symm
  exact congrArg Subtype.val (hQ.trans (by rw [hQq]))

private theorem gaga20_bounded_holomorphic_extension {n : ℕ}
    {U : Set (Fin n → ℂ)} {D c : (Fin n → ℂ) → ℂ}
    (hU : IsOpen U) (hD : AnalyticOnNhd ℂ D U)
    (hc : AnalyticOnNhd ℂ c {x ∈ U | D x ≠ 0})
    (hb : ∀ x ∈ U, ∃ C : ℝ, ∀ᶠ y in nhds x, D y ≠ 0 → ‖c y‖ ≤ C)
    {p : Fin n → ℂ} (hp : p ∈ U) :
    ∃ q : (Fin n → ℂ) → ℂ, AnalyticAt ℂ q p ∧
      ∀ᶠ z in nhds p, D z ≠ 0 → q z = c z := by
  have hH := gaga20_analytic_bounded_mul_square hU hD hc hb p hp
  obtain ⟨C, hC⟩ := hb p hp
  have hbound : ∀ᶠ z in nhds p, ‖D z ^ 2 * c z‖ ≤ C * ‖D z ^ 2‖ := by
    filter_upwards [hC] with z hz
    by_cases hDz : D z = 0
    · simp only [hDz, zero_pow (by decide : 2 ≠ 0), zero_mul, norm_zero, mul_zero, le_refl]
    · rw [norm_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hz hDz) (norm_nonneg _)
  obtain ⟨q, hq, heq⟩ := gaga20_analytic_division_of_norm_bound hH ((hD p hp).pow 2) hbound
  refine ⟨q, hq, heq.mono fun z hz hDz ↦ ?_⟩
  exact (mul_left_cancel₀ (pow_ne_zero 2 hDz) hz).symm

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5 in
private theorem gaga20_monic_factor_coeff_bounded {n d : ℕ}
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

private theorem gaga20_bounded_holomorphic_extension_on {n : ℕ}
    {U : Set (Fin n → ℂ)} {D c : (Fin n → ℂ) → ℂ}
    (hU : IsOpen U) (hD : AnalyticOnNhd ℂ D U)
    (hnz : ∀ x ∈ U, ¬ ∀ᶠ y in nhds x, D y = 0)
    (hc : AnalyticOnNhd ℂ c {x ∈ U | D x ≠ 0})
    (hb : ∀ x ∈ U, ∃ C : ℝ, ∀ᶠ y in nhds x, D y ≠ 0 → ‖c y‖ ≤ C) :
    ∃ Q : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ Q U ∧
      ∀ x ∈ U, D x ≠ 0 → Q x = c x := by
  classical
  have hlocal := fun x : U ↦ gaga20_bounded_holomorphic_extension hU hD hc hb x.property
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

private theorem gaga20_clopen_membership_near {E : Type*} [TopologicalSpace E]
    {T S : Set E} (hS : IsClopen (((↑) : T → E) ⁻¹' S)) {x : E} (hx : x ∈ T) :
    ∀ᶠ y in nhds x, y ∈ T → (y ∈ S ↔ x ∈ S) := by
  by_cases hxS : x ∈ S
  · obtain ⟨O, hO, heq⟩ := isOpen_induced_iff.mp hS.isOpen
    have hxO : x ∈ O := by
      have : (⟨x, hx⟩ : T) ∈ ((↑) : T → E) ⁻¹' S := hxS
      rwa [← heq] at this
    filter_upwards [hO.mem_nhds hxO] with y hy hyT
    have hyS : y ∈ S := by
      have : (⟨y, hyT⟩ : T) ∈ ((↑) : T → E) ⁻¹' O := hy
      rwa [heq] at this
    exact ⟨fun _ ↦ hxS, fun _ ↦ hyS⟩
  · obtain ⟨O, hO, heq⟩ := isOpen_induced_iff.mp hS.compl.isOpen
    have hxO : x ∈ O := by
      have : (⟨x, hx⟩ : T) ∈ (((↑) : T → E) ⁻¹' S)ᶜ := hxS
      rwa [← heq] at this
    filter_upwards [hO.mem_nhds hxO] with y hy hyT
    have hyS : y ∉ S := by
      have : (⟨y, hyT⟩ : T) ∈ ((↑) : T → E) ⁻¹' O := hy
      rwa [heq] at this
    exact ⟨fun h ↦ (hyS h).elim, fun h ↦ (hxS h).elim⟩

private theorem gaga20_analytic_coeff_root_product {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {p : E}
    (s : Finset ι) {r : ι → E → ℂ} (hr : ∀ i ∈ s, AnalyticAt ℂ (r i) p) (k : ℕ) :
    AnalyticAt ℂ (fun z ↦ (∏ i ∈ s, (Polynomial.X - Polynomial.C (r i z))).coeff k) p := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => simpa only [Finset.prod_empty] using analyticAt_const
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi, Polynomial.coeff_mul]
      apply Finset.analyticAt_fun_sum
      intro j hj
      apply AnalyticAt.mul _ (ih (fun l hl ↦ hr l (Finset.mem_insert_of_mem hl)) j.2)
      have hri := hr i (Finset.mem_insert_self i s)
      cases j.1 with
      | zero => simpa only [Polynomial.coeff_sub, Polynomial.coeff_X_zero,
          Polynomial.coeff_C_zero, zero_sub] using! hri.neg
      | succ l =>
          simp only [Polynomial.coeff_sub, Polynomial.coeff_C_succ, sub_zero]
          exact analyticAt_const

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5 in
private def gaga20_selectedFactor {n d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ)
    (S : Set ((Fin n → ℂ) × ℂ)) (z : Fin n → ℂ) : Polynomial ℂ := by
  classical
  exact (((monicPoly a z).roots.filter fun w ↦ (z, w) ∈ S).map
    fun w ↦ Polynomial.X - Polynomial.C w).prod

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5 in
private theorem gaga20_selectedFactor_monic_dvd {n d : ℕ}
    (a : Fin d → (Fin n → ℂ) → ℂ) (S : Set ((Fin n → ℂ) × ℂ)) (z : Fin n → ℂ) :
    (gaga20_selectedFactor a S z).Monic ∧ gaga20_selectedFactor a S z ∣ monicPoly a z := by
  classical
  constructor
  · exact Polynomial.monic_multisetProd_X_sub_C _
  · exact (Multiset.prod_dvd_prod_of_le
      (Multiset.map_le_map (Multiset.filter_le _ _))).trans
        (monicPoly a z).prod_multiset_X_sub_C_dvd

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
  HodgeLean.Foundations.AnalyticDivisorAlgebraic4 in
private theorem gaga20_analytic_selectedFactor_coeff {n d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    {S : Set ((Fin n → ℂ) × ℂ)} (hU : IsOpen U)
    (hS : IsClopen (((↑) : {y : (Fin n → ℂ) × ℂ |
      y.1 ∈ U ∧ weierstrassDiscr a y.1 ≠ 0 ∧ monicInLast a y = 0} →
        (Fin n → ℂ) × ℂ) ⁻¹' S))
    {p : Fin n → ℂ} (hp : p ∈ U) (ha : ∀ j, AnalyticAt ℂ (a j) p)
    (hD : weierstrassDiscr a p ≠ 0) (k : ℕ) :
    AnalyticAt ℂ (fun z ↦ (gaga20_selectedFactor a S z).coeff k) p := by
  classical
  obtain ⟨φ, hφ, hgraphs⟩ := spec_exists_root_graphs ha hD
  have hroots : ∀ᶠ z in nhds p, ∀ i, monicInLast a (z, φ i z) = 0 := by
    filter_upwards [hgraphs] with z hz i
    rw [hz.1]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  have hstable : ∀ᶠ z in nhds p, ∀ i, (z, φ i z) ∈ S ↔ (p, φ i p) ∈ S := by
    apply eventually_all.mpr
    intro i
    have hγ : ContinuousAt (fun z ↦ (z, φ i z)) p :=
      continuousAt_id.prodMk (hφ i).continuousAt
    have hmem := gaga20_clopen_membership_near hS
      (x := (p, φ i p)) ⟨hp, hD, hroots.self_of_nhds i⟩
    filter_upwards [hγ.eventually hmem, hroots, hU.mem_nhds hp,
      (spec_analyticAt_weierstrassDiscr ha).continuousAt.eventually_ne hD]
        with z hz hzroot hzU hzD
    exact hz ⟨hzU, hzD, hzroot i⟩
  let I : Finset (Fin d) := Finset.univ.filter fun i ↦ (p, φ i p) ∈ S
  apply (gaga20_analytic_coeff_root_product I (fun i _ ↦ hφ i) k).congr
  filter_upwards [hgraphs, hstable] with z hz hzs
  have hpoly : monicPoly a z = ∏ i : Fin d, (Polynomial.X - Polynomial.C (φ i z)) := by
    apply Polynomial.funext
    intro w
    rw [(spec_monicPoly a z).2.2, hz.1]
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hr : (monicPoly a z).roots = Finset.univ.val.map (fun i : Fin d ↦ φ i z) := by
    rw [hpoly, Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
    · rw [← hpoly]
      exact (spec_monicPoly a z).1.ne_zero
  have hfilter : Finset.univ.val.filter (fun i : Fin d ↦ (z, φ i z) ∈ S) = I.val := by
    apply Multiset.filter_congr
    intro i _
    exact hzs i
  have hfactor : gaga20_selectedFactor a S z =
      ∏ i ∈ I, (Polynomial.X - Polynomial.C (φ i z)) := by
    unfold gaga20_selectedFactor
    rw [hr, Multiset.filter_map]
    change (((Finset.univ.val.filter fun i : Fin d ↦ (z, φ i z) ∈ S).map
      (fun i ↦ φ i z)).map (fun w ↦ Polynomial.X - Polynomial.C w)).prod = _
    rw [hfilter, Multiset.map_map]
    rfl
  rw [hfactor]

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
  HodgeLean.Foundations.AnalyticDivisorAlgebraic4 in
private theorem gaga20_selectedFactor_coeff_extension {n d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    {S : Set ((Fin n → ℂ) × ℂ)} (hU : IsOpen U)
    (ha : ∀ j, AnalyticOnNhd ℂ (a j) U)
    (hnz : ∀ x ∈ U, ¬ ∀ᶠ y in nhds x, weierstrassDiscr a y = 0)
    (hS : IsClopen (((↑) : {y : (Fin n → ℂ) × ℂ |
      y.1 ∈ U ∧ weierstrassDiscr a y.1 ≠ 0 ∧ monicInLast a y = 0} →
        (Fin n → ℂ) × ℂ) ⁻¹' S)) (k : ℕ) :
    ∃ b : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ b U ∧
      ∀ z ∈ U, weierstrassDiscr a z ≠ 0 → b z = (gaga20_selectedFactor a S z).coeff k := by
  apply gaga20_bounded_holomorphic_extension_on hU
    (fun z hz ↦ spec_analyticAt_weierstrassDiscr (fun j ↦ ha j z hz)) hnz
  · intro z hz
    exact gaga20_analytic_selectedFactor_coeff hU hS hz.1 (fun j ↦ ha j z hz.1) hz.2 k
  · intro z hz
    obtain ⟨C, hC⟩ := gaga20_monic_factor_coeff_bounded (fun j ↦ ha j z hz)
    refine ⟨C, hC.mono fun y hy _ ↦ ?_⟩
    exact hy _ (gaga20_selectedFactor_monic_dvd a S y).1
      (gaga20_selectedFactor_monic_dvd a S y).2 k

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5 in
private theorem gaga20_selectedFactor_mul_compl {n d : ℕ}
    (a : Fin d → (Fin n → ℂ) → ℂ) (S : Set ((Fin n → ℂ) × ℂ)) (z : Fin n → ℂ) :
    gaga20_selectedFactor a S z * gaga20_selectedFactor a Sᶜ z = monicPoly a z := by
  classical
  unfold gaga20_selectedFactor
  simp only [Set.mem_compl_iff]
  rw [← Multiset.prod_add, ← Multiset.map_add, Multiset.filter_add_not]
  exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    (spec_monicPoly a z).1 (IsAlgClosed.splits (monicPoly a z)).natDegree_eq_card_roots.symm

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
  HodgeLean.Foundations.AnalyticDivisorAlgebraic4 in
private theorem gaga20_selectedFactor_analytic_extension {n d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    {S : Set ((Fin n → ℂ) × ℂ)} (hU : IsOpen U)
    (ha : ∀ j, AnalyticOnNhd ℂ (a j) U)
    (hnz : ∀ x ∈ U, ¬ ∀ᶠ y in nhds x, weierstrassDiscr a y = 0)
    (hS : IsClopen (((↑) : {y : (Fin n → ℂ) × ℂ |
      y.1 ∈ U ∧ weierstrassDiscr a y.1 ≠ 0 ∧ monicInLast a y = 0} →
        (Fin n → ℂ) × ℂ) ⁻¹' S)) :
    ∃ Q : (Fin n → ℂ) × ℂ → ℂ,
      AnalyticOnNhd ℂ Q (U ×ˢ Set.univ) ∧
      ∀ z ∈ U, weierstrassDiscr a z ≠ 0 →
        ∀ w, Q (z, w) = (gaga20_selectedFactor a S z).eval w := by
  choose b hb hbeq using fun k : Fin (d + 1) ↦
    gaga20_selectedFactor_coeff_extension hU ha hnz hS k.val
  let Q : (Fin n → ℂ) × ℂ → ℂ := fun y ↦ ∑ k : Fin (d + 1), b k y.1 * y.2 ^ k.val
  refine ⟨Q, ?_, ?_⟩
  · intro y hy
    exact Finset.analyticAt_fun_sum _ fun k _ ↦
      ((hb k y.1 hy.1).comp analyticAt_fst).mul (analyticAt_snd.pow k.val)
  · intro z hz hDz w
    have hdeg : (gaga20_selectedFactor a S z).natDegree < d + 1 := by
      have hle := Polynomial.natDegree_le_of_dvd (gaga20_selectedFactor_monic_dvd a S z).2
        (spec_monicPoly a z).1.ne_zero
      rw [(spec_monicPoly a z).2.1] at hle
      omega
    change (∑ k : Fin (d + 1), b k z * w ^ k.val) = _
    simp_rw [hbeq _ z hz hDz]
    exact (Fin.sum_univ_eq_sum_range (fun k ↦ (gaga20_selectedFactor a S z).coeff k * w ^ k)
      (d + 1)).trans ((gaga20_selectedFactor a S z).eval_eq_sum_range' hdeg w).symm

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
  HodgeLean.Foundations.AnalyticDivisorAlgebraic4 in
private theorem gaga20_clopen_analytic_factorization {n d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    {S : Set ((Fin n → ℂ) × ℂ)} (hU : IsOpen U)
    (ha : ∀ j, AnalyticOnNhd ℂ (a j) U)
    (hnz : ∀ x ∈ U, ¬ ∀ᶠ y in nhds x, weierstrassDiscr a y = 0)
    (hS : IsClopen (((↑) : {y : (Fin n → ℂ) × ℂ |
      y.1 ∈ U ∧ weierstrassDiscr a y.1 ≠ 0 ∧ monicInLast a y = 0} →
        (Fin n → ℂ) × ℂ) ⁻¹' S)) :
    ∃ Q R : (Fin n → ℂ) × ℂ → ℂ,
      AnalyticOnNhd ℂ Q (U ×ˢ Set.univ) ∧ AnalyticOnNhd ℂ R (U ×ˢ Set.univ) ∧
      (∀ y, y.1 ∈ U → monicInLast a y = Q y * R y) ∧
      (∀ z ∈ U, weierstrassDiscr a z ≠ 0 →
        ∀ w, Q (z, w) = (gaga20_selectedFactor a S z).eval w) ∧
      (∀ z ∈ U, weierstrassDiscr a z ≠ 0 →
        ∀ w, R (z, w) = (gaga20_selectedFactor a Sᶜ z).eval w) := by
  obtain ⟨Q, hQ, hQeq⟩ := gaga20_selectedFactor_analytic_extension hU ha hnz hS
  have hSc : IsClopen (((↑) : {y : (Fin n → ℂ) × ℂ |
      y.1 ∈ U ∧ weierstrassDiscr a y.1 ≠ 0 ∧ monicInLast a y = 0} →
        (Fin n → ℂ) × ℂ) ⁻¹' Sᶜ) := by
    simpa only [Set.preimage_compl] using hS.compl
  obtain ⟨R, hR, hReq⟩ := gaga20_selectedFactor_analytic_extension hU ha hnz hSc
  refine ⟨Q, R, hQ, hR, ?_, hQeq, hReq⟩
  rintro ⟨z, w⟩ hz
  have hφ : ContinuousAt (fun x : Fin n → ℂ ↦ (x, w)) z :=
    continuousAt_id.prodMk continuousAt_const
  have hq := (hQ (z, w) ⟨hz, Set.mem_univ w⟩).continuousAt.comp (f := fun x : Fin n → ℂ ↦ (x, w)) hφ
  have hr := (hR (z, w) ⟨hz, Set.mem_univ w⟩).continuousAt.comp (f := fun x : Fin n → ℂ ↦ (x, w)) hφ
  have hw := (laneC_analyticAt_monicInLast (fun j ↦ ha j z hz) w).continuousAt.comp (f := fun x : Fin n → ℂ ↦ (x, w)) hφ
  apply tendsto_nhds_unique_of_frequently_eq hw (hq.mul hr)
  have hfreq : ∃ᶠ x in nhds z, weierstrassDiscr a x ≠ 0 :=
    Filter.not_eventually.mp (hnz z hz)
  apply (hfreq.and_eventually (hU.mem_nhds hz)).mono
  intro x hx
  change monicInLast a (x, w) = Q (x, w) * R (x, w)
  rw [hQeq x hx.2 hx.1 w, hReq x hx.2 hx.1 w, ← Polynomial.eval_mul,
    gaga20_selectedFactor_mul_compl, (spec_monicPoly a x).2.2]

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
  HodgeLean.Foundations.AnalyticDivisorAlgebraic4 in
private theorem gaga20_selectedFactor_eval_zero {n d : ℕ}
    (a : Fin d → (Fin n → ℂ) → ℂ) (S : Set ((Fin n → ℂ) × ℂ))
    {z : Fin n → ℂ} {w : ℂ} (hw : monicInLast a (z, w) = 0) (hS : (z, w) ∈ S) :
    (gaga20_selectedFactor a S z).eval w = 0 := by
  classical
  apply (Polynomial.mem_roots (gaga20_selectedFactor_monic_dvd a S z).1.ne_zero).mp
  unfold gaga20_selectedFactor
  rw [Polynomial.roots_multiset_prod_X_sub_C, Multiset.mem_filter]
  refine ⟨?_, hS⟩
  apply (Polynomial.mem_roots (spec_monicPoly a z).1.ne_zero).mpr
  change (monicPoly a z).eval w = 0
  rw [(spec_monicPoly a z).2.2, hw]

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
  HodgeLean.Foundations.AnalyticDivisorAlgebraic4 in
private theorem gaga20_selectedFactor_unit_near_origin {n d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    {S : Set ((Fin n → ℂ) × ℂ)} {Q : (Fin n → ℂ) × ℂ → ℂ}
    (hU : U ∈ nhds 0) (ha : ∀ j, ContinuousAt (a j) 0) (ha0 : ∀ j, a j 0 = 0)
    (hQ : ContinuousAt Q 0) (hQ0 : Q 0 ≠ 0)
    (heq : ∀ z ∈ U, weierstrassDiscr a z ≠ 0 →
      ∀ w, Q (z, w) = (gaga20_selectedFactor a S z).eval w) :
    ∀ᶠ z in nhds 0, weierstrassDiscr a z ≠ 0 → gaga20_selectedFactor a S z = 1 := by
  classical
  obtain ⟨V, hV, B, hB, hprod⟩ := mem_nhds_prod_iff.mp (hQ.eventually_ne hQ0)
  obtain ⟨ε, hε, hεB⟩ := Metric.mem_nhds_iff.mp hB
  have hsmall := spec_monicInLast_roots_small ha ha0 hε
  filter_upwards [hU, hV, hsmall] with z hzU hzV hzsmall hzD
  have hempty : (monicPoly a z).roots.filter (fun w ↦ (z, w) ∈ S) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro w hw hwS
    have hwzero : monicInLast a (z, w) = 0 := by
      rw [← (spec_monicPoly a z).2.2]
      exact (Polynomial.mem_roots (spec_monicPoly a z).1.ne_zero).mp hw
    have hwB : w ∈ B := hεB (by simpa only [Metric.mem_ball, dist_zero_right] using hzsmall w hwzero)
    have hQzw : Q (z, w) ≠ 0 := hprod ⟨hzV, hwB⟩
    apply hQzw
    rw [heq z hzU hzD w]
    exact gaga20_selectedFactor_eval_zero a S hwzero hwS
  unfold gaga20_selectedFactor
  rw [hempty, Multiset.map_zero, Multiset.prod_zero]

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
  HodgeLean.Foundations.AnalyticDivisorAlgebraic4 in
private theorem gaga20_unit_selected_empty {n d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    {S : Set ((Fin n → ℂ) × ℂ)} {Q : (Fin n → ℂ) × ℂ → ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (h0 : 0 ∈ U)
    (ha : ∀ j, AnalyticOnNhd ℂ (a j) U) (ha0 : ∀ j, a j 0 = 0)
    (hnz : ¬ ∀ᶠ y in nhds 0, weierstrassDiscr a y = 0)
    (hQ : AnalyticOnNhd ℂ Q (U ×ˢ Set.univ)) (hQ0 : Q 0 ≠ 0)
    (heq : ∀ z ∈ U, weierstrassDiscr a z ≠ 0 →
      ∀ w, Q (z, w) = (gaga20_selectedFactor a S z).eval w) :
    ∀ z ∈ U, weierstrassDiscr a z ≠ 0 →
      ∀ w, monicInLast a (z, w) = 0 → (z, w) ∉ S := by
  have hnear := gaga20_selectedFactor_unit_near_origin (hU.mem_nhds h0)
    (fun j ↦ (ha j 0 h0).continuousAt) ha0 (hQ 0 ⟨h0, Set.mem_univ _⟩).continuousAt hQ0 heq
  have hQone : ∀ w, ∀ z ∈ U, Q (z, w) = 1 := by
    intro w
    have hQw : AnalyticOnNhd ℂ (fun z ↦ Q (z, w)) U := by
      intro z hz
      exact (hQ (z, w) ⟨hz, Set.mem_univ w⟩).comp
        (f := fun x : Fin n → ℂ ↦ (x, w)) (analyticAt_id.prod analyticAt_const)
    have hnorm : ∀ᶠ z in nhds 0, ‖Q (z, w) - 1‖ ≤ (0 : ℝ) * ‖(0 : ℂ)‖ := by
      apply gaga20_extend_norm_bound
        (spec_analyticAt_weierstrassDiscr (fun j ↦ ha j 0 h0)) hnz
        ((hQw 0 h0).sub analyticAt_const) analyticAt_const
      filter_upwards [hnear, hU.mem_nhds h0] with z hz hzU hzD
      change ‖Q (z, w) - 1‖ ≤ 0 * ‖(0 : ℂ)‖
      rw [heq z hzU hzD w, hz hzD, Polynomial.eval_one, sub_self, norm_zero, mul_zero]
    have hevent : (fun z ↦ Q (z, w)) =ᶠ[nhds 0] fun _ ↦ (1 : ℂ) := by
      filter_upwards [hnorm] with z hz
      have : ‖Q (z, w) - 1‖ ≤ 0 := by simpa only [zero_mul] using hz
      exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
    exact hQw.eqOn_of_preconnected_of_eventuallyEq (fun _ _ ↦ analyticAt_const) hconn h0 hevent
  intro z hz hzD w hw hwS
  have hzero := gaga20_selectedFactor_eval_zero a S hw hwS
  rw [← heq z hz hzD w, hQone w z hz] at hzero
  exact one_ne_zero hzero

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
  HodgeLean.Foundations.AnalyticDivisorAlgebraic4 in
private theorem gaga20_preconnected_simple_root_cover {n d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (h0 : 0 ∈ U)
    (ha : ∀ j, AnalyticOnNhd ℂ (a j) U) (ha0 : ∀ j, a j 0 = 0)
    (hnz : ∀ x ∈ U, ¬ ∀ᶠ y in nhds x, weierstrassDiscr a y = 0)
    (hirr : IsIrreducibleAt (monicInLast a) 0) :
    IsPreconnected {y : (Fin n → ℂ) × ℂ |
      y.1 ∈ U ∧ weierstrassDiscr a y.1 ≠ 0 ∧ monicInLast a y = 0} := by
  let T : Set ((Fin n → ℂ) × ℂ) := {y |
    y.1 ∈ U ∧ weierstrassDiscr a y.1 ≠ 0 ∧ monicInLast a y = 0}
  apply isPreconnected_iff_preconnectedSpace.mpr
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  let S : Set ((Fin n → ℂ) × ℂ) := ((↑) : T → _) '' s
  have hSs : ((↑) : T → _) ⁻¹' S = s := Set.preimage_image_eq s Subtype.val_injective
  have hS : IsClopen (((↑) : T → _) ⁻¹' S) := hSs.symm ▸ hs
  obtain ⟨Q, R, hQ, hR, hfac, hQeq, hReq⟩ := gaga20_clopen_analytic_factorization hU ha hnz hS
  have hfac0 : monicInLast a =ᶠ[nhds 0] fun y ↦ Q y * R y := by
    have hbase : ∀ᶠ y : (Fin n → ℂ) × ℂ in nhds 0, y.1 ∈ U :=
      continuous_fst.continuousAt (hU.mem_nhds h0)
    exact hbase.mono fun y hy ↦ hfac y hy
  rcases hirr.2 Q R (hQ 0 ⟨h0, Set.mem_univ _⟩) (hR 0 ⟨h0, Set.mem_univ _⟩)
    hfac0 with hQu | hRu
  · left
    have hempty := gaga20_unit_selected_empty hU hconn h0 ha ha0 (hnz 0 h0) hQ hQu hQeq
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hempty x.val.1 x.property.1 x.property.2.1 x.val.2 x.property.2.2
      ⟨x, hx, rfl⟩
  · right
    have hempty := gaga20_unit_selected_empty hU hconn h0 ha ha0 (hnz 0 h0) hR hRu hReq
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    have hxS : x.val ∉ S := by
      intro h
      exact hx (show x ∈ s from hSs ▸ h)
    exact hempty x.val.1 x.property.1 x.property.2.1 x.val.2 x.property.2.2 hxS

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
  HodgeLean.Foundations.AnalyticDivisorAlgebraic4 in
private theorem gaga20_connected_simple_root_cover {n d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)} (hd : 0 < d)
    (hU : IsOpen U) (hconn : IsPreconnected U) (h0 : 0 ∈ U)
    (ha : ∀ j, AnalyticOnNhd ℂ (a j) U) (ha0 : ∀ j, a j 0 = 0)
    (hnz : ∀ x ∈ U, ¬ ∀ᶠ y in nhds x, weierstrassDiscr a y = 0)
    (hirr : IsIrreducibleAt (monicInLast a) 0) :
    IsConnected {y : (Fin n → ℂ) × ℂ |
      y.1 ∈ U ∧ weierstrassDiscr a y.1 ≠ 0 ∧ monicInLast a y = 0} := by
  refine ⟨?_, gaga20_preconnected_simple_root_cover hU hconn h0 ha ha0 hnz hirr⟩
  have hfreq : ∃ᶠ z in nhds 0, weierstrassDiscr a z ≠ 0 :=
    Filter.not_eventually.mp (hnz 0 h0)
  obtain ⟨z, hzD, hzU⟩ := (hfreq.and_eventually (hU.mem_nhds h0)).exists
  have hcard : (monicPoly a z).roots.card = d :=
    (IsAlgClosed.splits (monicPoly a z)).natDegree_eq_card_roots.symm.trans
      (spec_monicPoly a z).2.1
  have hne : (monicPoly a z).roots ≠ 0 := by
    intro h
    rw [h, Multiset.card_zero] at hcard
    omega
  obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hne
  refine ⟨(z, w), hzU, hzD, ?_⟩
  rw [← (spec_monicPoly a z).2.2]
  exact (Polynomial.mem_roots (spec_monicPoly a z).1.ne_zero).mp hw

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
  HodgeLean.Foundations.AnalyticDivisorAlgebraic4 in
private theorem gaga20_root_mem_closure_over_base {n d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} {B : Set (Fin n → ℂ)}
    {z : Fin n → ℂ} {w : ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) z)
    (hz : z ∈ closure B) (hw : monicInLast a (z, w) = 0) :
    (z, w) ∈ closure {y : (Fin n → ℂ) × ℂ | y.1 ∈ B ∧ monicInLast a y = 0} := by
  rw [Metric.mem_closure_iff] at hz ⊢
  intro ε hε
  obtain ⟨m, hm⟩ := laneC_order_monicInLast_natCast a z w
  have hm0 : m ≠ 0 := by
    intro h
    have horder := analyticOrderAt_ne_zero.mpr
      ⟨(laneC_analyticAt_monicInLast ha w).comp₂ analyticAt_const analyticAt_id, hw⟩
    exact horder (hm.trans (by rw [h]; rfl))
  obtain ⟨r, hr, hrε, δ, hδ, -, -, hcount⟩ :=
    spec_exists_zeroCount_eq_order (laneC_analyticAt_monicInLast ha w) hm hε
  obtain ⟨z', hzB, hzz'⟩ := hz (min δ ε) (lt_min hδ hε)
  have hball : z' ∈ Metric.ball z δ := by
    rw [Metric.mem_ball, dist_comm]
    exact hzz'.trans_le (min_le_left _ _)
  have hc := hcount z' hball
  obtain ⟨w', hw', hw'0⟩ : ∃ w' ∈ Metric.ball w r,
      analyticOrderNatAt (fun v ↦ monicInLast a (z', v)) w' ≠ 0 := by
    apply exists_ne_zero_of_finsum_mem_ne_zero
    rw [← zeroCount, hc]
    exact hm0
  refine ⟨(z', w'), ⟨hzB, apply_eq_zero_of_analyticOrderNatAt_ne_zero
    (f := fun v ↦ monicInLast a (z', v)) hw'0⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨hzz'.trans_le (min_le_right _ _), by
    rw [dist_comm]
    exact (Metric.mem_ball.mp hw').trans hrε⟩

private theorem gaga20_closure_nonzero_inter {n : ℕ}
    {U : Set (Fin n → ℂ)} {D : (Fin n → ℂ) → ℂ} (hU : IsOpen U)
    (hnz : ∀ x ∈ U, ¬ ∀ᶠ y in nhds x, D y = 0) :
    closure {z ∈ U | D z ≠ 0} = closure U := by
  apply subset_antisymm (closure_mono fun _ h ↦ h.1)
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply mem_closure_iff_frequently.mpr
  have hf : ∃ᶠ y in nhds x, D y ≠ 0 := Filter.not_eventually.mp (hnz x hx)
  exact (hf.and_eventually (hU.mem_nhds hx)).mono fun _ h ↦ ⟨h.2, h.1⟩

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
  HodgeLean.Foundations.AnalyticDivisorAlgebraic4 in
private theorem gaga20_regular_of_preparation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {n d : ℕ}
    {f : E → ℂ} {H : (Fin n → ℂ) × ℂ → E} {u : (Fin n → ℂ) × ℂ → ℂ}
    {a : Fin d → (Fin n → ℂ) → ℂ} {y : (Fin n → ℂ) × ℂ}
    (hf : AnalyticAt ℂ f (H y)) (hH : AnalyticAt ℂ H y) (hu : AnalyticAt ℂ u y)
    (hu0 : u y ≠ 0)
    (hfac : (fun z ↦ f (H z)) =ᶠ[nhds y] fun z ↦ u z * monicInLast a z)
    (hy : monicInLast a y = 0) (hD : weierstrassDiscr a y.1 ≠ 0) :
    H y ∈ gaga20_regularZero f := by
  refine ⟨hfac.self_of_nhds.trans (by change u y * monicInLast a y = 0; rw [hy, mul_zero]), ?_⟩
  have hline : HasDerivAt (fun w : ℂ ↦ (y.1, w)) (0, 1) y.2 :=
    (hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2)
  have hPw : AnalyticAt ℂ (fun w ↦ monicInLast a (y.1, w)) y.2 := by
    rw [gaga5b_monicInLast_slice_eq]
    exact (Polynomial.differentiable _).analyticAt _
  have horder0 := analyticOrderAt_ne_zero.mpr ⟨hPw, hy⟩
  have horderle := (spec_weierstrassDiscr_ne_zero_iff a y.1).mp hD y.2
  have horder : analyticOrderAt (fun w ↦ monicInLast a (y.1, w)) y.2 = 1 := by
    exact le_antisymm horderle (Order.one_le_iff_ne_zero.mpr horder0)
  have hpd := laneC_deriv_ne_zero_of_order_one hPw horder
  intro hfd
  have hF : HasFDerivAt (fun z ↦ f (H z)) (0 : ((Fin n → ℂ) × ℂ) →L[ℂ] ℂ) y := by
    simpa only [hfd, ContinuousLinearMap.zero_comp, Function.comp_def] using
      hf.differentiableAt.hasFDerivAt.comp y hH.differentiableAt.hasFDerivAt
  have hG : HasFDerivAt (fun z ↦ u z * monicInLast a z) (0 : ((Fin n → ℂ) × ℂ) →L[ℂ] ℂ) y :=
    hF.congr_of_eventuallyEq hfac.symm
  have hz := hG.comp_hasDerivAt y.2 hline
  have hprod := ((hu.differentiableAt.comp y.2 hline.differentiableAt).hasDerivAt).mul
    hPw.differentiableAt.hasDerivAt
  have he := hz.unique hprod
  change 0 = deriv (fun w ↦ u (y.1, w)) y.2 * monicInLast a y +
    u y * deriv (fun w ↦ monicInLast a (y.1, w)) y.2 at he
  rw [hy, mul_zero, zero_add] at he
  exact hpd ((mul_eq_zero.mp he.symm).resolve_left hu0)

private theorem gaga20_regular_shrinking_of_cover {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {C W : Set E}
    (hC : IsConnected C) (hCW : C ⊆ gaga20_regularZero f ∩ W)
    (hf : ∀ x ∈ closure W, ContinuousAt f x)
    (hdense : {x | f x = 0} ∩ closure W ⊆ closure C) :
    closure (gaga20_regularZero f ∩ W) = {x | f x = 0} ∩ closure W ∧
      IsConnected (gaga20_regularZero f ∩ W) := by
  have hclW : closure (gaga20_regularZero f ∩ W) ⊆ closure W := closure_mono inter_subset_right
  have hclzero : closure (gaga20_regularZero f ∩ W) ⊆ {x | f x = 0} ∩ closure W := by
    intro x hx
    refine ⟨?_, hclW hx⟩
    exact tendsto_nhds_unique_of_frequently_eq (hf x (hclW hx)) tendsto_const_nhds
      ((mem_closure_iff_frequently.mp hx).mono fun y hy ↦ hy.1.1)
  refine ⟨subset_antisymm hclzero (hdense.trans (closure_mono hCW)), ?_⟩
  exact hC.subset_closure hCW fun x hx ↦ hdense ⟨hx.1.1, subset_closure hx.2⟩

open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
  HodgeLean.Foundations.AnalyticDivisorAlgebraic5 in
theorem gaga20_regular_locus_aux {n : ℕ} (p : Fin n → ℂ) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f p) (hf0 : f p = 0) (hirr : IsIrreducibleAt f p) :
    ∃ W ∈ nhds p, IsOpen W ∧ p ∈ W ∧
      closure (gaga20_regularZero f ∩ W) = {x | f x = 0} ∩ closure W ∧
      IsConnected (gaga20_regularZero f ∩ W) := by
  obtain ⟨m, L, d, hd, u, hu, hu0, a, ha, _, hi, hfac⟩ :=
    gaga18_prepare n p f hf ⟨hf0, hirr.2⟩
  let H : ((Fin m → ℂ) × ℂ) ≃ₜ (Fin n → ℂ) :=
    L.symm.toHomeomorph.trans (Homeomorph.addLeft p)
  have hH0 : H 0 = p := by
    change p + L.symm 0 = p
    rw [map_zero, add_zero]
  have hHan : ∀ y, AnalyticAt ℂ H y := fun y ↦
    analyticAt_const.add (L.symm.toContinuousLinearMap.analyticAt y)
  have hHt : Tendsto H (nhds 0) (nhds p) := by
    simpa only [hH0] using H.continuous.tendsto 0
  have hfa : ∀ᶠ y in nhds (0 : (Fin m → ℂ) × ℂ), AnalyticAt ℂ f (H y) :=
    hHt.eventually hf.eventually_analyticAt
  have hcoeff : ∀ᶠ y in nhds (0 : (Fin m → ℂ) × ℂ), ∀ j, AnalyticAt ℂ (a j) y.1 :=
    continuous_fst.continuousAt (eventually_all.mpr fun j ↦ (ha j).1.eventually_analyticAt)
  have hfacH : (fun y ↦ f (H y)) =ᶠ[nhds 0] fun y ↦ u y * monicInLast a y := hfac
  obtain ⟨ε, hε, hdata⟩ := Metric.eventually_nhds_iff_ball.mp
    (hfa.and (hu.eventually_analyticAt.and ((hu.continuousAt.eventually_ne hu0).and
      (hcoeff.and hfacH.eventually_nhds))))
  let R : ℝ := ε / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRε : R < ε := by dsimp [R]; linarith
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff_ball.mp
    (spec_monicInLast_roots_small (fun j ↦ (ha j).1.continuousAt) (fun j ↦ (ha j).2) hR)
  let r : ℝ := min δ ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := by dsimp [r]; have := min_le_left δ ε; linarith
  have hrε : r < ε := by dsimp [r]; have := min_le_right δ ε; linarith
  let U : Set (Fin m → ℂ) := Metric.ball 0 r
  let V : Set ((Fin m → ℂ) × ℂ) := U ×ˢ Metric.ball 0 R
  have hU : IsOpen U := Metric.isOpen_ball
  have h0U : (0 : Fin m → ℂ) ∈ U := Metric.mem_ball_self hr
  have hV : IsOpen V := hU.prod Metric.isOpen_ball
  have h0V : (0 : (Fin m → ℂ) × ℂ) ∈ V := ⟨h0U, Metric.mem_ball_self hR⟩
  have hclU : closure U = Metric.closedBall 0 r := closure_ball 0 hr.ne'
  have hclV : closure V = Metric.closedBall 0 r ×ˢ Metric.closedBall 0 R := by
    change closure (U ×ˢ Metric.ball 0 R) = _
    rw [closure_prod_eq, hclU, closure_ball 0 hR.ne']
  have hVsmall : closure V ⊆ Metric.ball 0 ε := by
    intro y hy
    rw [hclV] at hy
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff]
    exact ⟨(by simpa only [Metric.mem_closedBall, dist_zero_right] using hy.1 : ‖y.1‖ ≤ r).trans_lt hrε,
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy.2 : ‖y.2‖ ≤ R).trans_lt hRε⟩
  have hbase_data : ∀ z ∈ closure U, ∀ j, AnalyticAt ℂ (a j) z := by
    intro z hz
    apply (hdata (z, 0) (hVsmall ?_)).2.2.2.1
    rw [hclV]
    exact ⟨hclU ▸ hz, by simpa only [Metric.mem_closedBall, dist_self] using hR.le⟩
  have hsmall_cl : ∀ z ∈ closure U, ∀ w, monicInLast a (z, w) = 0 → ‖w‖ < R := by
    intro z hz
    apply hsmall z
    rw [hclU, Metric.mem_closedBall, dist_zero_right] at hz
    simpa only [Metric.mem_ball, dist_zero_right] using hz.trans_lt hrδ
  have hΔ := gaga18_discriminant m d a hd ha hi
  have hΔg : @Filter.Germ.ofFun (Fin m → ℂ) ℂ (nhds 0) (weierstrassDiscr a) ≠ 0 := by
    intro h
    exact hΔ (Filter.Germ.coe_eq.mp h)
  have hnz : ∀ z ∈ U, ¬ ∀ᶠ x in nhds z, weierstrassDiscr a x = 0 := by
    intro z hz he
    have hzg := HodgeLean.Foundations.AnalyticDivisorAlgebraic12.spec_germ_ne_zero_of_preconnected
      (weierstrassDiscr a) U hU (convex_ball 0 r).isPreconnected
      (fun x hx ↦ spec_analyticAt_weierstrassDiscr (hbase_data x (subset_closure hx)))
      0 z h0U hz hΔg
    exact hzg (Filter.Germ.coe_eq.mpr he)
  let T : Set ((Fin m → ℂ) × ℂ) := {y |
    y.1 ∈ U ∧ weierstrassDiscr a y.1 ≠ 0 ∧ monicInLast a y = 0}
  have hT : IsConnected T := gaga20_connected_simple_root_cover hd hU
    (convex_ball 0 r).isPreconnected h0U
    (fun j z hz ↦ hbase_data z (subset_closure hz) j) (fun j ↦ (ha j).2) hnz hi
  have hTV : T ⊆ V := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    simpa only [Metric.mem_ball, dist_zero_right] using
      (hsmall_cl y.1 (subset_closure hy.1) y.2 hy.2.2)
  let W : Set (Fin n → ℂ) := H '' V
  have hWo : IsOpen W := H.isOpenMap V hV
  have hpW : p ∈ W := ⟨0, h0V, hH0⟩
  refine ⟨W, hWo.mem_nhds hpW, hWo, hpW, ?_⟩
  apply gaga20_regular_shrinking_of_cover (hT.image H H.continuous.continuousOn)
  · rintro x ⟨y, hy, rfl⟩
    have hyV := hTV hy
    have hdy := hdata y (hVsmall (subset_closure hyV))
    exact ⟨gaga20_regular_of_preparation hdy.1 (hHan y) hdy.2.1 hdy.2.2.1
      hdy.2.2.2.2 hy.2.2 hy.2.1, ⟨y, hyV, rfl⟩⟩
  · intro x hx
    change x ∈ closure (H '' V) at hx
    rw [← H.image_closure] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (hdata y (hVsmall hy)).1.continuousAt
  · rintro x ⟨hxzero, hxW⟩
    change x ∈ closure (H '' V) at hxW
    rw [← H.image_closure] at hxW
    obtain ⟨y, hy, rfl⟩ := hxW
    have hdy := hdata y (hVsmall hy)
    have hyeq : f (H y) = u y * monicInLast a y := hdy.2.2.2.2.self_of_nhds
    have hyzero : monicInLast a y = 0 :=
      (mul_eq_zero.mp (hyeq.symm.trans hxzero)).resolve_left hdy.2.2.1
    have hybase : y.1 ∈ closure U := by
      rw [hclU]
      exact (hclV ▸ hy).1
    have hycl : y ∈ closure T := by
      have hb : y.1 ∈ closure {z ∈ U | weierstrassDiscr a z ≠ 0} := by
        rw [gaga20_closure_nonzero_inter hU hnz]
        exact hybase
      have hc := gaga20_root_mem_closure_over_base (hbase_data y.1 hybase) hb hyzero
      exact closure_mono (t := T) (fun v hv ↦ ⟨hv.1.1, hv.1.2, hv.2⟩) hc
    exact mem_closure_image H.continuous.continuousAt hycl


private theorem regular_graph_chart {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {P : E → ℂ}
    (hU : IsOpen U) (hP : AnalyticOnNhd ℂ P U) {x : E}
    (hx : x ∈ gaga20_regularZero P ∩ U) :
    ∃ (g : LinearMap.ker (fderiv ℂ P x : E →ₗ[ℂ] ℂ) → E)
      (k : E → LinearMap.ker (fderiv ℂ P x : E →ₗ[ℂ] ℂ)) (r : ℝ),
      0 < r ∧ g 0 = x ∧ Continuous k ∧ k x = 0 ∧
      AnalyticOnNhd ℂ g (Metric.ball 0 r) ∧
      MapsTo g (Metric.ball 0 r) (gaga20_regularZero P ∩ U) ∧
      ∀ᶠ y in nhds x, k y ∈ Metric.ball 0 r ∧
        (y ∈ gaga20_regularZero P ∩ U → g (k y) = y) := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, fderiv ℂ P x v ≠ 0 := by
    by_contra hn
    apply hx.1.2
    ext v
    simpa only [zero_apply] using not_exists_not.mp hn v
  obtain ⟨e, he⟩ := AnalyticDivisorAlgebraic3.spec_exists_prodKerEquiv (fderiv ℂ P x) hv
  obtain ⟨ψ, hψ, hψ0, hgraph⟩ :=
    AnalyticDivisorAlgebraic3.spec_exists_analytic_graph (hP x hx.2) hx.1.1 hv
  let K := LinearMap.ker (fderiv ℂ P x : E →ₗ[ℂ] ℂ)
  let g : K → E := fun t ↦ x + (t : E) + ψ t • v
  let k : E → K := fun y ↦ (e.symm (y - x)).1
  have hg0 : g 0 = x := by simp [g, hψ0]
  have hk : Continuous k := continuous_fst.comp (e.symm.continuous.comp (continuous_id.sub continuous_const))
  have hk0 : k x = 0 := by simp [k]
  have hga : AnalyticAt ℂ g 0 :=
    (analyticAt_const.add (K.subtypeL.analyticAt 0)).add (hψ.smul analyticAt_const)
  have hpair : Tendsto (fun t : K ↦ (t, ψ t)) (nhds 0) (nhds 0) := by
    simpa only [ContinuousAt, id_eq, hψ0, Prod.mk_zero_zero] using continuousAt_id.prodMk hψ.continuousAt
  have hgt : Tendsto g (nhds 0) (nhds x) := by
    simpa only [ContinuousAt, hg0] using hga.continuousAt
  have hreg : ∀ᶠ y in nhds x, fderiv ℂ P y ≠ 0 :=
    (hP x hx.2).fderiv.continuousAt.eventually_ne hx.1.2
  have hgood : ∀ᶠ t in nhds (0 : K),
      AnalyticAt ℂ g t ∧ g t ∈ gaga20_regularZero P ∩ U := by
    filter_upwards [hga.eventually_analyticAt, hpair.eventually hgraph,
      hgt.eventually hreg,
      hgt.eventually (hU.mem_nhds hx.2)] with t ha hz hr hu
    exact ⟨ha, ⟨(hz.mpr rfl), hr⟩, hu⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨g, k, r, hr, hg0, hk, hk0, fun t ht ↦ (hball ht).1,
    fun t ht ↦ (hball ht).2, ?_⟩
  have hevent : Tendsto (fun y ↦ e.symm (y - x)) (nhds x) (nhds 0) := by
    have ht : ContinuousAt (fun y ↦ e.symm (y - x)) x :=
      (e.symm.continuous.comp (continuous_id.sub continuous_const)).continuousAt
    simpa only [ContinuousAt, sub_self, map_zero] using ht
  filter_upwards [(hk.tendsto' _ _ hk0).eventually (Metric.ball_mem_nhds 0 hr),
    hevent.eventually hgraph] with y hy hz
  refine ⟨hy, fun hyR ↦ ?_⟩
  have hrep : x + ((e.symm (y - x)).1 : E) + (e.symm (y - x)).2 • v = y := by
    rw [add_assoc, ← he, e.apply_symm_apply, add_sub_cancel]
  have hψy := hz.mp (hrep.symm ▸ hyR.1.1)
  change x + ((e.symm (y - x)).1 : E) + ψ ((e.symm (y - x)).1) • v = y
  rw [hψy, hrep]

private theorem regular_local_continuation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {P Q : E → ℂ}
    (hU : IsOpen U) (hP : AnalyticOnNhd ℂ P U) (hQ : AnalyticOnNhd ℂ Q U)
    {x : E} (hx : x ∈ gaga20_regularZero P ∩ U) :
    ∃ N ∈ nhds x, ∀ y ∈ N, y ∈ gaga20_regularZero P ∩ U →
      (∀ᶠ z in nhds y, z ∈ gaga20_regularZero P ∩ U → Q z = 0) →
      ∀ᶠ z in nhds x, z ∈ gaga20_regularZero P ∩ U → Q z = 0 := by
  obtain ⟨g, k, r, hr, hg0, hk, hk0, hga, hgR, hrecover⟩ := regular_graph_chart hU hP hx
  obtain ⟨N, hN, hNo, hxN⟩ := eventually_nhds_iff.mp hrecover
  refine ⟨N, hNo.mem_nhds hxN, fun y hy hyR hyzero ↦ ?_⟩
  have hyball := (hN y hy).1
  have hgy := (hN y hy).2 hyR
  have hcomp : AnalyticOnNhd ℂ (fun t ↦ Q (g t)) (Metric.ball 0 r) :=
    fun t ht ↦ (hQ _ (hgR ht).2).comp (hga t ht)
  have hgyt : Tendsto g (nhds (k y)) (nhds y) := by
    simpa only [ContinuousAt, hgy] using (hga _ hyball).continuousAt
  have hzero : (fun t ↦ Q (g t)) =ᶠ[nhds (k y)] 0 := by
    filter_upwards [hgyt.eventually hyzero, Metric.isOpen_ball.mem_nhds hyball] with t ht htb
    exact ht (hgR htb)
  have hall := hcomp.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : LinearMap.ker (fderiv ℂ P x : E →ₗ[ℂ] ℂ)) r).isPreconnected
    hyball hzero
  filter_upwards [hrecover] with z hz hzR
  rw [← hz.2 hzR]
  exact hall hz.1

private theorem regular_connected_continuation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U W : Set E} {P Q : E → ℂ}
    (hU : IsOpen U) (hW : IsOpen W) (hWU : W ⊆ U)
    (hP : AnalyticOnNhd ℂ P U) (hQ : AnalyticOnNhd ℂ Q U)
    (hc : IsConnected (gaga20_regularZero P ∩ U))
    (hne : (gaga20_regularZero P ∩ W).Nonempty)
    (hzero : ∀ x ∈ gaga20_regularZero P ∩ W, Q x = 0) :
    ∀ x ∈ gaga20_regularZero P ∩ U, Q x = 0 := by
  let R := gaga20_regularZero P ∩ U
  let S : Set R := {x | ∀ᶠ z in nhds (x : E), z ∈ R → Q z = 0}
  have hopen : IsOpen S :=
    isOpen_setOfPred_eventually_nhds.preimage continuous_subtype_val
  have hclosed : IsClosed S := by
    apply isClosed_iff_nhds.mpr
    intro x hx
    obtain ⟨N, hN, hprop⟩ := regular_local_continuation hU hP hQ x.property
    have hN' : {y : R | (y : E) ∈ N} ∈ nhds x :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hN
    obtain ⟨y, hyN, hyS⟩ := hx _ hN'
    exact hprop y hyN y.property hyS
  have hnonempty : S.Nonempty := by
    obtain ⟨x, hxR, hxW⟩ := hne
    refine ⟨⟨x, hxR, hWU hxW⟩, ?_⟩
    filter_upwards [hW.mem_nhds hxW] with z hz hzR
    exact hzero z ⟨hzR.1, hz⟩
  have : PreconnectedSpace R := isPreconnected_iff_preconnectedSpace.mp hc.isPreconnected
  have hall : S = univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ hnonempty
  intro x hx
  have hxS : (⟨x, hx⟩ : R) ∈ S := hall.symm ▸ mem_univ _
  exact (Filter.Eventually.self_of_nhds hxS) hx

theorem gaga20_component_identification_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (U W : Set E) (P Q : E → ℂ)
    (hU : IsOpen U) (hW : IsOpen W) (hWU : W ⊆ U)
    (hP : AnalyticOnNhd ℂ P U) (hQ : AnalyticOnNhd ℂ Q U)
    (hcP : IsConnected (gaga20_regularZero P ∩ U))
    (hcQ : IsConnected (gaga20_regularZero Q ∩ U))
    (hdP : closure (gaga20_regularZero P ∩ U) ∩ U = {x ∈ U | P x = 0})
    (hdQ : closure (gaga20_regularZero Q ∩ U) ∩ U = {x ∈ U | Q x = 0})
    (hne : (gaga20_regularZero P ∩ W).Nonempty)
    (hpatch : gaga20_regularZero P ∩ W = gaga20_regularZero Q ∩ W) :
    {x ∈ U | P x = 0} = {x ∈ U | Q x = 0} := by
  have hQP := regular_connected_continuation hU hW hWU hP hQ hcP hne
    (fun x hx ↦ (show x ∈ gaga20_regularZero Q ∩ W from hpatch ▸ hx).1.1)
  have hPQ := regular_connected_continuation hU hW hWU hQ hP hcQ
    (hpatch ▸ hne)
    (fun x hx ↦ (show x ∈ gaga20_regularZero P ∩ W from hpatch.symm ▸ hx).1.1)
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hxc : x ∈ closure (gaga20_regularZero P ∩ U) :=
      (show x ∈ closure (gaga20_regularZero P ∩ U) ∩ U from hdP.symm ▸ hx).1
    exact (hQ x hx.1).continuousAt.continuousWithinAt.eq_const_of_mem_closure hxc hQP
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hxc : x ∈ closure (gaga20_regularZero Q ∩ U) :=
      (show x ∈ closure (gaga20_regularZero Q ∩ U) ∩ U from hdQ.symm ▸ hx).1
    exact (hP x hx.1).continuousAt.continuousWithinAt.eq_const_of_mem_closure hxc hPQ

theorem gaga20_relative_local_finiteness_aux {E : Type*} [TopologicalSpace E]
    {U : Set E} {A : Type*} (C : A → Set E)
    (hU : IsOpen U)
    (hlocal : ∀ x ∈ U, ∃ W ∈ nhds x, {a | (C a ∩ W).Nonempty}.Finite) :
    LocallyFinite fun a ↦ ((↑) : U → E) ⁻¹' C a := by
  intro x
  obtain ⟨W, hW, hfin⟩ := hlocal x x.property
  refine ⟨((↑) : U → E) ⁻¹' W, continuousAt_subtype_val.eventually hW, ?_⟩
  exact hfin.subset fun a ha ↦ by
    obtain ⟨y, hyC, hyW⟩ := ha
    exact ⟨y, hyC, hyW⟩

theorem gaga20_multiplicity_constancy_aux {E : Type*} [TopologicalSpace E]
    {A : Type*} (m : A → E → ℕ)
    (R : A → Set E)
    (hconn : ∀ a, IsConnected (R a))
    (hloc : ∀ a x, x ∈ R a → ∃ W ∈ nhds x, ∀ y ∈ W ∩ R a, m a y = m a x) :
    ∀ a x, x ∈ R a → ∀ y, y ∈ R a → m a y = m a x := by
  intro a x hx y hy
  let f : R a → ℕ := fun z ↦ m a z
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    obtain ⟨W, hW, hEq⟩ := hloc a z z.property
    filter_upwards [continuousAt_subtype_val.eventually hW] with w hw
    exact hEq w (mem_inter hw w.property)
  let _ : PreconnectedSpace (R a) :=
    Subtype.preconnectedSpace (hconn a).isPreconnected
  exact hf.apply_eq_of_preconnectedSpace ⟨y, hy⟩ ⟨x, hx⟩

theorem gaga20_match_of_zero_containment_aux {n : ℕ} (p : Fin n → ℂ)
    (P Q : (Fin n → ℂ) → ℂ) (hP : AnalyticAt ℂ P p) (hQ : AnalyticAt ℂ Q p)
    (hiP : IsIrreducibleAt P p) (hiQ : IsIrreducibleAt Q p)
    (hzero : ∀ᶠ z in nhds p, P z = 0 → Q z = 0) : AreAssociatedAt Q P p := by
  obtain ⟨c, hc, hdiv⟩ := spec_hypersurface_nullstellensatz n p P Q hP hQ hiP hzero
  have hc0 : c p ≠ 0 := (hiQ.2 P c hP hc hdiv).resolve_left (not_not.mpr hiP.1)
  exact ⟨c, hc, hc0, hdiv.mono fun z hz ↦ hz.trans (mul_comm _ _)⟩

theorem gaga20_nearby_distinct_divisors_aux {n r : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) {p : (Fin n → ℂ) × ℂ}
    {v : (Fin n → ℂ) × ℂ → ℂ} {P : Fin r → (Fin n → ℂ) × ℂ → ℂ}
    {b : Fin r → ℕ} (hvP : AnalyticAt ℂ v p) (hv0P : v p ≠ 0)
    (hPp : ∀ a, AnalyticAt ℂ (P a) p) (hirr : ∀ a, IsIrreducibleAt (P a) p)
    (hb : ∀ a, 0 < b a) (hcop : Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) p)) :
    ∀ᶠ q in nhds p, ∀ (N : Set ((Fin n → ℂ) × ℂ)), IsOpen N → N ∈ nhds p →
      N ⊆ V i → q ∈ N → AnalyticOnNhd ℂ v N →
      (∀ a, AnalyticOnNhd ℂ (P a) N) →
      (∀ y ∈ N, f i y = v y * ∏ a, P a y ^ b a) →
      ∀ (a c : Fin r), a ≠ c → P a q = 0 → P c q = 0 →
      ∀ (ka kc t : ℕ) (ua uc w : (Fin n → ℂ) × ℂ → ℂ)
        (Qa : Fin ka → (Fin n → ℂ) × ℂ → ℂ)
        (Qc : Fin kc → (Fin n → ℂ) × ℂ → ℂ)
        (R : Fin t → (Fin n → ℂ) × ℂ → ℂ)
        (da : Fin ka → ℕ) (dc : Fin kc → ℕ) (e : Fin t → ℕ),
        AnalyticAt ℂ ua q → ua q ≠ 0 →
        (∀ j, AnalyticAt ℂ (Qa j) q ∧ IsIrreducibleAt (Qa j) q ∧ 0 < da j) →
        Pairwise (fun j l ↦ IsCoprimeAt (Qa j) (Qa l) q) →
        (P a =ᶠ[nhds q] fun y ↦ ua y * ∏ j, Qa j y ^ da j) →
        AnalyticAt ℂ uc q → uc q ≠ 0 →
        (∀ j, AnalyticAt ℂ (Qc j) q ∧ IsIrreducibleAt (Qc j) q ∧ 0 < dc j) →
        Pairwise (fun j l ↦ IsCoprimeAt (Qc j) (Qc l) q) →
        (P c =ᶠ[nhds q] fun y ↦ uc y * ∏ j, Qc j y ^ dc j) →
        AnalyticAt ℂ w q → w q ≠ 0 →
        (∀ l, AnalyticAt ℂ (R l) q ∧ IsIrreducibleAt (R l) q ∧ 0 < e l) →
        Pairwise (fun l s ↦ IsCoprimeAt (R l) (R s) q) →
        (f i =ᶠ[nhds q] fun y ↦ w y * ∏ l, R l y ^ e l) →
        ∀ ja jc, ∃ la lc, localDivisorAt n (Qa ja) q = localDivisorAt n (R la) q ∧
          localDivisorAt n (Qc jc) q = localDivisorAt n (R lc) q ∧ la ≠ lc := by
  have hm := spec_nearby_distinct_group_matching hD i hvP hv0P hPp hirr hb hcop
  filter_upwards [hm] with q hq
  intro N hNo hNp hNV hqN hv hP hfac a c hac hza hzc ka kc t ua uc w Qa Qc R da dc e
    hua hua0 hQa hcQa hfa huc huc0 hQc hcQc hfc hw hw0 hR hcR hfR ja jc
  obtain ⟨la, lc, hla, hlc, hne⟩ := hq N hNo hNp hNV hqN hv hP hfac a c hac hza hzc
    ka kc t ua uc w Qa Qc R da dc e hua hua0 hQa hcQa hfa huc huc0 hQc hcQc hfc
    hw hw0 hR hcR hfR ja jc
  exact ⟨la, lc, spec_localDivisorAt_eq_of_areAssociatedAt (hQa ja).1 (hR la).1 hla,
    spec_localDivisorAt_eq_of_areAssociatedAt (hQc jc).1 (hR lc).1 hlc, hne⟩

theorem gaga20_clean_multiplicity_aux {n k : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ} {b : Fin k → ℕ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hP : ∀ a, AnalyticAt ℂ (P a) 0)
    (hiP : ∀ a, IsIrreducibleAt (P a) 0)
    (hb : ∀ a, 0 < b a)
    (hcop : Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) 0))
    (hfac : f =ᶠ[nhds 0] fun y ↦ u y * ∏ a, P a y ^ b a) :
    ∃ N, IsOpen N ∧ (0 : (Fin n → ℂ) × ℂ) ∈ N ∧
      (∀ q ∈ N, Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) q)) ∧
      ∀ q ∈ N, ∀ a, P a q = 0 → (∀ c, c ≠ a → P c q ≠ 0) →
        ∀ v : (Fin n → ℂ) × ℂ, fderiv ℂ (P a) q v ≠ 0 →
          analyticOrderAt (fun t : ℂ ↦ f (q + t • v)) 0 = b a := by
  have hc : ∀ᶠ q in nhds (0 : (Fin n → ℂ) × ℂ),
      Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) q) := by
    apply eventually_all.mpr
    intro a
    apply eventually_all.mpr
    intro c
    by_cases hac : a = c
    · exact Eventually.of_forall fun _ hne ↦ (hne hac).elim
    · exact (gaga19_pair_propagation_product n 0 (P a) (P c)
        (hP a) (hP c) (hiP a) (hiP c) (hcop hac)).mono fun _ h _ ↦ h.1
  have hm := spec_transverseOrder_of_decomposition hu hu0 hP hb hfac
  obtain ⟨N, hN, hNo, hN0⟩ := eventually_nhds_iff.mp (hc.and hm)
  exact ⟨N, hNo, hN0, fun q hq ↦ (hN q hq).1, fun q hq ↦ (hN q hq).2⟩

theorem gaga20_no_zero_germ_containment_aux {n k : ℕ} (p : Fin n → ℂ)
    (P : Fin k → (Fin n → ℂ) → ℂ)
    (hP : ∀ a, AnalyticAt ℂ (P a) p) (hiP : ∀ a, IsIrreducibleAt (P a) p)
    (hcop : Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) p)) :
    ∀ᶠ q in nhds p, ∀ a c, a ≠ c → IsIrreducibleAt (P a) q →
      ¬ (∀ᶠ z in nhds q, P a z = 0 → P c z = 0) := by
  obtain ⟨N, hNo, hpN, hN⟩ := spec_eventually_pairwise_coprime n k p P hP hiP hcop
  have ha : ∀ᶠ q in nhds p, ∀ a, AnalyticAt ℂ (P a) q :=
    eventually_all.mpr fun a ↦ (hP a).eventually_analyticAt
  filter_upwards [hNo.mem_nhds hpN, ha] with q hq hqa
  intro a c hac hia hzero
  obtain ⟨s, hs, hdiv⟩ := spec_hypersurface_nullstellensatz n q (P a) (P c)
    (hqa a) (hqa c) hia hzero
  apply hN q hq a c hac
  exact ⟨P a, fun _ ↦ 1, s, hqa a, hia, analyticAt_const,
    Eventually.of_forall (fun z ↦ (mul_one (P a z)).symm), hs, hdiv⟩

end HodgeLean.Foundations.AnalyticDivisorAlgebraic20
