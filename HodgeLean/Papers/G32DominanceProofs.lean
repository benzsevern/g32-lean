import HodgeLean.Papers.G32DominanceDefs
import HodgeLean.Papers.PapersG32Rank
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # G32 Theorem A, stage 4: dominance, open proof obligations -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set Filter
open scoped Topology
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

private def g32r_taylorSeries (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦ (Nat.factorial n : ℂ)⁻¹ * iteratedDeriv n f 0

@[simp] private lemma g32r_coeff_taylorSeries (f : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (g32r_taylorSeries f) =
      (Nat.factorial n : ℂ)⁻¹ * iteratedDeriv n f 0 := by
  simp [g32r_taylorSeries]

private lemma g32r_taylorSeries_mul {f g : ℂ → ℂ}
    (hf : ContDiffAt ℂ ⊤ f 0) (hg : ContDiffAt ℂ ⊤ g 0) :
    g32r_taylorSeries (f * g) = g32r_taylorSeries f * g32r_taylorSeries g := by
  ext n
  rw [g32r_coeff_taylorSeries, iteratedDeriv_mul (hf.of_le le_top) (hg.of_le le_top),
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [g32r_coeff_taylorSeries]
  rw [Finset.mul_sum]
  simp only [Nat.succ_eq_add_one]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by simpa using hi
  have hfac : (n.choose i : ℂ) * (Nat.factorial i : ℂ) *
      (Nat.factorial (n - i) : ℂ) = (Nat.factorial n : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  have hc : (n.choose i : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hin).ne'
  rw [← hfac]
  field_simp [hc]

private lemma g32r_taylorSeries_add {f g : ℂ → ℂ}
    (hf : ContDiffAt ℂ ⊤ f 0) (hg : ContDiffAt ℂ ⊤ g 0) :
    g32r_taylorSeries (f + g) = g32r_taylorSeries f + g32r_taylorSeries g := by
  ext n
  simp [iteratedDeriv_add (hf.of_le le_top) (hg.of_le le_top), mul_add]

private lemma g32r_taylorSeries_const_smul (c : ℂ) {f : ℂ → ℂ}
    (hf : ContDiffAt ℂ ⊤ f 0) :
    g32r_taylorSeries (c • f) = c • g32r_taylorSeries f := by
  ext n
  simp [iteratedDeriv_const_smul (hf.of_le le_top)]
  ring

private lemma g32r_taylorSeries_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, ContDiffAt ℂ ⊤ (f i) 0) :
    g32r_taylorSeries (∑ i ∈ s, f i) = ∑ i ∈ s, g32r_taylorSeries (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext n; simp [g32r_taylorSeries]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have hs : ContDiffAt ℂ ⊤ (∑ i ∈ s, f i) 0 := by
        convert (ContDiffAt.sum fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)) using 1
        ext x
        simp
      rw [g32r_taylorSeries_add (hf a (Finset.mem_insert_self ..)) hs,
        ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))]

private lemma g32r_taylorSeries_prod {ι : Type*} {s : Finset ι} {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, ContDiffAt ℂ ⊤ (f i) 0) :
    g32r_taylorSeries (∏ i ∈ s, f i) = ∏ i ∈ s, g32r_taylorSeries (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      ext n
      rw [g32r_coeff_taylorSeries]
      change (Nat.factorial n : ℂ)⁻¹ * iteratedDeriv n (fun _ : ℂ ↦ (1 : ℂ)) 0 = _
      rw [iteratedDeriv_const]
      cases n <;> simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      have hs : ContDiffAt ℂ ⊤ (∏ i ∈ s, f i) 0 :=
        contDiffAt_prod' fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      rw [g32r_taylorSeries_mul (hf a (Finset.mem_insert_self ..)) hs,
        ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))]

private lemma g32r_taylorSeries_det {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℂ → Matrix n n ℂ) (hA : ∀ i j, ContDiffAt ℂ ⊤ (fun z ↦ (A z) i j) 0) :
    g32r_taylorSeries (fun z ↦ (A z).det) =
      Matrix.det ((fun i j ↦ g32r_taylorSeries (fun z ↦ (A z) i j)) :
        Matrix n n (PowerSeries ℂ)) := by
  classical
  let B : Matrix n n (PowerSeries ℂ) :=
    fun i j ↦ g32r_taylorSeries (fun z ↦ (A z) i j)
  change g32r_taylorSeries (fun z ↦ (A z).det) = B.det
  rw [Matrix.det_apply B]
  simp only [Matrix.det_apply]
  dsimp only [B]
  let f : Equiv.Perm n → ℂ → ℂ := fun σ ↦
    ((Equiv.Perm.sign σ : ℤ) : ℂ) • (∏ i, fun z ↦ (A z) (σ i) i)
  have hfun : (fun z ↦ ∑ σ : Equiv.Perm n,
      Equiv.Perm.sign σ • ∏ i, (A z) (σ i) i) = ∑ σ, f σ := by
    ext z
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro σ hσ
    simp only [f, Pi.smul_apply, Finset.prod_apply]
    exact (Int.cast_smul_eq_zsmul (R := ℂ) (Equiv.Perm.sign σ)
      (∏ i, (A z) (σ i) i)).symm
  rw [hfun, g32r_taylorSeries_sum]
  · apply Finset.sum_congr rfl
    intro σ hσ
    have hp : ContDiffAt ℂ ⊤ (∏ i, fun z ↦ (A z) (σ i) i) 0 :=
      contDiffAt_prod' fun i _ ↦ hA (σ i) i
    rw [show f σ = (Equiv.Perm.sign σ : ℂ) •
        (∏ i, fun z ↦ (A z) (σ i) i) by rfl,
      g32r_taylorSeries_const_smul _ hp, g32r_taylorSeries_prod]
    · change (((Equiv.Perm.sign σ : ℤ) : ℂ) •
          ∏ i, g32r_taylorSeries (fun z ↦ (A z) (σ i) i)) = _
      exact (Int.cast_smul_eq_zsmul (R := ℂ) (Equiv.Perm.sign σ)
        (∏ i, g32r_taylorSeries (fun z ↦ (A z) (σ i) i)))
    · exact fun i _ ↦ hA (σ i) i
  · intro σ hσ
    dsimp only [f]
    convert (contDiffAt_prod' fun i _ ↦ hA (σ i) i).const_smul
      (((Equiv.Perm.sign σ : ℤ) : ℂ)) using 1

private lemma g32r_taylorSeries_eq_mk {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt f p 0) :
    g32r_taylorSeries f = PowerSeries.mk p.coeff := by
  ext n
  rw [g32r_coeff_taylorSeries, PowerSeries.coeff_mk]
  have hd : iteratedDeriv n f 0 = (Nat.factorial n : ℂ) * p.coeff n := by
    obtain ⟨r, hr⟩ := hp
    have h := hr.iteratedFDeriv_eq_sum_of_completeSpace (n := n) (fun _ ↦ 1)
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at h
    simpa [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Fintype.card_perm] using h
  rw [hd]
  have hf : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hf]

theorem g32r_open_image_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (f : E → Fin 9 → ℂ) (f' : E →L[ℂ] Fin 9 → ℂ) (x : E) (V : Set E)
    (hV : IsOpen V) (hx : x ∈ V) (hf : HasStrictFDerivAt f f' x)
    (hrank : Module.finrank ℂ (LinearMap.range (f' : E →ₗ[ℂ] Fin 9 → ℂ)) = 9) :
    ∃ U : Set (Fin 9 → ℂ), IsOpen U ∧ f x ∈ U ∧ U ⊆ f '' V := by
  have hrange : LinearMap.range (f' : E →ₗ[ℂ] Fin 9 → ℂ) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (hrank.trans (by simp))
  have himage : f '' V ∈ 𝓝 (f x) := by
    rw [← hf.map_nhds_eq_of_surj hrange]
    exact Filter.image_mem_map (hV.mem_nhds hx)
  obtain ⟨U, hUV, hU, hxU⟩ := mem_nhds_iff.mp himage
  exact ⟨U, hU, hxU, hUV⟩

theorem g32r_open_image_analytic_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (f : E → Fin 9 → ℂ) (V : Set E) (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f V) (x : E) (hx : x ∈ V)
    (hrank : Module.finrank ℂ (LinearMap.range (fderiv ℂ f x : E →ₗ[ℂ] Fin 9 → ℂ)) = 9) :
    ∃ U : Set (Fin 9 → ℂ), IsOpen U ∧ f x ∈ U ∧ U ⊆ f '' V := by
  exact g32r_open_image_aux f (fderiv ℂ f x) x V hV hx
    (hf x hx).hasStrictFDerivAt hrank

theorem g32r_rank_conj_aux (A : Matrix (Fin 9) (Fin 10) ℂ)
    (f : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) (L : Matrix (Fin 9) (Fin 9) ℂ)
    (R : Matrix (Fin 10) (Fin 10) ℂ) (hL : IsUnit L) (hR : IsUnit R)
    (h : A = L * LinearMap.toMatrix' f * R) :
    A.rank = Module.finrank ℂ (LinearMap.range f) := by
  rw [h, Matrix.rank_mul_eq_left_of_isUnit_det R _
      ((Matrix.isUnit_iff_isUnit_det R).mp hR),
    Matrix.rank_mul_eq_right_of_isUnit_det L _ ((Matrix.isUnit_iff_isUnit_det L).mp hL),
    Matrix.rank]
  rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']

theorem g32r_jet_rank_zero_aux (M : ℂ → Matrix (Fin 9) (Fin 10) ℂ)
    (hM : g32r_CertifiedJet M) : (M 0).rank = 5 := by
  obtain ⟨p, hp, hcoeff⟩ := hM
  have hM0 : M 0 = papers8_M0.map (algebraMap ℚ ℂ) := by
    ext i j
    have hv : M 0 i j = (p i j).coeff 0 := by
      simpa using ((hp i j).coeff_zero 1).symm
    rw [hv, hcoeff i j 0 (by omega)]
    simp [papers8_Mseries, Fin.sum_univ_succ, ← PowerSeries.coeff_zero_eq_constantCoeff]
    simp_rw [PowerSeries.coeff_monomial]
    norm_num
  rw [hM0]
  let rows : Fin 5 → Fin 9 := ![0, 1, 2, 3, 6]
  let cols : Fin 5 → Fin 10 := ![1, 2, 3, 4, 5]
  have hfactorQ : papers8_rankLeft * papers8_rankRight = papers8_M0 := by
    set_option maxRecDepth 100000 in
      decide +kernel
  have hfactor : papers8_rankLeft.map (algebraMap ℚ ℂ) *
      papers8_rankRight.map (algebraMap ℚ ℂ) = papers8_M0.map (algebraMap ℚ ℂ) := by
    simpa using congrArg (fun A => A.map (algebraMap ℚ ℂ)) hfactorQ
  have hminorQ : papers8_M0.submatrix rows cols = papers8_rankMinor := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hminor : (papers8_M0.map (algebraMap ℚ ℂ)).submatrix rows cols =
      papers8_rankMinor.map (algebraMap ℚ ℂ) := by
    rw [← hminorQ]
    rfl
  have hminorUnitQ : IsUnit papers8_rankMinor := by
    refine ⟨{ val := papers8_rankMinor
              inv := papers8_rankMinorInv
              val_inv := by decide +kernel
              inv_val := by decide +kernel }, rfl⟩
  have hminorUnit : IsUnit (papers8_rankMinor.map (algebraMap ℚ ℂ)) :=
    hminorUnitQ.map (algebraMap ℚ ℂ).mapMatrix
  apply Nat.le_antisymm
  · rw [← hfactor]
    exact (Matrix.rank_mul_le_right _ _).trans (by
      simpa only [Fintype.card_fin] using
        (Matrix.rank_le_card_height (papers8_rankRight.map (algebraMap ℚ ℂ))))
  · have hrankMinor : (papers8_rankMinor.map (algebraMap ℚ ℂ)).rank = 5 := by
      simpa using Matrix.rank_of_isUnit _ hminorUnit
    calc
      5 = (papers8_rankMinor.map (algebraMap ℚ ℂ)).rank := hrankMinor.symm
      _ = ((papers8_M0.map (algebraMap ℚ ℂ)).submatrix rows cols).rank :=
        congrArg Matrix.rank hminor.symm
      _ ≤ (papers8_M0.map (algebraMap ℚ ℂ)).rank :=
        Matrix.rank_submatrix_le _ rows cols

theorem g32r_jet_rank_nine_aux (M : ℂ → Matrix (Fin 9) (Fin 10) ℂ)
    (hM : g32r_CertifiedJet M) : ∀ᶠ θ in 𝓝[≠] (0 : ℂ), (M θ).rank = 9 := by
  obtain ⟨p, hp, hcoeff⟩ := hM
  let A : ℂ → Matrix (Fin 9) (Fin 9) ℂ := fun θ ↦ (M θ).submatrix id Fin.succ
  let B : Matrix (Fin 9) (Fin 10) (PowerSeries ℂ) :=
    fun i j ↦ PowerSeries.mk (p i j).coeff
  have hB : ∀ i j k, k ≤ 7 → PowerSeries.coeff k (B i j) =
      algebraMap ℚ ℂ (PowerSeries.coeff k (papers8_Mseries i j)) := by
    intro i j k hk
    simpa [B] using hcoeff i j k hk
  have horder : PowerSeries.order (B.submatrix id Fin.succ).det = 7 := by
    exact papers_g32_powerSeries_order_complex B hB
  have hBdet : (B.submatrix id Fin.succ).det ≠ 0 := by
    intro h
    rw [h] at horder
    simp at horder
  have hAtps : g32r_taylorSeries (fun θ ↦ (A θ).det) =
      (B.submatrix id Fin.succ).det := by
    rw [g32r_taylorSeries_det A]
    congr 1
    ext i j n
    change PowerSeries.coeff n (g32r_taylorSeries (fun z ↦ (M z) i (Fin.succ j))) =
      PowerSeries.coeff n (PowerSeries.mk (p i (Fin.succ j)).coeff)
    rw [g32r_taylorSeries_eq_mk (hp i (Fin.succ j))]
    intro i j
    exact (hp i (Fin.succ j)).analyticAt.contDiffAt
  have han : AnalyticAt ℂ (fun θ ↦ (A θ).det) 0 := by
    simp only [Matrix.det_apply]
    apply Finset.analyticAt_fun_sum
    intro σ hσ
    apply AnalyticAt.const_smul
    apply Finset.analyticAt_fun_prod
    intro i hi
    exact (hp (σ i) (Fin.succ i)).analyticAt
  obtain ⟨q, hq⟩ := han
  have hqne : q ≠ 0 := by
    intro hq0
    have ht0 : g32r_taylorSeries (fun θ ↦ (A θ).det) = 0 := by
      rw [g32r_taylorSeries_eq_mk hq, hq0]
      ext n
      simp [FormalMultilinearSeries.coeff]
    exact hBdet (hAtps ▸ ht0)
  filter_upwards [hq.locally_ne_zero hqne] with θ hdet
  apply Nat.le_antisymm
  · simpa using Matrix.rank_le_card_height (M θ)
  · have hrankA : (A θ).rank = 9 := Matrix.rank_of_det_ne_zero hdet
    have hle : (A θ).rank ≤ (M θ).rank := by
      simpa [A] using Matrix.rank_submatrix_le (M θ) id Fin.succ
    omega

theorem g32r_period_rank_nine_aux (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (Φ : g32r_PeriodMap F P) :
    ∃ t ∈ Φ.V, Module.finrank ℂ
      (LinearMap.range (fderiv ℂ Φ.period t : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ)) = 9 := by
  have hV : ∀ᶠ θ in 𝓝 (0 : ℂ), Φ.curve θ ∈ Φ.V :=
    Φ.curve_cont.eventually_mem (Φ.isOpen_V.mem_nhds Φ.curve_zero)
  have hall : ∀ᶠ θ in 𝓝[≠] (0 : ℂ),
      Φ.curve θ ∈ Φ.V ∧ ∃ L R, IsUnit L ∧ IsUnit R ∧
        Φ.jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ Φ.period (Φ.curve θ) : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * R ∧
        (Φ.jet θ).rank = 9 := by
    filter_upwards [hV.filter_mono inf_le_left, Φ.codiff.filter_mono inf_le_left,
      g32r_jet_rank_nine_aux Φ.jet Φ.jet_certified] with θ hθV hθcod hθrank
    obtain ⟨L, R, hL, hR, heq⟩ := hθcod
    exact ⟨hθV, L, R, hL, hR, heq, hθrank⟩
  obtain ⟨θ, hθV, L, R, hL, hR, heq, hθrank⟩ := hall.exists
  refine ⟨Φ.curve θ, hθV, ?_⟩
  rw [← g32r_rank_conj_aux (Φ.jet θ) _ L R hL hR heq, hθrank]

theorem g32r_dominant_aux (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (Φ : g32r_PeriodMap F P) :
    ∃ U : Set g32m_Domain, IsOpen U ∧ U.Nonempty ∧
      ∀ m ∈ U, ∃ s, g32t_KIsog (P.fiber s) (F.univ m) := by
  obtain ⟨t, htV, hrank⟩ := g32r_period_rank_nine_aux F P Φ
  obtain ⟨U, hU, htU, hUV⟩ :=
    g32r_open_image_analytic_aux Φ.period Φ.V Φ.isOpen_V Φ.analytic t htV hrank
  refine ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val,
    ⟨⟨Φ.period t, Φ.mapsTo htV⟩, htU⟩, ?_⟩
  intro m hm
  obtain ⟨t', ht'V, heq⟩ := hUV hm
  obtain ⟨s, hs⟩ := Φ.isog t' ht'V
  have hm_eq : (⟨Φ.period t', Φ.mapsTo ht'V⟩ : g32m_Domain) = m :=
    Subtype.ext heq
  exact ⟨s, hm_eq ▸ hs⟩

end HodgeLean.Papers
