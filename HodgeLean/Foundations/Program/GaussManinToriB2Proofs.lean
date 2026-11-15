import HodgeLean.Foundations.Program.GaussManinToriB2Defs

/-! # Proof obligations for the marked-period adapter to B2 -/

noncomputable section

set_option maxHeartbeats 400000

open Manifold
open scoped TensorProduct Matrix ContDiff

namespace HodgeLean.Foundations.Program

variable {g : ℕ}

theorem d2b_cplxPeriod_surjective_aux {P : Fin g → Fin (2 * g) → ℂ}
    (hP : d2_IsPeriodMatrix P) : Function.Surjective (d2b_cplxPeriod P) := by
  intro z
  obtain ⟨s, rfl⟩ := (d2v_realMap_bijective hP).2 z
  refine ⟨∑ k, (s k : ℂ) ⊗ₜ[ℤ] (Pi.single k 1 : Fin (2 * g) → ℤ), ?_⟩
  rw [map_sum]
  simp only [d2b_cplxPeriod, LinearMap.liftBaseChange_tmul]
  rw [d2_realMap, Fintype.linearCombination_apply]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [d2_markingMap, Fintype.linearCombination_apply, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

theorem d2b_homologyF_isWeightOne_aux {P : Fin g → Fin (2 * g) → ℂ}
    (hP : d2_IsPeriodMatrix P) :
    b2_IsWeightOne (Fin (2 * g) → ℤ) (d2b_homologyF P) := by
  let F := d2b_homologyF P
  have hconj (x : ℂ ⊗[ℤ] (Fin (2 * g) → ℤ)) :
      d2b_vecZ (2 * g) (b2_conj _ x) =
        fun k ↦ starRingEnd ℂ (d2b_vecZ (2 * g) x k) := by
    induction x using TensorProduct.induction_on with
    | zero => ext k; simp
    | tmul c n =>
        ext k
        change ((Pi.basisFun ℤ (Fin (2 * g))).baseChange ℂ).repr
            ((starRingEnd ℂ c) ⊗ₜ[ℤ] n) k = _
        simp [d2b_vecZ, mul_comm]
    | add x y hx hy => ext k; simp [map_add, hx, hy]
  have hperiod (x : ℂ ⊗[ℤ] (Fin (2 * g) → ℤ)) :
      d2b_cplxPeriod P x =
        ∑ k, d2b_vecZ (2 * g) x k • d2_column P k := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c n =>
        ext i
        simp [d2b_cplxPeriod, d2b_vecZ, d2_markingMap,
          Fintype.linearCombination_apply, Module.Basis.equivFun_apply,
          Module.Basis.baseChange_apply, Finset.smul_sum, mul_comm, mul_left_comm]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
    | add x y hx hy =>
        ext i
        simp [map_add, hx, hy, Finset.sum_add_distrib]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hdisj : Disjoint F (b2_conjSubmodule (Fin (2 * g) → ℤ) F) := by
    rw [Submodule.disjoint_def]
    intro x hxF hxc
    rw [b2a_mem_conjSubmodule] at hxc
    obtain ⟨y, hyF, hy⟩ := hxc
    have hx0 : d2b_cplxPeriod P x = 0 := hxF
    have hy0 : d2b_cplxPeriod P y = 0 := hyF
    have hxy : d2b_vecZ (2 * g) x =
        fun k ↦ starRingEnd ℂ (d2b_vecZ (2 * g) y k) := by
      rw [← hy, hconj]
    let a : Fin (2 * g) → ℝ := fun k ↦ (d2b_vecZ (2 * g) y k).re
    let b : Fin (2 * g) → ℝ := fun k ↦ (d2b_vecZ (2 * g) y k).im
    have hs : d2_realMap P a + Complex.I • d2_realMap P b = 0 := by
      rw [hperiod] at hy0
      rw [d2_realMap, Fintype.linearCombination_apply,
        Fintype.linearCombination_apply]
      convert hy0 using 1
      ext i
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Complex.real_smul, a, b]
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      simp only [d2_column, Pi.smul_apply]
      apply Complex.ext <;> simp <;> ring
    have ht : d2_realMap P a - Complex.I • d2_realMap P b = 0 := by
      rw [hperiod] at hx0
      rw [hxy] at hx0
      rw [d2_realMap, Fintype.linearCombination_apply,
        Fintype.linearCombination_apply]
      convert hx0 using 1
      ext i
      simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, Complex.real_smul, a, b]
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      simp only [d2_column, Pi.smul_apply]
      apply Complex.ext <;> simp <;> ring
    have ha0 : d2_realMap P a = 0 := by
      funext i
      change d2_realMap P a i = (0 : ℂ)
      have hsi := congrFun hs i
      have hti := congrFun ht i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul] at hsi hti
      linear_combination (1 / 2 : ℂ) * hsi + (1 / 2 : ℂ) * hti
    have hb0 : d2_realMap P b = 0 := by
      funext i
      change d2_realMap P b i = (0 : ℂ)
      have hsi := congrFun hs i
      have hti := congrFun ht i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul] at hsi hti
      have h2 : (2 * Complex.I) * d2_realMap P b i = 0 := by
        linear_combination hsi - hti
      exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    have ha : a = 0 := (d2v_realMap_injective hP) (by simpa using ha0)
    have hb : b = 0 := (d2v_realMap_injective hP) (by simpa using hb0)
    apply (d2b_vecZ (2 * g)).injective
    rw [hxy]
    funext k
    have hak := congrFun ha k
    have hbk := congrFun hb k
    apply Complex.ext <;> simp [a, b] at hak hbk ⊢ <;> assumption
  change b2_IsWeightOne (Fin (2 * g) → ℤ) F
  refine ⟨hdisj, codisjoint_iff.mpr (Submodule.eq_top_of_finrank_eq ?_)⟩
  have hrank := LinearMap.finrank_range_add_finrank_ker (d2b_cplxPeriod P)
  have hrange : LinearMap.range (d2b_cplxPeriod P) = ⊤ :=
    LinearMap.range_eq_top.mpr (d2b_cplxPeriod_surjective_aux hP)
  have hker : Module.finrank ℂ F = g := by
    rw [hrange, finrank_top, Module.finrank_fin_fun,
      show Module.finrank ℂ (ℂ ⊗[ℤ] (Fin (2 * g) → ℤ)) = 2 * g by
        rw [Module.finrank_baseChange, Module.finrank_fin_fun]] at hrank
    change Module.finrank ℂ (LinearMap.ker (d2b_cplxPeriod P)) = g
    omega
  have h := Submodule.finrank_sup_add_finrank_inf_eq F (b2_conjSubmodule _ F)
  rw [disjoint_iff.mp hdisj, finrank_bot, hker, b2a_finrank_conjSubmodule, hker,
    Nat.add_zero] at h
  rw [show Module.finrank ℂ (ℂ ⊗[ℤ] (Fin (2 * g) → ℤ)) = 2 * g by
    rw [Module.finrank_baseChange, Module.finrank_fin_fun]]
  omega

theorem d2b_hodgeOne_eq_annihilator_aux (P : Fin g → Fin (2 * g) → ℂ) :
    d2_hodgeOne P =
      {c | ∀ x ∈ d2b_homologyF P, d2b_pairing g c x = 0} := by
  have hpair_inj : Function.Injective (d2b_pairing g) := by
    intro c d hcd
    apply (d2_vec (2 * g)).symm.injective
    funext k
    let n : Fin (2 * g) → ℤ := Pi.single k 1
    have h := LinearMap.congr_fun hcd ((1 : ℂ) ⊗ₜ[ℤ] n)
    simpa [d2b_pairing, d2b_vecZ, dotProduct, n, Pi.single_apply] using h
  have hcomp (phi : Module.Dual ℂ (Fin g → ℂ)) :
      d2b_pairing g (d2_evalBilin P phi) =
        (d2b_cplxPeriod P).dualMap phi := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c n =>
        simp [d2b_pairing, d2b_vecZ, d2_evalBilin, d2b_cplxPeriod,
          d2_markingMap, d2_vec, dotProduct, Fintype.linearCombination_apply,
          Module.Basis.equivFun_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_eq_single k]
        · change _ = c * phi ((n k : ℂ) • d2_column P k)
          rw [map_smul]
          simp [d2_column]
          rw [show (fun i ↦ P i k) = d2_column P k from rfl]
          ring
        · intro j _ hj
          simp [Pi.single_apply, hj]
        · simp
    | add x y hx hy => simp [map_add, hx, hy]
  ext c
  change c ∈ d2_hodgeOne P ↔ _
  rw [d2_hodgeOne, LinearMap.mem_range]
  change (∃ phi, d2_evalBilin P phi = c) ↔
    ∀ x, x ∈ LinearMap.ker (d2b_cplxPeriod P) → d2b_pairing g c x = 0
  rw [← Submodule.mem_dualAnnihilator]
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  constructor
  · rintro ⟨phi, rfl⟩
    exact ⟨phi, (hcomp phi).symm⟩
  · rintro ⟨phi, hphi⟩
    refine ⟨phi, hpair_inj ?_⟩
    rw [hcomp, hphi]

theorem d2b_form_baseChange_eq_EC (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (x y : ℂ ⊗[ℤ] (Fin (2 * g) → ℤ)) :
    LinearMap.BilinForm.baseChange ℂ
      ((Matrix.toLinearMap₂' ℤ A) :
        LinearMap.BilinForm ℤ (Fin (2 * g) → ℤ)) x y =
      d2v_EC A (d2b_vecZ (2 * g) x) (d2b_vecZ (2 * g) y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [d2v_EC]
  | tmul c m =>
      induction y using TensorProduct.induction_on with
      | zero => simp [d2v_EC]
      | tmul d n =>
          simp [d2b_vecZ, d2v_EC, Matrix.toLinearMap₂'_apply', dotProduct,
            Matrix.mulVec, Fintype.linearCombination_apply]
          push_cast
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [show (∑ j, (A i j : ℂ) * ((n j : ℂ) * d)) =
              d * ∑ j, (A i j : ℂ) * (n j : ℂ) by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring]
          ring
      | add y z hy hz => simp [map_add, hy, hz, d2v_EC, Matrix.mulVec_add, dotProduct_add]
  | add x z hx hz => simp [map_add, hx, hz, d2v_EC, add_dotProduct]

theorem d2b_mem_homologyF_iff {P : Fin g → Fin (2 * g) → ℂ}
    (hP : d2_IsPeriodMatrix P) (x : ℂ ⊗[ℤ] (Fin (2 * g) → ℤ)) :
    x ∈ d2b_homologyF P ↔ ∃ s : Fin (2 * g) → ℝ,
      d2b_vecZ (2 * g) x = d2v_cplx s (d2v_J hP s) := by
  have hperiod : d2b_cplxPeriod P x =
      ∑ k, d2b_vecZ (2 * g) x k • d2_column P k := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c n =>
        ext i
        simp [d2b_cplxPeriod, d2b_vecZ, d2_markingMap,
          Fintype.linearCombination_apply, Module.Basis.equivFun_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
    | add x y hx hy =>
        ext i
        simp [map_add, hx, hy]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
  let s : Fin (2 * g) → ℝ := fun k ↦ (d2b_vecZ (2 * g) x k).re
  let t : Fin (2 * g) → ℝ := fun k ↦ (d2b_vecZ (2 * g) x k).im
  have hcoord : d2b_vecZ (2 * g) x = d2v_cplx s t := by
    funext k
    apply Complex.ext <;> simp [s, t, d2v_cplx]
  constructor
  · intro hx
    rw [d2b_homologyF, LinearMap.mem_ker, hperiod, hcoord] at hx
    have hs : d2_realMap P s + Complex.I • d2_realMap P t = 0 := by
      rw [d2_realMap, Fintype.linearCombination_apply,
        Fintype.linearCombination_apply]
      convert hx using 1
      ext i
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      simp [d2v_cplx, d2_column]
      ring
    have hrel : d2_realMap P t = Complex.I • d2_realMap P s := by
      funext i
      have hsi := congrFun hs i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hsi ⊢
      linear_combination (-Complex.I) * hsi +
        (d2_realMap P t i) * Complex.I_mul_I
    refine ⟨s, hcoord.trans ?_⟩
    congr 1
    exact d2v_realMap_injective hP (hrel.trans (d2v_realMap_J hP s).symm)
  · rintro ⟨u, hu⟩
    rw [d2b_homologyF, LinearMap.mem_ker, hperiod, hu]
    have hJ := d2v_realMap_J hP u
    have hs : d2_realMap P u + Complex.I • d2_realMap P (d2v_J hP u) = 0 := by
      funext i
      have hJi := congrFun hJ i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hJi ⊢
      rw [hJi, ← mul_assoc, Complex.I_mul_I]
      ring
    ext i
    simp only [Finset.sum_apply, Pi.zero_apply]
    have hsi := congrFun hs i
    simp only [d2_realMap, Fintype.linearCombination_apply, Pi.add_apply,
      Pi.smul_apply, Pi.zero_apply, smul_eq_mul, Finset.sum_apply,
      Complex.real_smul] at hsi
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Complex.real_smul] at hsi ⊢
    rw [Finset.mul_sum, ← Finset.sum_add_distrib] at hsi
    rw [← hsi]
    apply Finset.sum_congr rfl
    intro k _
    simp [d2v_cplx, d2_column]
    ring

theorem d2b_isRiemannForm_iff_aux {P : Fin g → Fin (2 * g) → ℂ}
    (hP : d2_IsPeriodMatrix P) (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) :
    d2_IsRiemannForm P A ↔
      b2_IsRiemannForm (Fin (2 * g) → ℤ) (d2b_homologyF P)
        (Matrix.toLinearMap₂' ℤ A) := by
  let Q : LinearMap.BilinForm ℤ (Fin (2 * g) → ℤ) := Matrix.toLinearMap₂' ℤ A
  have hconj (x : ℂ ⊗[ℤ] (Fin (2 * g) → ℤ)) :
      d2b_vecZ (2 * g) (b2_conj _ x) =
        fun k ↦ starRingEnd ℂ (d2b_vecZ (2 * g) x k) := by
    induction x using TensorProduct.induction_on with
    | zero => ext k; simp
    | tmul c n =>
        ext k
        change ((Pi.basisFun ℤ (Fin (2 * g))).baseChange ℂ).repr
            ((starRingEnd ℂ c) ⊗ₜ[ℤ] n) k = _
        simp [d2b_vecZ, mul_comm]
    | add x y hx hy => ext k; simp [map_add, hx, hy]
  have halt_fwd (h : Aᵀ = -A) : ∀ n, Q n n = 0 := by
    intro n
    simp only [Q, Matrix.toLinearMap₂'_apply']
    have hr := d2v_riemannReal_self A h (fun k ↦ (n k : ℝ))
    unfold d2_riemannReal at hr
    apply Int.cast_injective (α := ℝ)
    simpa [dotProduct, Matrix.mulVec] using hr
  have halt_rev (h : ∀ n, Q n n = 0) : Aᵀ = -A := by
    have hskew (n m : Fin (2 * g) → ℤ) : Q n m = -Q m n := by
      have hnm := h (n + m)
      change Q (n + m) (n + m) = 0 at hnm
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
        h n, h m] at hnm
      linear_combination hnm
    ext i j
    rw [Matrix.transpose_apply, Matrix.neg_apply]
    have hij := hskew (Pi.single j 1) (Pi.single i 1)
    simpa [Q, Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec,
      Pi.single_apply] using hij
  constructor
  · intro hA
    refine ⟨halt_fwd hA.alternating, ?_, ?_⟩
    · intro x hx y hy
      obtain ⟨s, hs⟩ := (d2b_mem_homologyF_iff hP x).1 hx
      obtain ⟨t, ht⟩ := (d2b_mem_homologyF_iff hP y).1 hy
      rw [d2b_form_baseChange_eq_EC, hs, ht, d2v_EC_cplx,
        d2v_E_J_J hA hP, d2v_E_J_right hA hP]
      simp
    · intro x hx hx0
      obtain ⟨s, hs⟩ := (d2b_mem_homologyF_iff hP x).1 hx
      have hs0 : s ≠ 0 := by
        intro h
        subst s
        apply hx0
        apply (d2b_vecZ (2 * g)).injective
        rw [hs]
        ext k
        simp [d2v_cplx]
      rw [d2b_form_baseChange_eq_EC, hs, hconj, hs]
      have hc : (fun k ↦ starRingEnd ℂ (d2v_cplx s (d2v_J hP s) k)) =
          d2v_cplx s (-d2v_J hP s) := by
        funext k
        simp [d2v_cplx]
      rw [hc, d2v_EC_cplx, d2v_riemannReal_neg_right,
        d2v_riemannReal_neg_right,
        d2v_riemannReal_self A hA.alternating,
        d2v_riemannReal_self A hA.alternating,
        d2v_riemannReal_swap A hA.alternating]
      have hp := d2v_E_pos hA hP hs0
      norm_num [Complex.I_mul_I] at hp ⊢
      have hswap := d2v_riemannReal_swap A hA.alternating (d2v_J hP s) s
      linarith
  · intro hQ
    have halt := halt_rev hQ.alt
    refine ⟨halt, ?_, ?_⟩
    · intro s t s' t' hs ht
      have hs' : s' = d2v_J hP s := d2v_realMap_injective hP
        (hs.trans (d2v_realMap_J hP s).symm)
      have ht' : t' = d2v_J hP t := d2v_realMap_injective hP
        (ht.trans (d2v_realMap_J hP t).symm)
      subst s'; subst t'
      let x := (d2b_vecZ (2 * g)).symm (d2v_cplx s (d2v_J hP s))
      let y := (d2b_vecZ (2 * g)).symm (d2v_cplx t (d2v_J hP t))
      have hx : x ∈ d2b_homologyF P :=
        (d2b_mem_homologyF_iff hP x).2 ⟨s, by simp [x]⟩
      have hy : y ∈ d2b_homologyF P :=
        (d2b_mem_homologyF_iff hP y).2 ⟨t, by simp [y]⟩
      have hi := hQ.isotropic x hx y hy
      rw [d2b_form_baseChange_eq_EC] at hi
      simp [x, y, d2v_EC_cplx] at hi
      have hre := congrArg Complex.re hi
      norm_num at hre
      linarith
    · intro s s' hs hrel
      have hs' : s' = d2v_J hP s := d2v_realMap_injective hP
        (hrel.trans (d2v_realMap_J hP s).symm)
      subst s'
      let x := (d2b_vecZ (2 * g)).symm (d2v_cplx s (d2v_J hP s))
      have hx : x ∈ d2b_homologyF P :=
        (d2b_mem_homologyF_iff hP x).2 ⟨s, by simp [x]⟩
      have hx0 : x ≠ 0 := by
        intro h0
        have h0' := congrArg (d2b_vecZ (2 * g)) h0
        simp [x] at h0'
        apply hs
        funext k
        have hk := congrArg Complex.re (congrFun h0' k)
        simpa [d2v_cplx] using hk
      have hp := hQ.positive x hx hx0
      rw [d2b_form_baseChange_eq_EC] at hp
      have hc : (fun k ↦ starRingEnd ℂ (d2v_cplx s (d2v_J hP s) k)) =
          d2v_cplx s (-d2v_J hP s) := by
        funext k
        simp [d2v_cplx]
      simp only [x, LinearEquiv.apply_symm_apply, hconj, hc] at hp
      rw [d2v_EC_cplx, d2v_riemannReal_neg_right,
        d2v_riemannReal_neg_right, d2v_riemannReal_self A halt,
        d2v_riemannReal_swap A halt] at hp
      norm_num [Complex.I_mul_I] at hp ⊢
      have hswap := d2v_riemannReal_swap A halt (d2v_J hP s) s
      linarith

theorem d2b_fiberMap_bijective_aux {P : Fin g → Fin (2 * g) → ℂ}
    (hP : d2_IsPeriodMatrix P) : Function.Bijective (d2b_fiberMap P) := by
  let F := d2b_homologyF P
  let f : ((ℂ ⊗[ℤ] (Fin (2 * g) → ℤ)) ⧸ F) →ₗ[ℂ] (Fin g → ℂ) :=
    F.liftQ (d2b_cplxPeriod P) (by exact le_rfl)
  have hf_surj : Function.Surjective f := by
    intro z
    obtain ⟨x, rfl⟩ := d2b_cplxPeriod_surjective_aux hP z
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    change F.liftQ (d2b_cplxPeriod P) _ (Submodule.Quotient.mk x) = _
    rfl
  have hf_inj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot' _ _ rfl
  have hf_lattice (n : Fin (2 * g) → ℤ) :
      f (b2_latticeMap (Fin (2 * g) → ℤ) F n) = d2_markingMap P n := by
    change d2b_cplxPeriod P ((1 : ℂ) ⊗ₜ[ℤ] n) = d2_markingMap P n
    simp [d2b_cplxPeriod]
  constructor
  · intro a b hab
    induction a using QuotientAddGroup.induction_on with | _ a => ?_
    induction b using QuotientAddGroup.induction_on with | _ b => ?_
    rw [d2b_fiberMap, QuotientAddGroup.lift_mk, QuotientAddGroup.lift_mk] at hab
    change QuotientAddGroup.mk' (d2_lattice P).toAddSubgroup (f a) =
      QuotientAddGroup.mk' (d2_lattice P).toAddSubgroup (f b) at hab
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_iff_sub_mem] at hab
    change f a - f b ∈ d2_lattice P at hab
    rw [d2_lattice, ← Fintype.range_linearCombination] at hab
    obtain ⟨n, hn⟩ := hab
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    refine ⟨n, (hf_inj ?_).symm⟩
    rw [map_sub, hf_lattice]
    exact hn.symm
  · intro z
    induction z using QuotientAddGroup.induction_on with | _ z => ?_
    obtain ⟨x, rfl⟩ := hf_surj z
    refine ⟨QuotientAddGroup.mk' _ x, ?_⟩
    rfl

theorem d2b_fiberMap_isHomeomorph_aux {P : Fin g → Fin (2 * g) → ℂ}
    (hP : d2_IsPeriodMatrix P) : IsHomeomorph (d2b_fiberMap P) := by
  let F := d2b_homologyF P
  letI : CompactSpace (b2_torus (Fin (2 * g) → ℤ) F) :=
    b2_torus_compactSpace F (d2b_homologyF_isWeightOne_aux hP)
  letI : T2Space ((ℂ ⊗[ℤ] (Fin (2 * g) → ℤ)) ⧸ F) := b2t_quot_t2Space F
  letI : DiscreteTopology (d2_lattice P) := d2_lattice_discrete hP
  rw [isHomeomorph_iff_continuous_bijective]
  refine ⟨?_, d2b_fiberMap_bijective_aux hP⟩
  apply continuous_quot_lift
  apply continuous_quotient_mk'.comp
  exact LinearMap.continuous_of_finiteDimensional _

theorem d2b_homologyF_holomorphic_aux
    {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace B] [ChartedSpace E B] [IsManifold 𝓘(ℂ, E) ω B]
    (X : d2_MarkedPeriodFamily E B g) (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (hA : ∀ b, d2_IsRiemannForm (X.period b) A) :
    (d2b_localSystem B g).IsHolomorphicSubbundle E
      (fun b ↦ d2b_homologyF (X.period b)) := by
  classical
  intro b₁
  · obtain ⟨U, hU, h₁, hUo⟩ := d2v_exists_simplyConnected_nhds E b₁
    let M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℂ :=
      (A.map (Int.cast : ℤ → ℂ))ᵀ
    let σ : Fin g → B → ℂ ⊗[ℤ] (Fin (2 * g) → ℤ) := fun i b ↦
      (d2b_vecZ (2 * g)).symm (M⁻¹ *ᵥ fun k ↦ X.period b i k)
    refine ⟨U, hU, h₁, hUo, g, σ, ?_, ?_⟩
    · intro i
      let L : (Fin g → Fin (2 * g) → ℂ) →ₗ[ℂ]
          ℂ ⊗[ℤ] (Fin (2 * g) → ℤ) :=
        (d2b_vecZ (2 * g)).symm.toLinearMap.comp
          ((Matrix.mulVecLin M⁻¹).comp (LinearMap.proj i))
      let c := ((b2_coord (ℂ ⊗[ℤ] (Fin (2 * g) → ℤ))).toLinearMap.comp L).toContinuousLinearMap
      have hc : (b2_coord (ℂ ⊗[ℤ] (Fin (2 * g) → ℤ)) ∘ σ i) = c ∘ X.period := by
        funext b
        simp [c, L, σ, M]
      show b2_IsHolomorphicOn E ((d2b_localSystem B g).flatCoord U hU ⟨b₁, h₁⟩ (σ i)) U
      refine ((c.contDiff.contMDiff.comp X.holomorphic).contMDiffOn.congr fun b hb ↦ ?_)
      simp only [Function.comp_apply, b2_LatticeLocalSystem.flatCoord, hb, dite_true]
      have ht : ((d2b_localSystem B g).flatTransport U hU ⟨b, hb⟩ ⟨b₁, h₁⟩)
          (σ i b) = σ i b :=
        b2a_const_flatTransport (Fin (2 * g) → ℤ) U hU ⟨b, hb⟩ ⟨b₁, h₁⟩ (σ i b)
      rw [ht]
      exact congrFun hc b
    · intro b hb
      have hAb := hA b
      have hdetA := d2v_det_ne_zero hAb (X.isPeriod b)
      have hdetM : M.det ≠ 0 := by
        dsimp [M]
        rw [Matrix.det_transpose, show A.map (Int.cast : ℤ → ℂ) =
          (Int.castRingHom ℂ).mapMatrix A from rfl, ← RingHom.map_det]
        intro hz
        apply hdetA
        change (A.det : ℂ) = 0 at hz
        have hz' : (A.det : ℂ) = (0 : ℤ) := by simpa using hz
        exact Int.cast_injective hz'
      have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdetM
      have hinv : Function.Injective M⁻¹.mulVec := by
        intro v w hvw
        apply_fun M.mulVec at hvw
        simpa [Matrix.mulVec_mulVec, M.mul_nonsing_inv hunit] using hvw
      have hmem (i : Fin g) : σ i b ∈ d2b_homologyF (X.period b) := by
        have hx : d2_evalBilin (X.period b) (LinearMap.proj i) ∈ d2_hodgeOne (X.period b) :=
          LinearMap.mem_range_self _ _
        obtain ⟨t, ht⟩ := d2v_mem_hodgeOne_repr hAb (X.isPeriod b) hx
        apply (d2b_mem_homologyF_iff (X.isPeriod b) (σ i b)).2
        refine ⟨t, ?_⟩
        simp only [σ, LinearEquiv.apply_symm_apply]
        have ht' := congrArg (d2_vec (2 * g)).symm ht
        have hrow : (fun k ↦ X.period b i k) = M *ᵥ d2v_cplx t (d2v_J (X.isPeriod b) t) := by
          simpa [d2_evalBilin, M] using ht'
        rw [hrow]
        let v := d2v_cplx t (d2v_J (X.isPeriod b) t)
        change M⁻¹ *ᵥ (M *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, M.nonsing_inv_mul hunit, Matrix.one_mulVec]
      have hle : Submodule.span ℂ (Set.range fun i ↦ σ i b) ≤
          d2b_homologyF (X.period b) :=
        Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)
      have hrank := LinearMap.finrank_range_add_finrank_ker
        (d2b_cplxPeriod (X.period b))
      have hrange : LinearMap.range (d2b_cplxPeriod (X.period b)) = ⊤ :=
        LinearMap.range_eq_top.mpr (d2b_cplxPeriod_surjective_aux (X.isPeriod b))
      rw [hrange, finrank_top, Module.finrank_fin_fun,
        show Module.finrank ℂ (ℂ ⊗[ℤ] (Fin (2 * g) → ℤ)) = 2 * g by
          rw [Module.finrank_baseChange, Module.finrank_fin_fun]] at hrank
      have hspanrank : Module.finrank ℂ (Submodule.span ℂ (Set.range fun i ↦ σ i b)) = g := by
        rw [finrank_span_eq_card]
        · simp
        · have hrows : LinearIndependent ℂ (fun i : Fin g ↦ fun k ↦ X.period b i k) := by
            rw [linearIndependent_iff_injective_fintypeLinearCombination]
            convert d2v_rowLin_injective (X.isPeriod b) using 1
            ext a k
            simp [Fintype.linearCombination_apply, d2v_rowLin]
          exact hrows.map' ((d2b_vecZ (2 * g)).symm.toLinearMap.comp
            (Matrix.mulVecLin M⁻¹)) (LinearMap.ker_eq_bot.mpr
              ((d2b_vecZ (2 * g)).symm.injective.comp hinv))
      apply le_antisymm hle
      exact (Submodule.eq_of_le_of_finrank_le hle (by
        rw [hspanrank]
        change Module.finrank ℂ (LinearMap.ker (d2b_cplxPeriod (X.period b))) ≤ g
        omega)).ge
theorem d2b_isPolarizedTorusFamily_aux
    {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace B] [ChartedSpace E B] [IsManifold 𝓘(ℂ, E) ω B]
    (X : d2_MarkedPeriodFamily E B g) (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (hA : ∀ b, d2_IsRiemannForm (X.period b) A) :
    b2_IsPolarizedTorusFamily E (d2b_localSystem B g)
      (fun b ↦ d2b_homologyF (X.period b)) (fun _ ↦ Matrix.toLinearMap₂' ℤ A) := by
  refine ⟨d2b_homologyF_holomorphic_aux X A hA, ?_, ?_, ?_⟩
  · intro b b' γ x y
    rfl
  · exact fun b ↦ d2b_homologyF_isWeightOne_aux (X.isPeriod b)
  · intro b
    exact (d2b_isRiemannForm_iff_aux (X.isPeriod b) A).1 (hA b)

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace B] [ChartedSpace E B]

theorem d2b_totalMap_surjective_aux (X : d2_MarkedPeriodFamily E B g) :
    Function.Surjective (d2b_totalMap X) := by
  rintro ⟨b, t⟩
  let f := d2b_fiberMap (X.period b)
  have hf := d2b_fiberMap_bijective_aux (X.isPeriod b)
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk'_surjective
    (d2_lattice (X.period b)).toAddSubgroup (f t)
  refine ⟨(b, z), ?_⟩
  change (⟨b, Function.invFun f
    (QuotientAddGroup.mk' (d2_lattice (X.period b)).toAddSubgroup z)⟩ :
      b2_totalSpace (d2b_localSystem B g) (fun b ↦ d2b_homologyF (X.period b))) = ⟨b, t⟩
  congr 1
  change Function.invFun f
      (QuotientAddGroup.mk' (d2_lattice (X.period b)).toAddSubgroup z) = t
  rw [hz]
  exact Function.leftInverse_invFun hf.1 t

theorem d2b_totalMap_eq_iff_aux (X : d2_MarkedPeriodFamily E B g)
    (b b' : B) (z z' : Fin g → ℂ) :
    d2b_totalMap X (b, z) = d2b_totalMap X (b', z') ↔
      b = b' ∧ z - z' ∈ d2_lattice (X.period b) := by
  constructor
  · intro h
    have hb : b = b' := congrArg Sigma.fst h
    subst b'
    refine ⟨rfl, ?_⟩
    have ht : Function.invFun (d2b_fiberMap (X.period b))
        (QuotientAddGroup.mk' (d2_lattice (X.period b)).toAddSubgroup z) =
        Function.invFun (d2b_fiberMap (X.period b))
          (QuotientAddGroup.mk' (d2_lattice (X.period b)).toAddSubgroup z') := by
      change (⟨b, Function.invFun (d2b_fiberMap (X.period b))
          (QuotientAddGroup.mk' (d2_lattice (X.period b)).toAddSubgroup z)⟩ :
          b2_totalSpace (d2b_localSystem B g) (fun b ↦ d2b_homologyF (X.period b))) =
        ⟨b, Function.invFun (d2b_fiberMap (X.period b))
          (QuotientAddGroup.mk' (d2_lattice (X.period b)).toAddSubgroup z')⟩ at h
      exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
    apply_fun d2b_fiberMap (X.period b) at ht
    have hsurj := (d2b_fiberMap_bijective_aux (X.isPeriod b)).2
    rw [Function.rightInverse_invFun hsurj, Function.rightInverse_invFun hsurj] at ht
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_iff_sub_mem] at ht
    exact ht
  · rintro ⟨hb, hz⟩
    subst b'
    change (⟨b, Function.invFun (d2b_fiberMap (X.period b))
        (QuotientAddGroup.mk' (d2_lattice (X.period b)).toAddSubgroup z)⟩ :
        b2_totalSpace (d2b_localSystem B g) (fun b ↦ d2b_homologyF (X.period b))) =
      ⟨b, Function.invFun (d2b_fiberMap (X.period b))
        (QuotientAddGroup.mk' (d2_lattice (X.period b)).toAddSubgroup z')⟩
    congr 1
    apply congrArg (Function.invFun (d2b_fiberMap (X.period b)))
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_iff_sub_mem]
    exact hz

theorem d2b_elliptic_homologyF_eq_stdF_aux :
    d2b_homologyF (d2_ellipticPeriod Complex.I) = b2_stdF := by
  apply Submodule.ext
  intro x
  have hperiod : d2b_cplxPeriod (d2_ellipticPeriod Complex.I) x 0 =
      b2a_pi x 0 + Complex.I * b2a_pi x 1 := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c n =>
        simp [d2b_cplxPeriod, d2_markingMap,
          Fintype.linearCombination_apply, Fin.sum_univ_two, b2a_pi_tmul,
          d2_column, d2_ellipticPeriod]
        ring
    | add x y hx hy => simp [map_add, hx, hy]; ring
  rw [d2b_homologyF, LinearMap.mem_ker, b2_stdF, Submodule.mem_span_singleton]
  constructor
  · intro hx
    have hcoord : b2a_pi x 1 = Complex.I * b2a_pi x 0 := by
      have h := congrFun hx 0
      rw [hperiod] at h
      have h' : b2a_pi x 0 + Complex.I * b2a_pi x 1 = 0 := by simpa using h
      calc
        b2a_pi x 1 = -Complex.I * (Complex.I * b2a_pi x 1) := by
          rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
        _ = -Complex.I * (-b2a_pi x 0) := by
          rw [eq_neg_of_add_eq_zero_right h']
        _ = Complex.I * b2a_pi x 0 := by ring
    refine ⟨b2a_pi x 0, b2a_pi.injective ?_⟩
    rw [map_smul, b2a_stdVec_pi]
    ext i
    fin_cases i
    · simp
    · simpa [hcoord, mul_comm]
  · rintro ⟨c, rfl⟩
    apply funext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [hperiod]
    simp [map_smul, b2a_pi_tmul, Complex.I_mul_I]
    linear_combination c * Complex.I_mul_I

theorem d2b_zero_cplxPeriod_not_surjective_aux :
    ¬ Function.Surjective (d2b_cplxPeriod (0 : Fin 1 → Fin 2 → ℂ)) := by
  intro h
  obtain ⟨x, hx⟩ := h (fun _ ↦ 1)
  have hm : d2_markingMap (0 : Fin 1 → Fin 2 → ℂ) = 0 := by
    ext n i
    simp [d2_markingMap, d2_column]
  have hz : d2b_cplxPeriod (0 : Fin 1 → Fin 2 → ℂ) x = 0 := by
    rw [d2b_cplxPeriod, hm]
    simp
  rw [hz] at hx
  have := congrFun hx 0
  simp at this

theorem d2b_zero_homologyF_not_isWeightOne_aux :
    ¬ b2_IsWeightOne (Fin 2 → ℤ) (d2b_homologyF (0 : Fin 1 → Fin 2 → ℂ)) := by
  have hm : d2_markingMap (0 : Fin 1 → Fin 2 → ℂ) = 0 := by
    ext n i
    simp [d2_markingMap, d2_column]
  have hF : d2b_homologyF (0 : Fin 1 → Fin 2 → ℂ) = ⊤ := by
    rw [d2b_homologyF, d2b_cplxPeriod, hm]
    simp
  have hc : b2_conjSubmodule (Fin 2 → ℤ)
      (⊤ : Submodule ℂ (ℂ ⊗[ℤ] (Fin 2 → ℤ))) = ⊤ := by
    apply top_unique
    intro x _
    apply Submodule.subset_span
    exact ⟨b2_conj _ x, Submodule.mem_top, b2a_conj_conj x⟩
  rw [b2_IsWeightOne, hF, hc]
  intro h
  have htb : (⊤ : Submodule ℂ (ℂ ⊗[ℤ] (Fin 2 → ℤ))) = ⊥ := by
    simpa using h.inf_eq_bot
  have hv : b2a_stdVec = 0 := by
    have : b2a_stdVec ∈ (⊥ : Submodule ℂ (ℂ ⊗[ℤ] (Fin 2 → ℤ))) := by
      rw [← htb]
      exact Submodule.mem_top
    simpa using this
  have hv' := congrArg b2a_pi hv
  rw [b2a_stdVec_pi] at hv'
  have := congrFun hv' 0
  simp at this

theorem d2b_neg_stdForm_not_isRiemannForm_aux :
    ¬ b2_IsRiemannForm (Fin 2 → ℤ) b2_stdF (-b2_stdForm) := by
  intro h
  have hv0 : b2a_stdVec ≠ 0 := by
    intro hv
    have hv' := congrArg b2a_pi hv
    rw [b2a_stdVec_pi] at hv'
    have := congrFun hv' 0
    simp at this
  have hv : (-b2_stdForm).baseChange ℂ b2a_stdVec (b2_conj _ b2a_stdVec) =
      2 * Complex.I := by
    rw [b2a_stdVec_conj]
    simp only [map_add, LinearMap.add_apply, LinearMap.BilinForm.baseChange_tmul,
      LinearMap.neg_apply, b2a_stdForm_apply]
    simp
    ring
  have hp := h.positive b2a_stdVec (Submodule.mem_span_singleton_self _) hv0
  rw [hv] at hp
  norm_num [Complex.I_mul_I] at hp

end HodgeLean.Foundations.Program
