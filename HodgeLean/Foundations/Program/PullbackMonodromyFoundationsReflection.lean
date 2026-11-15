import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsReflectionCheck
import HodgeLean.Foundations.Program.PullbackMonodromy

set_option maxHeartbeats 400000

/-! # The reflection class of `r₁` in G32

An element of `b4b_Group` whose matrix is linearly conjugate to that of `r₁` is a group conjugate
of `r₁`. The linear conjugacy makes `g - 1` of rank one with eigenvalue `ω` on its image; the
invariant form `b65t_H` then fixes `g` from one moved column, and the kernel checks of
`PullbackMonodromyFoundationsReflectionCheck` compare the result with the forty conjugates.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Matrix HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem b65t_operator_apply (M : Matrix (Fin 4) (Fin 4) ℂ) (x : Fin 4 → ℂ) :
    b65r_operator M x = M *ᵥ x := rfl

/-- Conjugation by an operator carries a rank-one perturbation of the identity to another. -/
theorem b65t_rankOne_conj_op (M R : Matrix (Fin 4) (Fin 4) ℂ)
    (K : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hK : b65r_operator M = (K : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) * b65r_operator R * ↑(K⁻¹))
    (a : Fin 4 → ℂ) (φ : (Fin 4 → ℂ) →ₗ[ℂ] ℂ) (hR : ∀ x, R *ᵥ x = x + φ x • a) :
    ∃ (u : Fin 4 → ℂ) (ψ : (Fin 4 → ℂ) →ₗ[ℂ] ℂ), (∀ x, M *ᵥ x = x + ψ x • u) ∧ ψ u = φ a := by
  let Ki : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) := ↑(K⁻¹)
  refine ⟨(K : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) a, φ.comp (Ki : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ)),
    fun x ↦ ?_, ?_⟩
  · have h1 : (K : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (Ki x) = x := by
      change ((K * K⁻¹ : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ) : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) x = x
      rw [mul_inv_cancel]; rfl
    rw [← b65t_operator_apply, hK]
    change (K : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (b65r_operator R (Ki x)) = _
    rw [b65t_operator_apply, hR, map_add, map_smul, h1]
    rfl
  · have h2 : Ki ((K : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) a) = a := by
      change ((K⁻¹ * K : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ) : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) a = a
      rw [inv_mul_cancel]; rfl
    change φ (Ki _) = _
    rw [h2]

/-- Conjugation by an invertible matrix carries a rank-one perturbation of the identity to another. -/
theorem b65t_rankOne_conj_mat (X Y Q Q' : Matrix (Fin 4) (Fin 4) ℂ) (hQ : Q' * Q = 1)
    (hQ' : Q * Q' = 1) (hX : X = Q * Y * Q')
    (a : Fin 4 → ℂ) (φ : (Fin 4 → ℂ) →ₗ[ℂ] ℂ) (hY : ∀ x, Y *ᵥ x = x + φ x • a) :
    ∃ (u : Fin 4 → ℂ) (ψ : (Fin 4 → ℂ) →ₗ[ℂ] ℂ), (∀ x, X *ᵥ x = x + ψ x • u) ∧ ψ u = φ a := by
  refine ⟨Q *ᵥ a, φ.comp (Matrix.mulVecLin Q'), fun x ↦ ?_, ?_⟩
  · rw [hX, ← mulVec_mulVec, ← mulVec_mulVec, hY, mulVec_add, mulVec_smul, mulVec_mulVec, hQ',
      one_mulVec]
    rfl
  · change φ (Q' *ᵥ (Q *ᵥ a)) = _
    rw [mulVec_mulVec, hQ, one_mulVec]

/-- A unitary rank-one perturbation with eigenvalue `ω` on its image is the reflection formula. -/
theorem b65t_unitary_reflection (A Hc : Matrix (Fin 4) (Fin 4) ℂ) (ω : ℂ)
    (hω : ω * star ω = 1) (hU : Aᴴ * Hc * A = Hc) (v : Fin 4 → ℂ) (hv : A *ᵥ v = ω • v)
    (y : Fin 4 → ℂ) (l : ℂ) (hy : A *ᵥ y = y + l • v) :
    (star v ⬝ᵥ (Hc *ᵥ v)) * l = (ω - 1) * (star v ⬝ᵥ (Hc *ᵥ y)) := by
  have key : star (A *ᵥ v) ⬝ᵥ (Hc *ᵥ (A *ᵥ y)) = star v ⬝ᵥ (Hc *ᵥ y) := by
    rw [star_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul, vecMul_vecMul, ← Matrix.mul_assoc, hU, dotProduct_mulVec]
  rw [hv, hy, star_smul, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul,
    smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul, smul_eq_mul] at key
  have : star ω = ω⁻¹ := by
    have hω0 : ω ≠ 0 := by rintro rfl; simp at hω
    field_simp; rw [mul_comm]; exact hω
  rw [this] at key
  have hω0 : ω ≠ 0 := by rintro rfl; simp at hω
  field_simp at key
  linear_combination key


local notation "ev" => HurwitzPrymRex_ev g32h_omega
local notation "evM" => HurwitzPrymRex_evM g32h_omega

theorem b65t_star_omega : star g32h_omega = g32h_omega ^ 2 := by
  have hw := g32h_omega_sq_add
  have hs : star g32h_omega ^ 2 + star g32h_omega + 1 = 0 := by
    have := congrArg star hw
    simp only [star_add, star_pow, star_one, star_zero] at this
    exact this
  have hprod : (star g32h_omega - g32h_omega) * (star g32h_omega + g32h_omega + 1) = 0 := by
    linear_combination hs - hw
  rcases mul_eq_zero.mp hprod with h | h
  · exfalso
    have hre : g32h_omega = ((g32h_omega.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · have := congrArg Complex.im (sub_eq_zero.mp h)
        simp at this
        simp; linarith
    rw [hre] at hw
    have h2 : ((g32h_omega.re ^ 2 + g32h_omega.re + 1 : ℝ) : ℂ) = 0 := by push_cast; exact hw
    have h3 : g32h_omega.re ^ 2 + g32h_omega.re + 1 = 0 := by exact_mod_cast h2
    nlinarith [sq_nonneg (g32h_omega.re + 1 / 2)]
  · linear_combination h - hw

theorem b65t_omega_unit : g32h_omega * star g32h_omega = 1 := by
  rw [b65t_star_omega]
  linear_combination (g32h_omega - 1) * g32h_omega_sq_add

theorem b65t_ev_sig (x : HurwitzPrymRex_Zw) : ev (b65t_sig x) = star (ev x) := by
  have hs : ∀ n : ℤ, star (n : ℂ) = n := fun n ↦ by simp
  simp only [HurwitzPrymRex_ev, b65t_sig, star_add, star_mul', hs, b65t_star_omega]
  push_cast
  linear_combination (-(x.om : ℂ)) * g32h_omega_sq_add

theorem b65t_evM_star (A : HurwitzPrymRex_Mat) : evM (b65t_star A) = (evM A)ᴴ := by
  ext i j
  simp [HurwitzPrymRex_evM, b65t_star, conjTranspose_apply, b65t_ev_sig]

theorem b65t_ev_mv (A : HurwitzPrymRex_Mat) (v : Fin 4 → HurwitzPrymRex_Zw) :
    (fun i ↦ ev (b65t_mv A v i)) = evM A *ᵥ (fun i ↦ ev (v i)) := by
  funext i
  simp only [b65t_mv, HurwitzPrymRex_ev_add, HurwitzPrymRex_ev_mul g32h_omega_sq_add, mulVec,
    dotProduct, Fin.sum_univ_four, HurwitzPrymRex_evM, Matrix.of_apply]
  ring

theorem b65t_ew_eq (w : List (Fin 4)) : b65t_ew w = b65s_ew w := rfl

theorem b65t_exists_word (g : b4b_Group) : ∃ w : List (Fin 4), g = b65s_gw w := by
  have hind : ∀ (x : Matrix (Fin 4) (Fin 4) ℂ), x ∈ Submonoid.closure
        {g32R1 g32h_omega, g32R2 g32h_omega, g32X g32h_omega, g32Y g32h_omega} →
      ∃ hx : x ∈ g32h_G, ∃ w : List (Fin 4), (⟨x, hx⟩ : b4b_Group) = b65s_gw w := by
    intro x hcl
    induction hcl using Submonoid.closure_induction with
    | mem x hmem =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl
        · exact ⟨(b4b_generators 0).property, [0], by simp [b65s_gw]; rfl⟩
        · exact ⟨(b4b_generators 1).property, [1], by simp [b65s_gw]; rfl⟩
        · exact ⟨(b4b_generators 2).property, [2], by simp [b65s_gw]; rfl⟩
        · exact ⟨(b4b_generators 3).property, [3], by simp [b65s_gw]; rfl⟩
    | one => exact ⟨one_mem _, [], rfl⟩
    | mul x y hx hy ihx ihy =>
        rcases ihx with ⟨hxG, u, hu⟩
        rcases ihy with ⟨hyG, v, hv⟩
        refine ⟨mul_mem hxG hyG, u ++ v, ?_⟩
        rw [b65s_gw_append, ← hu, ← hv]
        rfl
  rcases hind g.val g.property with ⟨_, w, hw⟩
  exact ⟨w, hw⟩


theorem b65t_vbeq_sound {u v : Fin 4 → HurwitzPrymRex_Zw} (h : b65t_vbeq u v = true) : u = v := by
  simp only [b65t_vbeq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  funext i
  fin_cases i <;> assumption

theorem b65t_vbeq_self (u : Fin 4 → HurwitzPrymRex_Zw) : b65t_vbeq u u = true := by
  simp [b65t_vbeq]

theorem b65t_vmem_sound {v : Fin 4 → HurwitzPrymRex_Zw} {L : List (Fin 4 → HurwitzPrymRex_Zw)}
    (h : b65t_vmem v L = true) : v ∈ L := by
  obtain ⟨c, hc, hvc⟩ := List.any_eq_true.mp h
  rwa [b65t_vbeq_sound hvc]

theorem b65t_vmem_of_mem {v : Fin 4 → HurwitzPrymRex_Zw} {L : List (Fin 4 → HurwitzPrymRex_Zw)}
    (h : v ∈ L) : b65t_vmem v L = true :=
  List.any_eq_true.mpr ⟨v, h, b65t_vbeq_self v⟩

theorem b65t_unitary (w : List (Fin 4)) :
    (evM (b65t_ew w))ᴴ * evM b65t_H * evM (b65t_ew w) = evM b65t_H := by
  induction w with
  | nil =>
      change (evM HurwitzPrymRex_mone)ᴴ * _ * evM HurwitzPrymRex_mone = _
      rw [HurwitzPrymRex_evM_mone, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  | cons i w ih =>
      have hg := congrArg evM (HurwitzPrymRex_mbeq_sound (b65t_H_invariant i))
      rw [HurwitzPrymRex_evM_mmul g32h_omega_sq_add, HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
        b65t_evM_star] at hg
      change (evM (HurwitzPrymRex_mmul (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne i)
        (b65t_ew w)))ᴴ * _ * evM (HurwitzPrymRex_mmul _ (b65t_ew w)) = _
      rw [HurwitzPrymRex_evM_mmul g32h_omega_sq_add, conjTranspose_mul]
      calc _ = (evM (b65t_ew w))ᴴ * ((evM (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne i))ᴴ *
              (evM b65t_H * evM (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne i))) *
            evM (b65t_ew w) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hg, ih]

theorem b65t_col_mem (w : List (Fin 4)) (j : Fin 4) :
    (fun r ↦ b65t_ew w r j) ∈ b65t_orbit := by
  induction w with
  | nil =>
      have : (fun r ↦ b65t_ew [] r j) = b65t_e j := rfl
      rw [this]
      exact b65t_vmem_sound (b65t_basis_mem j)
  | cons i w ih =>
      have : (fun r ↦ b65t_ew (i :: w) r j) =
          b65t_mv (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne i) (fun r ↦ b65t_ew w r j) := rfl
      rw [this]
      have h := List.all_eq_true.mp b65t_orbit_closed _ ih
      exact b65t_vmem_sound (List.all_eq_true.mp h i (List.mem_finRange i))



theorem b65t_dvd_mul (h y : HurwitzPrymRex_Zw) :
    b65t_dvd h (HurwitzPrymRex_Zw.mul h y) = true := by
  have e1 : (HurwitzPrymRex_Zw.mul (HurwitzPrymRex_Zw.mul h y) (b65t_sig h)).re =
      y.re * (HurwitzPrymRex_Zw.mul h (b65t_sig h)).re := by
    simp only [HurwitzPrymRex_Zw.mul, b65t_sig]; ring
  have e2 : (HurwitzPrymRex_Zw.mul (HurwitzPrymRex_Zw.mul h y) (b65t_sig h)).om =
      y.om * (HurwitzPrymRex_Zw.mul h (b65t_sig h)).re := by
    simp only [HurwitzPrymRex_Zw.mul, b65t_sig]; ring
  simp only [b65t_dvd, e1, e2, Int.mul_emod_left, beq_self_eq_true, Bool.and_self]

theorem b65t_ev_z (a b : ℤ) : ev (z a b) = a + b * g32h_omega := rfl

theorem b65t_first_rankOne : ∀ x : Fin 4 → ℂ,
    evM (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne 0) *ᵥ x =
      x + (![1, 0, 0, -1] ⬝ᵥ x) • ![g32h_omega, -1 - g32h_omega, 0, 1] := by
  intro x
  funext i
  fin_cases i <;>
    simp [mulVec, dotProduct, Fin.sum_univ_four, HurwitzPrymRex_evM, HurwitzPrymRex_nth,
      HurwitzPrymRex_g32SOne, HurwitzPrymRex_ev] <;> ring

theorem b65t_ev_om : ev (z (-1) 1) = g32h_omega - 1 := by
  simp [HurwitzPrymRex_ev]; ring

theorem b65t_omega_ne_one : g32h_omega ≠ 1 := by
  intro h
  have := g32h_omega_sq_add
  rw [h] at this
  norm_num at this

theorem b65t_conj_eq (X : Matrix (Fin 4) (Fin 4) ℂ) :
    HurwitzPrymRex_g32conj X = HurwitzPrymRex_g32P * X * HurwitzPrymRex_g32Pinv := rfl

theorem b65t_reflection_class_proof (g : b4b_Group)
    (K : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hK : b65r_operator (b4b_toMatrix g) =
      (K : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
        b65r_operator (b4b_toMatrix (b4b_generators 0)) * ↑(K⁻¹)) :
    ∃ h : b4b_Group, h * b4b_generators 0 * h⁻¹ = g := by
  obtain ⟨w, rfl⟩ := b65t_exists_word g
  set N := b65t_ew w with hN
  set A := evM N with hA
  set P := HurwitzPrymRex_g32P
  set Pi' := HurwitzPrymRex_g32Pinv
  have hM : b4b_toMatrix (b65s_gw w) = P * A * Pi' := by
    rw [b65s_gw_matrix, ← b65t_ew_eq, b65t_conj_eq]
  have hR : b4b_toMatrix (b4b_generators 0) =
      P * evM (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne 0) * Pi' := by
    rw [← b65t_conj_eq, HurwitzPrymRex_g32_conj0]; rfl
  let φ : (Fin 4 → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x ↦ ![1, 0, 0, -1] ⬝ᵥ x
      map_add' := fun x y ↦ dotProduct_add _ x y
      map_smul' := fun c x ↦ by simp [dotProduct_smul] }
  obtain ⟨u1, ψ1, h1, e1⟩ := b65t_rankOne_conj_mat _ _ P Pi' HurwitzPrymRex_g32_Pinv_P
    HurwitzPrymRex_g32_P_Pinv hR _ φ b65t_first_rankOne
  obtain ⟨u2, ψ2, h2, e2⟩ := b65t_rankOne_conj_op _ _ K hK u1 ψ1 h1
  have hA' : A = Pi' * b4b_toMatrix (b65s_gw w) * P := by
    have hPP : Pi' * P = 1 := HurwitzPrymRex_g32_Pinv_P
    rw [hM, show Pi' * (P * A * Pi') * P = (Pi' * P) * A * (Pi' * P) by
      simp only [Matrix.mul_assoc], hPP, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨u, ψ, hAu, e3⟩ := b65t_rankOne_conj_mat _ _ Pi' P HurwitzPrymRex_g32_P_Pinv
    HurwitzPrymRex_g32_Pinv_P hA' u2 ψ2 h2
  have hψu : ψ u = g32h_omega - 1 := by
    rw [e3, e2, e1]
    simp [φ, dotProduct, Fin.sum_univ_four]
    ring
  -- a column moved by `A`
  have hex : ∃ j : Fin 4, ψ (Pi.single j 1) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : ψ u = 0 := by
      rw [← Finset.univ_sum_single u, map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [show (Pi.single i (u i) : Fin 4 → ℂ) = u i • (Pi.single i 1 : Fin 4 → ℂ) by
        funext l; by_cases hl : l = i <;> simp [hl], map_smul, hcon, smul_zero]
    rw [hψu, sub_eq_zero] at this
    exact b65t_omega_ne_one this
  obtain ⟨j, hj⟩ := hex
  set μ := ψ (Pi.single j 1)
  set c : Fin 4 → HurwitzPrymRex_Zw := fun r ↦ N r j with hc
  have hcmem : c ∈ b65t_orbit := b65t_col_mem w j
  set vI : Fin 4 → HurwitzPrymRex_Zw :=
    fun i ↦ HurwitzPrymRex_Zw.add (c i) (HurwitzPrymRex_Zw.mul (z (-1) 0) (b65t_e j i)) with hvI
  set v : Fin 4 → ℂ := fun i ↦ ev (vI i) with hv
  have hev_e : ∀ k i, ev (b65t_e k i) = (Pi.single k (1 : ℂ) : Fin 4 → ℂ) i := by
    intro k i
    by_cases hik : i = k
    · subst hik; simp [b65t_e, HurwitzPrymRex_ev]
    · simp [b65t_e, hik, HurwitzPrymRex_ev]
  have hcol : ∀ k i, A i k = (Pi.single k (1 : ℂ) : Fin 4 → ℂ) i + ψ (Pi.single k 1) * u i := by
    intro k i
    have := congrFun (hAu (Pi.single k 1)) i
    rw [mulVec_single_one] at this
    simpa using this
  have hvμ : v = μ • u := by
    funext i
    simp only [hv, hvI, HurwitzPrymRex_ev_add, HurwitzPrymRex_ev_mul g32h_omega_sq_add, hev_e,
      hc, Pi.smul_apply, smul_eq_mul]
    change A i j + _ = _
    rw [hcol j i, b65t_ev_z]
    push_cast
    ring
  have hAv : A *ᵥ v = g32h_omega • v := by
    rw [hvμ, mulVec_smul, hAu, hψu]
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hμ0 : μ ≠ 0 := hj
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [map_zero] at hψu
    exact b65t_omega_ne_one (sub_eq_zero.mp hψu.symm)
  have hcol' : ∀ k, A *ᵥ Pi.single k 1 = Pi.single k 1 + (ψ (Pi.single k 1) / μ) • v := by
    intro k
    rw [hAu, hvμ, smul_smul, div_mul_cancel₀ _ hμ0]
  -- the unitary relation
  set Hc := evM b65t_H
  have hrel : ∀ k, (star v ⬝ᵥ (Hc *ᵥ v)) * (ψ (Pi.single k 1) / μ) =
      (g32h_omega - 1) * (star v ⬝ᵥ (Hc *ᵥ Pi.single k 1)) := fun k ↦
    b65t_unitary_reflection A Hc g32h_omega b65t_omega_unit (b65t_unitary w) v hAv _ _ (hcol' k)
  have hevbeta0 : ∀ k, ev (b65t_beta vI k) = ∑ i, star (v i) * Hc i k := by
    intro k
    simp only [b65t_beta, HurwitzPrymRex_ev_add, HurwitzPrymRex_ev_mul g32h_omega_sq_add,
      b65t_ev_sig, Fin.sum_univ_four, hv, Hc, HurwitzPrymRex_evM, Matrix.of_apply]
    ring
  have hbeta_dot : ∀ k, star v ⬝ᵥ (Hc *ᵥ Pi.single k 1) = ∑ i, star (v i) * Hc i k := by
    intro k
    simp [dotProduct, mulVec, Pi.single_apply]
  have hevh : ev (b65t_hval vI) = star v ⬝ᵥ (Hc *ᵥ v) := by
    simp only [b65t_hval, HurwitzPrymRex_ev_add, HurwitzPrymRex_ev_mul g32h_omega_sq_add,
      hevbeta0]
    simp only [dotProduct, mulVec, Fin.sum_univ_four, Pi.star_apply, hv]
    ring
  have hRN : ∀ i k, b65t_R vI i k = HurwitzPrymRex_Zw.mul (b65t_hval vI) (N i k) := by
    intro i k
    apply HurwitzPrymRex_ev_injective g32h_omega_sq_add
    rw [HurwitzPrymRex_ev_mul g32h_omega_sq_add]
    change ev (b65t_R vI i k) = ev (b65t_hval vI) * A i k
    have hr := hrel k
    rw [hbeta_dot] at hr
    field_simp at hr
    have hRi : ev (b65t_R vI i k) = (if i = k then ev (b65t_hval vI) else 0) +
        (g32h_omega - 1) * (v i * ∑ i, star (v i) * Hc i k) := by
      unfold b65t_R
      split_ifs
      · rw [HurwitzPrymRex_ev_add, HurwitzPrymRex_ev_mul g32h_omega_sq_add,
          HurwitzPrymRex_ev_mul g32h_omega_sq_add, b65t_ev_om, hevbeta0]
      · rw [HurwitzPrymRex_ev_add, HurwitzPrymRex_ev_mul g32h_omega_sq_add,
          HurwitzPrymRex_ev_mul g32h_omega_sq_add, b65t_ev_z, b65t_ev_z, hevbeta0]
        push_cast; ring
    rw [hRi, hcol k i, hevh, show v i = μ * u i from congrFun hvμ i]
    by_cases hik : i = k
    · subst hik
      simp only [ite_true, Pi.single_eq_same]
      linear_combination (-(u i)) * hr
    · simp only [hik, ite_false, Pi.single_eq_of_ne hik]
      linear_combination (-(u i)) * hr
  -- the kernel check for this column
  have hcand := List.all_eq_true.mp
    (List.all_eq_true.mp b65t_columns_check j (List.mem_finRange j)) c hcmem
  have hce : b65t_vbeq c (b65t_e j) = false := by
    by_contra hb
    have heq := b65t_vbeq_sound (Bool.not_eq_false _ ▸ hb)
    have : v = 0 := by
      funext i
      simp only [hv, hvI, heq, HurwitzPrymRex_ev_add, HurwitzPrymRex_ev_mul g32h_omega_sq_add,
        b65t_ev_z, Pi.zero_apply]
      push_cast; ring
    rw [hvμ] at this
    exact hu0 ((smul_eq_zero.mp this).resolve_left hμ0)
  simp only [b65t_columnOk, hce, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, Bool.or_eq_true] at hcand
  obtain ⟨hh0, hcase⟩ := hcand
  have hdvd : b65t_allDvd (b65t_hval vI) (b65t_R vI) = true := by
    simp only [b65t_allDvd, List.all_eq_true, List.mem_finRange, forall_const, hRN]
    intro i k
    exact b65t_dvd_mul _ _
  rcases hcase with hnd | hany
  · exact absurd hdvd (by simpa using hnd)
  obtain ⟨t, ht, hteq⟩ := List.any_eq_true.mp hany
  have hRC := HurwitzPrymRex_mbeq_sound hteq
  have hevh0 : ev (b65t_hval vI) ≠ 0 := by
    intro h0
    apply hh0
    apply HurwitzPrymRex_ev_injective g32h_omega_sq_add
    rw [h0]; simp [HurwitzPrymRex_ev]
  have hAC : A = evM t.1 := by
    ext i k
    have := congrArg ev (congrFun (congrFun hRC i) k)
    rw [hRN] at this
    simp only [b65t_smul, HurwitzPrymRex_ev_mul g32h_omega_sq_add] at this
    exact mul_left_cancel₀ hevh0 this
  have hw := List.all_eq_true.mp b65t_class_words t ht
  simp only [Bool.and_eq_true] at hw
  have hw1 := HurwitzPrymRex_mbeq_sound hw.1
  have hw2 := HurwitzPrymRex_mbeq_sound hw.2
  have hg : b65s_gw w = b65s_gw (t.2.1 ++ 0 :: t.2.2) := by
    apply Subtype.val_injective
    change b4b_toMatrix _ = b4b_toMatrix _
    rw [hM, hAC, b65s_gw_matrix, ← b65t_ew_eq, hw1, b65t_conj_eq]
  have hone : b65s_gw t.2.1 * b65s_gw t.2.2 = 1 := by
    rw [← b65s_gw_append]
    apply Subtype.val_injective
    change b4b_toMatrix _ = b4b_toMatrix 1
    rw [b65s_gw_matrix, ← b65t_ew_eq, hw2, HurwitzPrymRex_evM_mone, map_one, map_one]
  refine ⟨b65s_gw t.2.1, ?_⟩
  have hq : b65s_gw t.2.2 = (b65s_gw t.2.1)⁻¹ := eq_inv_of_mul_eq_one_right hone
  rw [hg, b65s_gw_append, show b65s_gw (0 :: t.2.2) = b4b_generators 0 * b65s_gw t.2.2 by
    simp [b65s_gw], hq, mul_assoc]

end HodgeLean.Foundations.Program
