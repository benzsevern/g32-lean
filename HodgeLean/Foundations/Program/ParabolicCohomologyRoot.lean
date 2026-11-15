import HodgeLean.Foundations.Program.ParabolicCohomologyLemmas
import HodgeLean.Foundations.Program.ParabolicCohomologyRootK
import HodgeLean.Papers.PapersArithmetic

/-! # The G32 root over `ℂ` and over `K`, compared through `hp_embed`

The embedding `hp_embed` sends `ζ` to `g32h_omega` and commutes with `star`; the printed generators,
the root words and the certificate entries commute with any ring map of fields; the matrix
realization of `b4b_root` is the root words at `g32h_omega`. With the explicit matrices of
`ParabolicCohomologyRootK`, this gives product one, unitarity, the local fixed dimensions and the
vanishing common fixed space over `ℂ` and over `K`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Matrix HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem hp_embed_zeta_eq : hp_embed pc_zeta = g32h_omega := by
  have hom : hp_embed QuadraticAlgebra.omega = Complex.I * (Real.sqrt 3 : ℂ) := by
    simp [hp_embed]
  have h1 : hp_embed pc_zeta = (-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2 := by
    rw [pc_zeta, map_div₀, map_add, map_neg, map_one, hom, map_ofNat]
  have harg : 2 * Real.pi * Complex.I / 3 = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hθ : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h1, g32h_omega, harg]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, hθ, Real.cos_pi_sub, Real.cos_pi_div_three]
    simp
    norm_num
  · rw [Complex.exp_ofReal_mul_I_im, hθ, Real.sin_pi_sub, Real.sin_pi_div_three]
    simp

theorem hp_embed_star (x : hp_K) : hp_embed (star x) = star (hp_embed x) := by
  simp only [hp_embed, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    QuadraticAlgebra.lift_apply_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
    zero_mul, add_zero]
  simp [Rat.smul_def]

section map

variable {K L : Type*} [Field K] [Field L] (f : K →+* L)

theorem hp_genOver_map (ω : K) (k : Fin 4) : (hp_genOver ω k).map f = hp_genOver (f ω) k := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [hp_genOver, g32R1, g32R2, g32X, g32Y, map_div₀, map_ofNat]

theorem hp_word_map (ω : K) (w : List (Fin 4)) :
    ((w.map (hp_genOver ω)).prod).map f = (w.map (hp_genOver (f ω))).prod := by
  rw [← RingHom.mapMatrix_apply, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  exact hp_genOver_map f ω k

theorem hp_reflOver_map (ω : K) (w : List (Fin 4)) :
    (hp_reflOver ω w).map f = hp_reflOver (f ω) w := by
  simp only [hp_reflOver]
  rw [← RingHom.mapMatrix_apply, map_mul, map_mul, RingHom.mapMatrix_apply,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, pc_map_inv, hp_word_map]
  have := hp_genOver_map f ω 0
  simp only [hp_genOver, Matrix.cons_val_zero] at this
  rw [this]

theorem hp_rootTupleOver_map (ω : K) (j : Fin 13) :
    (hp_rootTupleOver ω j).map f = hp_rootTupleOver (f ω) j := by
  have h0 : (g32R1 ω).map f = g32R1 (f ω) := hp_genOver_map f ω 0
  have h1 : (g32R2 ω).map f = g32R2 (f ω) := hp_genOver_map f ω 1
  have h2 : (g32X ω).map f = g32X (f ω) := hp_genOver_map f ω 2
  have hr : ∀ w, ((hp_reflOver ω w)⁻¹).map f = (hp_reflOver (f ω) w)⁻¹ := fun w => by
    rw [pc_map_inv, hp_reflOver_map]
  fin_cases j
  · exact h0
  · change ((g32R1 ω)⁻¹).map f = (g32R1 (f ω))⁻¹
    rw [pc_map_inv, h0]
  · change ((g32R2 ω)⁻¹).map f = (g32R2 (f ω))⁻¹
    rw [pc_map_inv, h1]
  · exact h1
  · exact hp_reflOver_map f ω _
  · exact hr _
  · exact hp_reflOver_map f ω _
  · exact hr _
  · exact hp_reflOver_map f ω _
  · exact hr _
  · exact hp_reflOver_map f ω _
  · exact hr _
  · change (g32X ω ^ 2).map f = g32X (f ω) ^ 2
    rw [← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply, h2]

theorem hp_certOver_map_0 (ω : K) (j : Fin 13) (k : Fin 4) :
    f (hp_certOver ω 0 j k) = hp_certOver (f ω) 0 j k := by
  fin_cases j <;> fin_cases k <;> simp [hp_certOver, map_div₀, map_ofNat]

theorem hp_certOver_map_1 (ω : K) (j : Fin 13) (k : Fin 4) :
    f (hp_certOver ω 1 j k) = hp_certOver (f ω) 1 j k := by
  fin_cases j <;> fin_cases k <;> simp [hp_certOver, map_div₀, map_ofNat]

theorem hp_certOver_map_2 (ω : K) (j : Fin 13) (k : Fin 4) :
    f (hp_certOver ω 2 j k) = hp_certOver (f ω) 2 j k := by
  fin_cases j <;> fin_cases k <;> simp [hp_certOver, map_div₀, map_ofNat]

theorem hp_certOver_map_3 (ω : K) (j : Fin 13) (k : Fin 4) :
    f (hp_certOver ω 3 j k) = hp_certOver (f ω) 3 j k := by
  fin_cases j <;> fin_cases k <;> simp [hp_certOver, map_div₀, map_ofNat]

theorem hp_certOver_map_4 (ω : K) (j : Fin 13) (k : Fin 4) :
    f (hp_certOver ω 4 j k) = hp_certOver (f ω) 4 j k := by
  fin_cases j <;> fin_cases k <;> simp [hp_certOver, map_div₀, map_ofNat]

theorem hp_certOver_map_5 (ω : K) (j : Fin 13) (k : Fin 4) :
    f (hp_certOver ω 5 j k) = hp_certOver (f ω) 5 j k := by
  fin_cases j <;> fin_cases k <;> simp [hp_certOver, map_div₀, map_ofNat]

theorem hp_certOver_map (ω : K) (a : Fin 6) (j : Fin 13) (k : Fin 4) :
    f (hp_certOver ω a j k) = hp_certOver (f ω) a j k := by
  fin_cases a
  · exact hp_certOver_map_0 f ω j k
  · exact hp_certOver_map_1 f ω j k
  · exact hp_certOver_map_2 f ω j k
  · exact hp_certOver_map_3 f ω j k
  · exact hp_certOver_map_4 f ω j k
  · exact hp_certOver_map_5 f ω j k

theorem hp_g32H0_map (ω : K) (a b : Fin 6) : f (g32H0 ω a b) = g32H0 (f ω) a b := by
  fin_cases a <;> fin_cases b <;> simp [g32H0, map_div₀, map_ofNat]

end map

theorem hp_toMatrix_inv (g : b4b_Group) : b4b_toMatrix g⁻¹ = (b4b_toMatrix g)⁻¹ :=
  (Matrix.inv_eq_right_inv (by rw [← map_mul, mul_inv_cancel, map_one])).symm

theorem hp_toMatrix_generators (k : Fin 4) :
    b4b_toMatrix (b4b_generators k) = hp_genOver g32h_omega k := by
  fin_cases k <;> rfl

theorem hp_toMatrix_reflection (w : List (Fin 4)) :
    b4b_toMatrix (b4b_reflection w) = hp_reflOver g32h_omega w := by
  simp only [b4b_reflection, hp_reflOver, map_mul, hp_toMatrix_inv, map_list_prod, List.map_map]
  have : (b4b_toMatrix ∘ b4b_generators) = hp_genOver g32h_omega :=
    funext hp_toMatrix_generators
  rw [this, hp_toMatrix_generators 0]
  rfl

theorem hp_rootTuple_eq_over (j : Fin 13) : hp_rootTuple j = hp_rootTupleOver g32h_omega j := by
  change b4b_toMatrix (b4b_root j) = _
  fin_cases j <;>
    simp [b4b_root, hp_rootTupleOver, hp_toMatrix_inv, hp_toMatrix_reflection,
      hp_toMatrix_generators, hp_genOver]

theorem hp_rootTupleK_map_eq (j : Fin 13) : (hp_rootTupleK j).map hp_embed = hp_rootTuple j := by
  rw [hp_rootTuple_eq_over, ← hp_embed_zeta_eq]
  exact hp_rootTupleOver_map hp_embed pc_zeta j

theorem hp_certK_map_eq (a : Fin 6) (j : Fin 13) (k : Fin 4) :
    hp_embed (hp_certK a j k) = hp_cert a j k := by
  rw [hp_certK, hp_certOver_map, hp_embed_zeta_eq]
  rfl

theorem hp_rootTuple_eq_map : hp_rootTuple = fun j => (hp_TKlit j).map hp_embed := by
  funext j
  rw [← hp_rootTupleK_map_eq, hp_rootTupleK_eq]

theorem hp_cert_eq_map (a : Fin 6) : hp_cert a = fun j => hp_embed ∘ hp_certK a j := by
  funext j k
  exact (hp_certK_map_eq a j k).symm

theorem hp_embed_semiconj : Function.Semiconj hp_embed star star := hp_embed_star

theorem hp_rootTupleK_prod : (List.ofFn hp_rootTupleK).prod = 1 := by
  rw [hp_rootTupleK_eq]
  exact hp_TKlit_prod

theorem hp_rootTupleK_unitary : ∀ j, (hp_rootTupleK j)ᴴ * 1 * hp_rootTupleK j = 1 := by
  rw [hp_rootTupleK_eq]
  exact hp_TKlit_unitary

theorem hp_rootTuple_prod : (List.ofFn hp_rootTuple).prod = 1 := by
  rw [hp_rootTuple_eq_map]
  have : List.ofFn (fun j => (hp_TKlit j).map hp_embed) =
      (List.ofFn hp_TKlit).map hp_embed.mapMatrix := by
    rw [List.map_ofFn]
    rfl
  rw [this, ← map_list_prod, hp_TKlit_prod, map_one]

theorem hp_rootTuple_unitary : ∀ j, (hp_rootTuple j)ᴴ * 1 * hp_rootTuple j = 1 := by
  intro j
  rw [hp_rootTuple_eq_map]
  simp only
  rw [← Matrix.conjTranspose_map _ hp_embed_semiconj, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, ← map_one hp_embed.mapMatrix, ← map_mul, ← map_mul,
    hp_TKlit_unitary j, map_one]

theorem hp_map_sub_one {K L : Type*} [Field K] [Field L] (f : K →+* L) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι K) : A.map f - 1 = (A - 1).map f := by
  change f.mapMatrix A - 1 = f.mapMatrix (A - 1)
  rw [map_sub, map_one]

theorem hp_root_localFixed_eq (j : Fin 13) :
    Module.finrank ℂ (pc_localFixed hp_rootTuple j) = if j = 12 then 2 else 3 := by
  have hj : pc_localFixed hp_rootTuple j =
      LinearMap.ker (Matrix.toLin' ((hp_TKlit j - 1).map hp_embed)) := by
    rw [hp_rootTuple_eq_map, ← hp_map_sub_one]
    rfl
  rw [hj]
  induction j using Fin.lastCases with
  | last =>
    obtain ⟨h1, h2, h3⟩ := hp_ker_cert12
    simp only [show Fin.last 12 = (12 : Fin 13) from rfl, ↓reduceIte]
    exact pc_finrank_ker_of_cert_map hp_embed _ _ _ _ h1 h2 h3
  | cast i =>
    obtain ⟨h1, h2, h3⟩ := hp_ker_cert i
    simp only [show i.castSucc ≠ (12 : Fin 13) from Fin.castSucc_ne_last i, ↓reduceIte]
    exact pc_finrank_ker_of_cert_map hp_embed _ _ _ _ h1 h2 h3

theorem hp_root_fixed_eq : pc_fixed hp_rootTuple = ⊥ := by
  refine pc_fixed_eq_bot_of_cert hp_rootTuple ![0, 2, 4, 8] (fun k => (hp_fixL k).map hp_embed) ?_
  have h := congrArg hp_embed.mapMatrix hp_fix_cert
  rw [map_sum, map_one] at h
  rw [hp_rootTuple_eq_map]
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h
  rw [map_mul, map_sub, map_one]
  rfl

theorem hp_rootK_localFixed_eq (j : Fin 13) :
    Module.finrank hp_K (pc_localFixed hp_rootTupleK j) = if j = 12 then 2 else 3 := by
  have hj : pc_localFixed hp_rootTupleK j = LinearMap.ker (Matrix.toLin' (hp_TKlit j - 1)) := by
    rw [hp_rootTupleK_eq]
    rfl
  rw [hj]
  induction j using Fin.lastCases with
  | last =>
    obtain ⟨h1, h2, h3⟩ := hp_ker_cert12
    simp only [show Fin.last 12 = (12 : Fin 13) from rfl, ↓reduceIte]
    exact pc_finrank_ker_of_cert _ _ _ _ h1 h2 h3
  | cast i =>
    obtain ⟨h1, h2, h3⟩ := hp_ker_cert i
    simp only [show i.castSucc ≠ (12 : Fin 13) from Fin.castSucc_ne_last i, ↓reduceIte]
    exact pc_finrank_ker_of_cert _ _ _ _ h1 h2 h3

theorem hp_rootK_fixed_eq : pc_fixed hp_rootTupleK = ⊥ := by
  rw [hp_rootTupleK_eq]
  exact pc_fixed_eq_bot_of_cert hp_TKlit ![0, 2, 4, 8] hp_fixL hp_fix_cert

theorem hp_g32H0_det_ne_zero_C : (g32H0 g32h_omega).det ≠ 0 := by
  rw [papers_g32_h0_det g32h_omega g32h_omega_sq_add]
  norm_num

theorem hp_g32H0_det_ne_zero_K : (g32H0 pc_zeta).det ≠ 0 := by
  rw [papers_g32_h0_det pc_zeta hp_zeta_sq_add]
  norm_num

end HodgeLean.Foundations.Program
