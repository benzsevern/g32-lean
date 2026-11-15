import HodgeLean.Papers.G34FamilyDefs
import HodgeLean.Papers.PapersArithmetic

/-! # G34 Theorem A, stage 2: the Hurwitz family and its Prym–Tyurin factor, open proof
obligations -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

theorem g34h_rootNorm_eq_aux {K : Type*} [Field K] (w : K) (hw : w ^ 2 + w + 1 = 0)
    (i : Fin 10) : g34h_rootNorm w i = ![6, 2, 2, 6, 6, 6, 2, 6, 2, 2] i := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  fin_cases i <;>
    simp [g34h_rootNorm, g34h_root, Fin.sum_univ_six] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g34h_refl_sq_aux {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0)
    (i : Fin 10) : g34h_refl w i * g34h_refl w i = 1 := by
  let u := g34h_root w i
  let v := g34h_root (-1 - w) i
  let B := Matrix.vecMulVec u v
  have hn : v ⬝ᵥ u = g34h_rootNorm w i := by
    rfl
  have hB : B * B = g34h_rootNorm w i • B := by
    calc
      B * B = Matrix.vecMulVec u ((v ⬝ᵥ u) • v) := Matrix.vecMulVec_mul_vecMulVec u v u v
      _ = g34h_rootNorm w i • B := by
        rw [hn]
        ext j k
        simp [B, Matrix.vecMulVec_apply]
        ring
  have hne : g34h_rootNorm w i ≠ 0 := by
    rw [g34h_rootNorm_eq_aux w hw]
    fin_cases i <;> norm_num
  rw [g34h_refl, show Matrix.vecMulVec (g34h_root w i) (g34h_root (-1 - w) i) = B by rfl]
  rw [mul_sub, sub_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_smul, sub_mul,
    Matrix.one_mul, Matrix.smul_mul, hB]
  ext j k
  simp
  field_simp [hne]
  ring

theorem g34h_rank_refl_sub_one_aux {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) (i : Fin 10) : (g34h_refl w i - 1).rank = 1 := by
  let B := Matrix.vecMulVec (g34h_root w i) (g34h_root (-1 - w) i)
  have hn : g34h_rootNorm w i ≠ 0 := by
    rw [g34h_rootNorm_eq_aux w hw]
    fin_cases i <;> norm_num
  have hc : -(2 / g34h_rootNorm w i) ≠ 0 := by
    exact neg_ne_zero.mpr (div_ne_zero (by norm_num) hn)
  have heq : g34h_refl w i - 1 = -(2 / g34h_rootNorm w i) • B := by
    simp [g34h_refl, B]
  rw [heq, Matrix.rank_smul_of_mem_nonZeroDivisors B
    (mem_nonZeroDivisors_of_ne_zero hc)]
  apply le_antisymm (Matrix.rank_vecMulVec_le _ _)
  let p : Fin 10 → Fin 6 := ![0, 0, 1, 0, 0, 0, 2, 0, 0, 1]
  let f : Fin 1 → Fin 6 := fun _ => p i
  have hdet : (B.submatrix f f).det ≠ 0 := by
    have hp : w ^ 2 = -w - 1 := by linear_combination hw
    fin_cases i <;>
      simp [B, f, p, Matrix.det_fin_one, Matrix.submatrix, g34h_root,
        Matrix.vecMulVec_apply] <;>
      ring_nf <;> simp only [hp] <;> norm_num
  have hsub := Matrix.rank_submatrix_le B f f
  rw [Matrix.rank_of_det_ne_zero hdet] at hsub
  simpa using hsub

set_option maxHeartbeats 400000 in
theorem g34h_refl_conj_aux {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0)
    (i : Fin 10) :
    g34h_refl w 0 * g34h_refl w i * g34h_refl w 0 * (g34h_refl w i * g34h_refl w 0) =
      g34h_refl w i := by
  let P := 1 - g34h_refl w 0
  let Q := 1 - g34h_refl w i
  have hPP : P * P = 2 • P := by
    dsimp only [P]
    have hs := g34h_refl_sq_aux w hw 0
    calc
      (1 - g34h_refl w 0) * (1 - g34h_refl w 0) =
          1 - g34h_refl w 0 - g34h_refl w 0 + g34h_refl w 0 * g34h_refl w 0 := by
        noncomm_ring
      _ = 2 • (1 - g34h_refl w 0) := by rw [hs]; module
  have hQQ : Q * Q = 2 • Q := by
    dsimp only [Q]
    have hs := g34h_refl_sq_aux w hw i
    calc
      (1 - g34h_refl w i) * (1 - g34h_refl w i) =
          1 - g34h_refl w i - g34h_refl w i + g34h_refl w i * g34h_refl w i := by
        noncomm_ring
      _ = 2 • (1 - g34h_refl w i) := by rw [hs]; module
  by_cases hi : i = 0
  · subst i
    have hs := g34h_refl_sq_aux w hw 0
    rw [show g34h_refl w 0 * g34h_refl w 0 * g34h_refl w 0 *
        (g34h_refl w 0 * g34h_refl w 0) =
        (g34h_refl w 0 * g34h_refl w 0) * g34h_refl w 0 *
          (g34h_refl w 0 * g34h_refl w 0) by noncomm_ring, hs]
    simp
  let u0 := g34h_root w 0
  let v0 := g34h_root (-1 - w) 0
  let ui := g34h_root w i
  let vi := g34h_root (-1 - w) i
  let c0 := 2 / g34h_rootNorm w 0
  let ci := 2 / g34h_rootNorm w i
  have hP : P = c0 • Matrix.vecMulVec u0 v0 := by simp [P, c0, u0, v0, g34h_refl]
  have hQ : Q = ci • Matrix.vecMulVec ui vi := by simp [Q, ci, ui, vi, g34h_refl]
  have hcoef : c0 * ci * (v0 ⬝ᵥ ui) * (vi ⬝ᵥ u0) = 1 := by
    have hwo := hw
    have hp : w ^ 2 = -w - 1 := by linear_combination hw
    have hp3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw
    have hp4 : w ^ 4 = w := by linear_combination (w ^ 2 - w) * hw
    fin_cases i
    · exact (hi rfl).elim
    all_goals
      simp [c0, ci, u0, v0, ui, vi, g34h_rootNorm_eq_aux w hwo, g34h_root,
        dotProduct, Fin.sum_univ_six]
    all_goals field_simp
    all_goals (try ring_nf)
    all_goals (try simp only [hp3, hp4])
    all_goals (try ring)
    all_goals rw [hp]
    all_goals ring
  have hPQP : P * Q * P = P := by
    rw [hP, hQ, smul_mul_smul, Matrix.vecMulVec_mul_vecMulVec,
      smul_mul_smul, Matrix.vecMulVec_mul_vecMulVec]
    ext j k
    simp [Matrix.vecMulVec_apply]
    linear_combination c0 * u0 j * v0 k * hcoef
  have hQPQ : Q * P * Q = Q := by
    rw [hQ, hP, smul_mul_smul, Matrix.vecMulVec_mul_vecMulVec,
      smul_mul_smul, Matrix.vecMulVec_mul_vecMulVec]
    ext j k
    simp [Matrix.vecMulVec_apply]
    linear_combination ci * ui j * vi k * hcoef
  simp only [two_smul] at hPP hQQ
  have hs0 : g34h_refl w 0 = 1 - P := by simp [P]
  have hsi : g34h_refl w i = 1 - Q := by simp [Q]
  rw [hs0, hsi]
  have hA : (1 - P) * (1 - Q) * (1 - P) = 1 - P - Q + P * Q + Q * P := by
    calc
      (1 - P) * (1 - Q) * (1 - P) =
          1 - P - P + P * P - Q + Q * P + P * Q - P * Q * P := by noncomm_ring
      _ = 1 - P - Q + P * Q + Q * P := by rw [hPP, hPQP]; module
  rw [hA]
  have hB : (1 - P - Q + P * Q + Q * P) * (1 - Q) = 1 - P - Q + Q * P := by
    calc
      (1 - P - Q + P * Q + Q * P) * (1 - Q) =
          1 - P - Q + P * Q + Q * P -
            (Q - P * Q - Q * Q + P * (Q * Q) + Q * P * Q) := by noncomm_ring
      _ = 1 - P - Q + Q * P := by rw [hQQ, hQPQ]; noncomm_ring
  rw [← mul_assoc, hB]
  calc
    (1 - P - Q + Q * P) * (1 - P) =
        1 - P - Q + Q * P - (P - P * P - Q * P + Q * (P * P)) := by noncomm_ring
    _ = 1 - Q := by rw [hPP]; noncomm_ring

set_option maxHeartbeats 400000 in
theorem g34h_refl_eq_skel_aux (i : Fin 10) :
    Matrix.toEuclideanLin (g34h_refl skelg34_omega i) = (skelg34_reflection i).toLinearMap := by
  have hc : starRingEnd ℂ skelg34_omega = -1 - skelg34_omega := by
    simp [skelg34_omega, map_div₀]
    rw [map_ofNat]
    ring
  have hinner : inner ℂ (skelg34_root i) (skelg34_root i) =
      g34h_rootNorm skelg34_omega i := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    fin_cases i <;>
      simp [skelg34_root, g34h_rootNorm, g34h_root, dotProduct, hc,
        Fin.sum_univ_six] <;> ring
  apply LinearMap.ext
  intro x
  ext j
  rw [show (skelg34_reflection i).toLinearMap x =
      2 • (x - (ℂ ∙ skelg34_root i).starProjection x) - x by
    simpa [skelg34_reflection] using
      (Submodule.reflection_apply (K := (ℂ ∙ skelg34_root i)ᗮ) x),
    Submodule.starProjection_singleton, RCLike.ofReal_pow,
    ← inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (skelg34_root i), hinner,
    EuclideanSpace.inner_eq_star_dotProduct]
  fin_cases i <;> fin_cases j <;>
    simp [g34h_refl, skelg34_root, g34h_root, Matrix.toEuclideanLin,
      Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, hc, Fin.sum_univ_six,
      map_add, map_neg] <;> ring

theorem g34h_tuple_prod_aux {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) : (List.ofFn (g34h_tuple w)).prod = 1 := by
  rw [List.ofFn_eq_map]
  norm_num [List.finRange, g34h_tuple, ← mul_assoc, g34h_refl_sq_aux w hw]

theorem g34h_multCW_classRep_aux {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) : g34h_multCW (g34h_classRep w) = defectMultiplicity 6 g34Angles := by
  simp only [g34h_multCW, Fin.sum_univ_succ]
  norm_num [g34h_classRep, g34h_rank_refl_sub_one_aux w hw,
    papers_g34_multiplicity_hodge.2.1]

theorem g34h_multCW_reflections_aux {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) (r : ℕ) (i : Fin 10) :
    g34h_multCW (fun _ : Fin r => g34h_refl w i) = (r : ℤ) - 12 := by
  simp [g34h_multCW, g34h_rank_refl_sub_one_aux w hw]
  ring

theorem g34h_holoCW_classRep_aux (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g34h_holoCW (g34h_classRep w) = (holomorphicMultiplicity 6 g34Angles : ℝ) := by
  let u := g34h_root w 0
  let v := g34h_root (-1 - w) 0
  let M := Matrix.vecMulVec (-(2 / g34h_rootNorm w 0) • u) v
  have hn : v ⬝ᵥ u = g34h_rootNorm w 0 := by rfl
  have hd : (-(2 / g34h_rootNorm w 0) • u) ⬝ᵥ v = -2 := by
    rw [smul_dotProduct, dotProduct_comm, hn, g34h_rootNorm_eq_aux w hw]
    norm_num
  have heq : g34h_refl w 0 = M - Matrix.scalar (Fin 6) (-1) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [g34h_refl, M, u, v, Matrix.vecMulVec_apply, Matrix.scalar_apply]
      ring
    · simp [g34h_refl, M, u, v, Matrix.vecMulVec_apply, Matrix.scalar_apply, hij]
  have hchar : (g34h_refl w 0).charpoly = (Polynomial.X - 1) ^ 5 * (Polynomial.X + 1) := by
    rw [heq, Matrix.charpoly_sub_scalar]
    dsimp only [M]
    rw [Matrix.charpoly_vecMulVec]
    rw [hd]
    norm_num [two_smul]
    ring
  have hinv : (g34h_refl w 0)⁻¹ = g34h_refl w 0 := by
    apply Matrix.inv_eq_right_inv
    exact g34h_refl_sq_aux w hw 0
  have hroots : ((Polynomial.X - 1) ^ 5 * (Polynomial.X + 1) : Polynomial ℂ).roots =
      ({1, 1, 1, 1, 1, -1} : Multiset ℂ) := by
    rw [show (Polynomial.X - 1) ^ 5 * (Polynomial.X + 1) =
        (Multiset.map (fun x : ℂ => Polynomial.X - Polynomial.C x)
          ({1, 1, 1, 1, 1, -1} : Multiset ℂ)).prod by
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons,
        Multiset.map_singleton, Multiset.prod_singleton, map_one, map_neg]
      ring,
      Polynomial.roots_multiset_prod_X_sub_C]
  have hangle : g32h_angle (-1) = 1 / 2 := by
    have hpi := Real.pi_pos
    rw [g32h_angle, Complex.arg_neg_one, (toIcoMod_eq_self _).2]
    · field_simp
    · constructor <;> linarith
  have hone : g32h_angle 1 = 0 := by simp [g32h_angle]
  have hage : g34h_age (g34h_refl w 0)⁻¹ = 1 / 2 := by
    rw [g34h_age, hinv, hchar, hroots]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton, hone, hangle]
    norm_num
  simp only [g34h_holoCW, Fin.sum_univ_succ]
  norm_num [g34h_classRep, hage, papers_g34_multiplicity_hodge.2.2.2.1]

theorem g34h_riemannHurwitz_aux {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) :
    (39191040 : ℚ) * (-2 + ∑ j, (1 - 1 / (orderOf (g34h_classRep w j) : ℚ))) =
      2 * 156764161 - 2 := by
  have ho : orderOf (g34h_refl w 0) = 2 := by
    apply orderOf_eq_prime (by simpa [pow_two] using g34h_refl_sq_aux w hw 0)
    intro h
    have hr := g34h_rank_refl_sub_one_aux w hw 0
    rw [h, sub_self, Matrix.rank_zero] at hr
    norm_num at hr
  simp only [Fin.sum_univ_succ]
  norm_num [g34h_classRep, ho]

theorem g34h_tuple_nielsen_aux : g34h_Nielsen (g34h_tuple skelg34_omega) := by
  refine ⟨fun j => ?_, g34h_tuple_prod_aux skelg34_omega g34h_omega_sq_add, ?_⟩
  · let i : Fin 10 := ⟨(j : ℕ) / 2, by omega⟩
    let s0 := g34h_refl skelg34_omega 0
    let si := g34h_refl skelg34_omega i
    have h0 : s0 ∈ g34h_G := Submonoid.subset_closure ⟨0, rfl⟩
    have hi : si ∈ g34h_G := Submonoid.subset_closure ⟨i, rfl⟩
    refine ⟨s0 * si, mul_mem h0 hi, si * s0, mul_mem hi h0, ?_, ?_⟩
    · have hs0 := g34h_refl_sq_aux skelg34_omega g34h_omega_sq_add 0
      have hsi := g34h_refl_sq_aux skelg34_omega g34h_omega_sq_add i
      dsimp only [s0, si]
      rw [show g34h_refl skelg34_omega 0 * g34h_refl skelg34_omega i *
          (g34h_refl skelg34_omega i * g34h_refl skelg34_omega 0) =
          g34h_refl skelg34_omega 0 *
            (g34h_refl skelg34_omega i * g34h_refl skelg34_omega i) *
              g34h_refl skelg34_omega 0 by noncomm_ring, hsi]
      simp only [Matrix.mul_one]
      exact hs0
    · dsimp only [g34h_classRep, g34h_tuple, s0, si]
      exact (g34h_refl_conj_aux skelg34_omega g34h_omega_sq_add i).symm
  · rw [g34h_G]
    apply le_antisymm
    · apply Submonoid.closure_le.2
      rintro x ⟨j, rfl⟩
      exact Submonoid.subset_closure
        ⟨⟨(j : ℕ) / 2, by omega⟩, by simp [g34h_tuple]⟩
    · apply Submonoid.closure_mono
      rintro x ⟨i, rfl⟩
      refine ⟨⟨2 * (i : ℕ), by omega⟩, ?_⟩
      simp [g34h_tuple]

theorem g34h_nielsen_conj_aux (g : Fin 20 → Matrix (Fin 6) (Fin 6) ℂ) (hg : g34h_Nielsen g)
    (h h' : Matrix (Fin 6) (Fin 6) ℂ) (hh : h ∈ g34h_G) (hh' : h' ∈ g34h_G) (hinv : h * h' = 1) :
    g34h_Nielsen (fun j => h * g j * h') := by
  obtain ⟨hclass, hprod, hgen⟩ := hg
  have hinv' : h' * h = 1 := mul_eq_one_comm.mp hinv
  let f : Matrix (Fin 6) (Fin 6) ℂ →* Matrix (Fin 6) (Fin 6) ℂ :=
    { toFun := fun x => h * x * h'
      map_one' := by simp [hinv]
      map_mul' := fun x y => by
        rw [show h * x * h' * (h * y * h') = h * x * (h' * h) * y * h' by noncomm_ring,
          hinv', mul_one, mul_assoc h x y] }
  have hf : ∀ x, f x = h * x * h' := fun x => rfl
  refine ⟨fun j => ?_, ?_, ?_⟩
  · obtain ⟨k, hk, k', hk', hkk, hj⟩ := hclass j
    refine ⟨h * k, mul_mem hh hk, k' * h', mul_mem hk' hh', ?_, ?_⟩
    · rw [show h * k * (k' * h') = h * (k * k') * h' by noncomm_ring, hkk, mul_one, hinv]
    · show h * g j * h' = _
      rw [hj]
      noncomm_ring
  · have : (List.ofFn fun j => h * g j * h') = (List.ofFn g).map f := by
      rw [List.map_ofFn]
      rfl
    rw [this, ← map_list_prod, hprod, map_one]
  · have : Set.range (fun j => h * g j * h') = f '' Set.range g := by
      rw [← Set.range_comp]
      rfl
    rw [this, ← MonoidHom.map_mclosure, hgen]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hf]
      exact mul_mem (mul_mem hh hx) hh'
    · intro x hx
      refine ⟨h' * x * h, mul_mem (mul_mem hh' hx) hh, ?_⟩
      show h * (h' * x * h) * h' = x
      rw [show h * (h' * x * h) * h' = (h * h') * x * (h * h') by noncomm_ring, hinv]
      simp

theorem g34h_multCW_of_nielsen_aux (g : Fin 20 → Matrix (Fin 6) (Fin 6) ℂ)
    (hg : g34h_Nielsen g) : g34h_multCW g = 8 := by
  obtain ⟨hclass, -, -⟩ := hg
  have hr : ∀ j, (g j - 1).rank = (g34h_classRep skelg34_omega j - 1).rank := by
    intro j
    obtain ⟨k, -, k', -, hkk, hj⟩ := hclass j
    have hdet : k.det * k'.det = 1 := by rw [← Matrix.det_mul, hkk, Matrix.det_one]
    rw [hj, show k * g34h_classRep skelg34_omega j * k' - 1 =
        k * (g34h_classRep skelg34_omega j - 1) * k' by
      rw [mul_sub, sub_mul, mul_one, hkk]]
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _
        (isUnit_iff_exists_inv.mpr ⟨k.det, by rw [mul_comm]; exact hdet⟩),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_iff_exists_inv.mpr ⟨_, hdet⟩)]
  rw [← papers_g34_multiplicity_hodge.2.1,
    ← g34h_multCW_classRep_aux skelg34_omega g34h_omega_sq_add]
  unfold g34h_multCW
  simp only [hr]

theorem g34h_holoCW_of_nielsen_aux (g : Fin 20 → Matrix (Fin 6) (Fin 6) ℂ)
    (hg : g34h_Nielsen g) : g34h_holoCW g = 4 := by
  obtain ⟨hclass, -, -⟩ := hg
  have ha : ∀ j, g34h_age (g j)⁻¹ = g34h_age (g34h_classRep skelg34_omega j)⁻¹ := by
    intro j
    obtain ⟨k, -, k', -, hkk, hj⟩ := hclass j
    have hkk' : k' * k = 1 := mul_eq_one_comm.mp hkk
    let u : (Matrix (Fin 6) (Fin 6) ℂ)ˣ := ⟨k, k', hkk, hkk'⟩
    have hinv : (g j)⁻¹ = (u : Matrix (Fin 6) (Fin 6) ℂ) *
        (g34h_classRep skelg34_omega j)⁻¹ * (u : Matrix (Fin 6) (Fin 6) ℂ)⁻¹ := by
      show (g j)⁻¹ = k * (g34h_classRep skelg34_omega j)⁻¹ * k⁻¹
      rw [hj, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hkk, mul_assoc]
    rw [g34h_age, g34h_age, hinv, Matrix.charpoly_units_conj]
  have hfour : (holomorphicMultiplicity 6 g34Angles : ℝ) = 4 := by
    exact_mod_cast papers_g34_multiplicity_hodge.2.2.2.1
  rw [← hfour, ← g34h_holoCW_classRep_aux skelg34_omega g34h_omega_sq_add]
  unfold g34h_holoCW
  simp only [ha]

theorem g34h_fiber_polarized_aux (P : g34h_PrymFamily) :
    ∀ s, wtr_PolarizedWeil 4 (P.fiber s) := by
  intro s
  have hm := g34h_multCW_of_nielsen_aux (P.tuple s) (P.tuple_nielsen s)
  have hdim : dim (P.fiber s).X.left = 8 := by
    have h := P.dim_eq s
    rw [hm] at h
    exact_mod_cast h
  have hp := g34h_holoCW_of_nielsen_aux (P.tuple s) (P.tuple_nielsen s)
  have hh : g32h_h10 (P.fiber s) = 4 ∧ g32h_h01 (P.fiber s) = 4 := by
    rcases P.hodge s with h | h
    · rw [hm, hp] at h
      norm_num at h ⊢
      constructor
      · exact_mod_cast h.1
      · exact_mod_cast h.2
    · rw [hm, hp] at h
      norm_num at h ⊢
      constructor
      · exact_mod_cast h.2
      · exact_mod_cast h.1
  have hweil :
      letI := (torusCohomology_cupProductOf (P.fiber s).X).finite
      (P.fiber s).W.IsWeilType :=
    (isWeilType_iff_finrank_eq _ _ _ _ (P.fiber s).W).2 (hh.1.trans hh.2.symm)
  exact ⟨hdim, hweil, P.nondegenerate s, P.rosati s, P.positive s⟩

theorem g34h_h10_eq_four_aux (P : g34h_PrymFamily) (s : P.S) :
    g32h_h10 (P.fiber s) = 4 ∧ g32h_h01 (P.fiber s) = 4 := by
  have hm := g34h_multCW_of_nielsen_aux (P.tuple s) (P.tuple_nielsen s)
  have hp := g34h_holoCW_of_nielsen_aux (P.tuple s) (P.tuple_nielsen s)
  rcases P.hodge s with h | h
  · rw [hm, hp] at h
    norm_num at h ⊢
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  · rw [hm, hp] at h
    norm_num at h ⊢
    constructor
    · exact_mod_cast h.2
    · exact_mod_cast h.1

end HodgeLean.Papers
