import HodgeLean.Foundations.Program.ParabolicCohomologyRoot

/-! # Proofs for PC stages H2 and H6

The `_aux` theorems that `ParabolicCohomology.lean` restates, with their proofs. The H2 statements
use the lemmas of `ParabolicCohomologyLemmas`; the H6 statements over `K` use the explicit matrices
of `ParabolicCohomologyRootK`, and those over `ℂ` are transported from `K` through `hp_embed`
(`ParabolicCohomologyRoot`).
HC no distance; AV milestone no distance.
-/

noncomputable section

open Matrix HodgeLean.Papers

namespace HodgeLean.Foundations.Program

theorem pc_trivialPart_le_Z_aux {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (T : Fin r → Matrix ι ι K) (hprod : (List.ofFn T).prod = 1) :
    pc_trivialPart T ≤ pc_Z T := by
  refine sup_le ?_ ?_
  · rintro _ ⟨v, rfl⟩
    simp only [pc_Z, LinearMap.mem_ker, pc_relation_apply']
    change ∑ i, (pc_Q T i * (1 - T i)) *ᵥ v = 0
    rw [← Matrix.sum_mulVec, pc_sum_Q_sub, hprod, sub_self, Matrix.zero_mulVec]
  · intro a ha
    simp only [pc_Z, LinearMap.mem_ker, pc_relation_apply']
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi := ha i (Set.mem_univ _)
    have hi' : (T i - 1) *ᵥ a i = 0 := hi
    rw [← Matrix.mulVec_mulVec, ← neg_sub, Matrix.neg_mulVec, hi', neg_zero, Matrix.mulVec_zero]

theorem pc_finrank_aux {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (hprod : (List.ofFn T).prod = 1) :
    (Module.finrank K (pc_Vpar T) : ℤ) + ∑ i, (Module.finrank K (pc_localFixed T i) : ℤ) =
      ((r : ℤ) - 2) * Fintype.card ι + Module.finrank K (pc_fixed T) +
        Module.finrank K (pc_fixedTranspose T) := by
  have hZ := LinearMap.finrank_range_add_finrank_ker (pc_relation T)
  rw [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card] at hZ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hZ
  have hV := Submodule.finrank_quotient_add_finrank
    ((pc_trivialPart T).comap (pc_Z T).subtype)
  rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe
    (pc_trivialPart_le_Z_aux T hprod))] at hV
  have hR := pc_finrank_range_relation T
  have hP := pc_finrank_trivialPart T
  change Module.finrank K (pc_Vpar T) + _ = Module.finrank K (pc_Z T) at hV
  change _ + Module.finrank K (pc_Z T) = _ at hZ
  zify at hZ hV hR hP
  linear_combination hV + hZ - hR - hP

theorem pc_finrank_fixedTranspose_aux {K : Type*} [Field K] [StarRing K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hH : IsUnit H.det) (hinv : ∀ i, (T i)ᴴ * H * T i = H) :
    Module.finrank K (pc_fixedTranspose T) = Module.finrank K (pc_fixed T) := by
  have hTH : ∀ i, IsUnit (T i)ᴴ.det := fun i => by
    have h := congrArg Matrix.det (hinv i)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
    have h' : star (T i).det * (T i).det = 1 := by
      apply mul_right_cancel₀ hH.ne_zero
      linear_combination h
    rw [Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one h')
  have cancel : ∀ A : Matrix ι ι K, IsUnit A.det → ∀ x y, A *ᵥ x = A *ᵥ y → x = y := by
    intro A hA x y h
    have := congrArg (A⁻¹ *ᵥ ·) h
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA] using this
  have hfwd : ∀ φ ∈ pc_fixedTranspose T, H⁻¹ *ᵥ star φ ∈ pc_fixed T := by
    intro φ hφ
    rw [pc_mem_fixedTranspose_iff] at hφ
    rw [pc_mem_fixed_iff]
    intro i
    have hs : (T i)ᴴ *ᵥ star φ = star φ := by rw [← Matrix.star_vecMul, hφ i]
    have key : (T i)ᴴ *ᵥ (H *ᵥ (T i *ᵥ (H⁻¹ *ᵥ star φ))) = (T i)ᴴ *ᵥ star φ := by
      rw [hs]
      simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
      rw [hinv i, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec]
    have hHT := cancel _ (hTH i) _ _ key
    apply cancel H hH
    rw [hHT, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec]
  have hbwd : ∀ w ∈ pc_fixed T, star (H *ᵥ w) ∈ pc_fixedTranspose T := by
    intro w hw
    rw [pc_mem_fixed_iff] at hw
    rw [pc_mem_fixedTranspose_iff]
    intro i
    have h1 : (T i)ᴴ *ᵥ (H *ᵥ w) = H *ᵥ w := by
      calc (T i)ᴴ *ᵥ (H *ᵥ w) = (T i)ᴴ *ᵥ (H *ᵥ (T i *ᵥ w)) := by rw [hw i]
        _ = H *ᵥ w := by
          simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
          rw [hinv i]
    rw [← Matrix.conjTranspose_conjTranspose (T i), ← Matrix.star_mulVec, h1]
  let f : pc_fixedTranspose T ≃+ pc_fixed T :=
    { toFun := fun φ => ⟨H⁻¹ *ᵥ star φ.1, hfwd φ.1 φ.2⟩
      invFun := fun w => ⟨star (H *ᵥ w.1), hbwd w.1 w.2⟩
      left_inv := fun φ => by
        ext1
        simp only
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec, star_star]
      right_inv := fun w => by
        ext1
        simp only
        rw [star_star, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hH, Matrix.one_mulVec]
      map_add' := fun φ ψ => by
        ext1
        simp only [Submodule.coe_add, star_add, Matrix.mulVec_add] }
  have hbij : Function.Bijective (starRingEnd K) :=
    Function.Involutive.bijective fun x => star_star x
  have hrank := rank_eq_of_equiv_equiv (starRingEnd K) f hbij fun c φ => by
    ext1
    change H⁻¹ *ᵥ star (c • φ.1) = starRingEnd K c • (H⁻¹ *ᵥ star φ.1)
    rw [star_smul, Matrix.mulVec_smul]
    rfl
  unfold Module.finrank
  rw [hrank]

theorem pc_finrank_unitary_aux {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hH : IsUnit H.det) (hinv : ∀ i, (T i)ᴴ * H * T i = H) :
    (Module.finrank K (pc_Vpar T) : ℤ) + ∑ i, (Module.finrank K (pc_localFixed T i) : ℤ) =
      ((r : ℤ) - 2) * Fintype.card ι + 2 * Module.finrank K (pc_fixed T) := by
  rw [pc_finrank_aux T hprod, pc_finrank_fixedTranspose_aux T H hH hinv]
  ring

theorem pc_finrank_trivial_aux (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (r : ℕ) : Module.finrank K (pc_Vpar (fun _ : Fin r => (1 : Matrix ι ι K))) = 0 := by
  have htop : (pc_trivialPart (fun _ : Fin r => (1 : Matrix ι ι K))).comap
      (pc_Z (fun _ : Fin r => (1 : Matrix ι ι K))).subtype = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine Submodule.mem_comap.mpr (Submodule.mem_sup_right ?_)
    intro i _
    simp [pc_localFixed]
  have : Subsingleton (pc_Vpar (fun _ : Fin r => (1 : Matrix ι ι K))) := by
    rw [pc_Vpar, htop]
    infer_instance
  exact Module.finrank_zero_of_subsingleton

theorem pc_fixed_tuple_aux {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    pc_fixed (pc_tuple σ g) = pc_invariants σ := by
  have hmem : ∀ (A : Matrix ι ι K) (v : ι → K),
      v ∈ LinearMap.ker (Matrix.toLin' (A - 1)) ↔ A *ᵥ v = v := fun A v => by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  apply le_antisymm
  · intro v hv
    simp only [pc_fixed, pc_localFixed, pc_tuple, Submodule.mem_iInf, hmem] at hv
    simp only [pc_invariants, Submodule.mem_iInf, hmem]
    intro x
    have hx : x ∈ Subgroup.closure (Set.range g) := hg ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hv i
    | one => simp
    | mul y z _ _ hy hz => rw [map_mul, ← Matrix.mulVec_mulVec, hz, hy]
    | inv y _ hy =>
      calc σ y⁻¹ *ᵥ v = σ y⁻¹ *ᵥ (σ y *ᵥ v) := by rw [hy]
        _ = v := by rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one,
          Matrix.one_mulVec]
  · intro v hv
    simp only [pc_invariants, Submodule.mem_iInf] at hv
    simp only [pc_fixed, pc_localFixed, pc_tuple, Submodule.mem_iInf]
    exact fun i => hv (g i)

theorem pc_finrank_nielsen_aux {G : Type*} [Group G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (H : Matrix ι ι K) (hprod : (List.ofFn g).prod = 1)
    (hg : Subgroup.closure (Set.range g) = ⊤) (hH : IsUnit H.det)
    (hinv : ∀ x, (σ x)ᴴ * H * σ x = H) :
    (Module.finrank K (pc_Vpar (pc_tuple σ g)) : ℤ) +
        ∑ i, (Module.finrank K (pc_localFixed (pc_tuple σ g) i) : ℤ) =
      ((r : ℤ) - 2) * Fintype.card ι + 2 * Module.finrank K (pc_invariants σ) := by
  have hprod' : (List.ofFn (pc_tuple σ g)).prod = 1 := by
    have : List.ofFn (pc_tuple σ g) = (List.ofFn g).map σ := by
      rw [List.map_ofFn]
      rfl
    rw [this, ← map_list_prod, hprod, map_one]
  rw [pc_finrank_unitary_aux _ H hprod' hH fun i => hinv (g i), pc_fixed_tuple_aux σ g hg]

theorem pc_S_eq_invFree_aux {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hinv : ∀ i, (T i)ᴴ * H * T i = H)
    (a b : Fin r → ι → K) :
    pc_S T H a b = pc_SInvFree T H a b := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pc_form_invariant H (pc_Q T i) (pc_Q_invariant T H hinv i), Matrix.mulVec_add,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit (pc_Q_det_ne_zero T hprod i)),
    Matrix.one_mulVec]

theorem pc_S_skew_aux {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hHerm : Hᴴ = H) (hinv : ∀ i, (T i)ᴴ * H * T i = H)
    (a b : Fin r → ι → K) (ha : a ∈ pc_Z T) (hb : b ∈ pc_Z T) :
    pc_S T H a b + star (pc_S T H b a) = 0 := by
  set h : (ι → K) → (ι → K) → K := fun x y => star x ⬝ᵥ (H *ᵥ y) with hh
  have hal : ∀ x x' y, h (x + x') y = h x y + h x' y := fun x x' y => by
    simp [hh, star_add, add_dotProduct]
  have har : ∀ x y y', h x (y + y') = h x y + h x y' := fun x y y' => by
    simp [hh, Matrix.mulVec_add, dotProduct_add]
  have hsl : ∀ x x' y, h (x - x') y = h x y - h x' y := fun x x' y => by
    simp [hh, star_sub, sub_dotProduct]
  have hsr : ∀ x y y', h x (y - y') = h x y - h x y' := fun x y y' => by
    simp [hh, Matrix.mulVec_sub, dotProduct_sub]
  have hst : ∀ x y, star (h x y) = h y x := pc_form_star H hHerm
  have hQ : ∀ i x y, h (pc_Q T i *ᵥ x) (pc_Q T i *ᵥ y) = h x y := fun i =>
    pc_form_invariant H _ (pc_Q_invariant T H hinv i)
  have hT : ∀ i x y, h (T i *ᵥ x) (T i *ᵥ y) = h x y := fun i => pc_form_invariant H _ (hinv i)
  have hc : ∀ (x : Fin r → ι → K) i, pc_c T x i = x i - T i *ᵥ x i := fun x i => by
    simp [pc_c, Matrix.sub_mulVec]
  -- the term identity
  have hterm : ∀ i : Fin r,
      h (pc_F T a i + pc_Q T i *ᵥ a i) (pc_Q T i *ᵥ pc_c T b i) +
          star (h (pc_F T b i + pc_Q T i *ᵥ b i) (pc_Q T i *ᵥ pc_c T a i)) =
        h (pc_Fn T a (i + 1)) (pc_Fn T b (i + 1)) - h (pc_Fn T a i) (pc_Fn T b i) := fun i => by
    rw [pc_Fn_succ, pc_Fn_succ, ← pc_F_eq_Fn, ← pc_F_eq_Fn, hst]
    simp only [hal, har, hQ]
    simp only [hc, hsl, hsr, hT]
    ring
  have hS : ∀ x y, pc_S T H x y = ∑ i, h (pc_F T x i + pc_Q T i *ᵥ x i)
      (pc_Q T i *ᵥ pc_c T y i) := fun x y => by
    rw [pc_S_eq_invFree_aux T H hprod hinv]
    rfl
  rw [hS, hS, star_sum, ← Finset.sum_add_distrib]
  simp only [hterm]
  have htel := Finset.sum_range_sub (fun k => h (pc_Fn T a k) (pc_Fn T b k)) r

  rw [Fin.sum_univ_eq_sum_range (fun k => h (pc_Fn T a (k + 1)) (pc_Fn T b (k + 1)) -
    h (pc_Fn T a k) (pc_Fn T b k)), htel, pc_Fn_r, pc_Fn_r, pc_Fn_zero,
    pc_Fn_zero]
  rw [pc_Z, LinearMap.mem_ker] at ha hb
  simp [hh, ha, hb]

theorem pc_S_trivialPart_left_aux {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hinv : ∀ i, (T i)ᴴ * H * T i = H)
    (x b : Fin r → ι → K) (hx : x ∈ pc_trivialPart T) (hb : b ∈ pc_Z T) :
    pc_S T H x b = 0 := by
  obtain ⟨y, ⟨v, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  change pc_SForm T H (_ + z) b = 0
  rw [map_add, LinearMap.add_apply]
  change pc_S T H (fun _ => v) b + pc_S T H z b = 0
  have h1 : pc_S T H (fun _ => v) b = 0 := by
    rw [pc_S_eq_invFree_aux T H hprod hinv]
    have hterm : ∀ i : Fin r, star (pc_F T (fun _ => v) i + pc_Q T i *ᵥ v) ⬝ᵥ
        (H *ᵥ (pc_Q T i *ᵥ pc_c T b i)) = star v ⬝ᵥ (H *ᵥ (pc_Q T i *ᵥ pc_c T b i)) := by
      intro i
      rw [pc_F_eq_Fn, pc_Fn_const T v i i.isLt.le, ← pc_Q_eq_take, sub_add_cancel]
    change ∑ i, star (pc_F T (fun _ => v) i + pc_Q T i *ᵥ v) ⬝ᵥ
        (H *ᵥ (pc_Q T i *ᵥ pc_c T b i)) = 0
    simp only [hterm]
    rw [← dotProduct_sum, ← Matrix.mulVec_sum]
    rw [pc_Z, LinearMap.mem_ker] at hb
    change star v ⬝ᵥ (H *ᵥ pc_relation T b) = 0
    rw [hb, Matrix.mulVec_zero, dotProduct_zero]
  have h2 : pc_S T H z b = 0 := by
    have hz' : ∀ i, T i *ᵥ z i = z i := fun i => by
      have := hz i (Set.mem_univ _)
      simp only [pc_localFixed, SetLike.mem_coe, LinearMap.mem_ker, Matrix.toLin'_apply,
        Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
      exact this
    have hc : ∀ i, pc_c T z i = 0 := fun i => by
      simp [pc_c, Matrix.sub_mulVec, hz']
    have hF : ∀ i, pc_F T z i = 0 := fun i => by simp [pc_F, hc]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hF, Matrix.mulVec_zero, zero_add, pc_c, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub, dotProduct_sub, sub_eq_zero]
    rw [← pc_form_invariant H _ (hinv i) (z i) (b i), hz' i]
  rw [h1, h2, add_zero]

theorem pc_S_trivialPart_right_aux {K : Type*} [Field K] [StarRing K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hHerm : Hᴴ = H) (hinv : ∀ i, (T i)ᴴ * H * T i = H)
    (a x : Fin r → ι → K) (ha : a ∈ pc_Z T) (hx : x ∈ pc_trivialPart T) :
    pc_S T H a x = 0 := by
  have h := pc_S_skew_aux T H hprod hHerm hinv a x ha (pc_trivialPart_le_Z_aux T hprod hx)
  rwa [pc_S_trivialPart_left_aux T H hprod hinv x a hx ha, star_zero, add_zero] at h

theorem hp_root_localFixed_aux (j : Fin 13) :
    Module.finrank ℂ (pc_localFixed hp_rootTuple j) = if j = 12 then 2 else 3 := by
  exact hp_root_localFixed_eq j

theorem hp_root_fixed_aux : pc_fixed hp_rootTuple = ⊥ := by
  exact hp_root_fixed_eq

theorem hp_cert_mem_aux (a : Fin 6) : hp_cert a ∈ pc_Z hp_rootTuple := by
  rw [pc_Z, LinearMap.mem_ker, hp_rootTuple_eq_map, hp_cert_eq_map, pc_relation_map,
    hp_TKlit_mem a]
  funext x
  simp

theorem hp_cert_gram_aux (a b : Fin 6) :
    (1 + 2 * HodgeLean.Papers.g32h_omega) * pc_S hp_rootTuple 1 (hp_cert a) (hp_cert b) =
      HodgeLean.Papers.g32H0 HodgeLean.Papers.g32h_omega a b := by
  rw [pc_S_eq_invFree_aux hp_rootTuple 1 hp_rootTuple_prod hp_rootTuple_unitary]
  have h1 : (1 : Matrix (Fin 4) (Fin 4) ℂ) = (1 : Matrix (Fin 4) (Fin 4) hp_K).map hp_embed :=
    (Matrix.map_one _ hp_embed.map_zero hp_embed.map_one).symm
  rw [hp_rootTuple_eq_map, hp_cert_eq_map, hp_cert_eq_map, h1,
    pc_SInvFree_map hp_embed hp_embed_star, ← hp_embed_zeta_eq, ← hp_g32H0_map,
    ← hp_TKlit_gram a b, map_mul, map_add, map_mul, map_one, map_ofNat]

theorem hp_cert_independent_aux (c : Fin 6 → ℂ)
    (hc : ∑ a, c a • hp_cert a ∈ pc_trivialPart hp_rootTuple) : c = 0 := by
  exact pc_independent_of_gram hp_rootTuple 1
    (fun a x ha hx => pc_S_trivialPart_right_aux hp_rootTuple 1 hp_rootTuple_prod
      (by simp) hp_rootTuple_unitary a x ha hx)
    hp_cert hp_cert_mem_aux _ _ hp_g32H0_det_ne_zero_C hp_cert_gram_aux c hc

theorem hp_vpar_finrank_aux : Module.finrank ℂ (pc_Vpar hp_rootTuple) = 6 := by
  have h := pc_finrank_unitary_aux hp_rootTuple 1 hp_rootTuple_prod (by simp)
    hp_rootTuple_unitary
  have h0 : Module.finrank ℂ (pc_fixed hp_rootTuple) = 0 := by
    rw [hp_root_fixed_aux]
    exact finrank_bot ℂ _
  simp only [hp_root_localFixed_aux, h0, Fintype.card_fin] at h
  have hsum : ∑ j : Fin 13, (((if j = 12 then 2 else 3 : ℕ)) : ℤ) = 38 := by
    simp [Fin.sum_univ_succ]
  push_cast at h hsum
  omega

theorem pc_SPar_mk_aux {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hHerm : Hᴴ = H) (hinv : ∀ i, (T i)ᴴ * H * T i = H)
    (a b : Fin r → ι → K) (ha : a ∈ pc_Z T) (hb : b ∈ pc_Z T) :
    pc_SPar T H (Submodule.Quotient.mk ⟨a, ha⟩) (Submodule.Quotient.mk ⟨b, hb⟩) =
      pc_S T H a b := by
  have hlift : ∀ (c : Fin r → ι → K) (hc : c ∈ pc_Z T),
      ((pc_lift T (Submodule.Quotient.mk ⟨c, hc⟩) : pc_Z T) : Fin r → ι → K) - c ∈
        pc_trivialPart T := fun c hc => by
    have h : Submodule.Quotient.mk (p := (pc_trivialPart T).comap (pc_Z T).subtype)
        (pc_lift T (Submodule.Quotient.mk ⟨c, hc⟩)) = Submodule.Quotient.mk ⟨c, hc⟩ :=
      Submodule.mk_quotientEquivOfIsCompl_apply
        (Classical.choose_spec (Submodule.exists_isCompl _)) _
    rw [Submodule.Quotient.eq, Submodule.mem_comap] at h
    simpa using h
  set a' : Fin r → ι → K := (pc_lift T (Submodule.Quotient.mk ⟨a, ha⟩)).1
  set b' : Fin r → ι → K := (pc_lift T (Submodule.Quotient.mk ⟨b, hb⟩)).1
  have hb' : b' ∈ pc_Z T := (pc_lift T _).2
  change pc_S T H a' b' = pc_S T H a b
  have ex : a' = a + (a' - a) := by abel
  have ey : b' = b + (b' - b) := by abel
  rw [ex]
  change pc_SForm T H (a + (a' - a)) b' = _
  rw [map_add, LinearMap.add_apply]
  change pc_S T H a b' + pc_S T H (a' - a) b' = _
  rw [pc_S_trivialPart_left_aux T H hprod hinv _ _ (hlift a ha) hb', add_zero, ey]
  change pc_SForm T H a (b + (b' - b)) = _
  rw [map_add]
  change pc_S T H a b + pc_S T H a (b' - b) = _
  rw [pc_S_trivialPart_right_aux T H hprod hHerm hinv _ _ ha (hlift b hb), add_zero]

theorem hp_embed_zeta_aux : hp_embed pc_zeta = HodgeLean.Papers.g32h_omega := by
  exact hp_embed_zeta_eq

theorem hp_rootTupleK_map_aux (j : Fin 13) :
    (hp_rootTupleK j).map hp_embed = hp_rootTuple j := by
  exact hp_rootTupleK_map_eq j

theorem hp_certK_map_aux (a : Fin 6) (j : Fin 13) (k : Fin 4) :
    hp_embed (hp_certK a j k) = hp_cert a j k := by
  exact hp_certK_map_eq a j k

theorem hp_certK_mem_aux (a : Fin 6) : hp_certK a ∈ pc_Z hp_rootTupleK := by
  rw [pc_Z, LinearMap.mem_ker, hp_rootTupleK_eq]
  exact hp_TKlit_mem a

theorem hp_certK_gram_aux (a b : Fin 6) :
    (1 + 2 * pc_zeta) * pc_S hp_rootTupleK 1 (hp_certK a) (hp_certK b) =
      HodgeLean.Papers.g32H0 pc_zeta a b := by
  rw [pc_S_eq_invFree_aux hp_rootTupleK 1 hp_rootTupleK_prod hp_rootTupleK_unitary,
    hp_rootTupleK_eq]
  exact hp_TKlit_gram a b

theorem hp_certK_independent_aux (c : Fin 6 → hp_K)
    (hc : ∑ a, c a • hp_certK a ∈ pc_trivialPart hp_rootTupleK) : c = 0 := by
  exact pc_independent_of_gram hp_rootTupleK 1
    (fun a x ha hx => pc_S_trivialPart_right_aux hp_rootTupleK 1 hp_rootTupleK_prod
      (by simp) hp_rootTupleK_unitary a x ha hx)
    hp_certK hp_certK_mem_aux _ _ hp_g32H0_det_ne_zero_K hp_certK_gram_aux c hc

theorem hp_vparK_finrank_aux : Module.finrank hp_K (pc_Vpar hp_rootTupleK) = 6 := by
  have h := pc_finrank_unitary_aux hp_rootTupleK 1 hp_rootTupleK_prod (by simp)
    hp_rootTupleK_unitary
  have h0 : Module.finrank hp_K (pc_fixed hp_rootTupleK) = 0 := by
    rw [hp_rootK_fixed_eq]
    exact finrank_bot hp_K _
  simp only [hp_rootK_localFixed_eq, h0, Fintype.card_fin] at h
  have hsum : ∑ j : Fin 13, (((if j = 12 then 2 else 3 : ℕ)) : ℤ) = 38 := by
    simp [Fin.sum_univ_succ]
  push_cast at h hsum
  omega

end HodgeLean.Foundations.Program
