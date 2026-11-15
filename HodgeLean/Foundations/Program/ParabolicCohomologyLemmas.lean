import HodgeLean.Foundations.Program.ParabolicCohomologyDefs

/-! # Lemmas for PC stage H2

Telescoping identities for the partial products `Q_i`, the invariant form
`h(x, y) = star x ⬝ᵥ (H *ᵥ y)` and the partial sums `F_k` of the parameter model.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Matrix

namespace HodgeLean.Foundations.Program

theorem pc_filter_lt_eq_take : ∀ (r : ℕ) (i : Fin r),
    (List.finRange r).filter (fun j => decide (j < i)) = (List.finRange r).take i
  | 0, i => i.elim0
  | r + 1, i => by
    rw [List.finRange_succ]
    refine Fin.cases ?_ (fun k => ?_) i
    · simp
    · have ih := pc_filter_lt_eq_take r k
      simp only [List.filter_cons, Fin.succ_pos, decide_true, ite_true, Fin.val_succ,
        List.take_succ_cons]
      congr 1
      rw [← List.map_take, ← ih, List.filter_map]
      rfl

theorem pc_Q_eq_take {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (i : Fin r) :
    pc_Q T i = ((List.ofFn T).take i).prod := by
  rw [pc_Q, pc_filter_lt_eq_take, List.ofFn_eq_map, ← List.map_take]

theorem pc_take_succ_prod {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (i : Fin r) :
    ((List.ofFn T).take (i + 1)).prod = pc_Q T i * T i := by
  rw [pc_Q_eq_take, List.take_add_one, List.prod_append]
  simp

theorem pc_sum_Q_sub {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) :
    ∑ i, pc_Q T i * (1 - T i) = 1 - (List.ofFn T).prod := by
  have h : ∀ i : Fin r, pc_Q T i * (1 - T i) =
      ((List.ofFn T).take i).prod - ((List.ofFn T).take (i + 1)).prod := fun i => by
    rw [pc_take_succ_prod, pc_Q_eq_take, mul_sub, mul_one]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => ((List.ofFn T).take k).prod - ((List.ofFn T).take (k + 1)).prod),
    Finset.sum_range_sub']
  simp [List.take_of_length_le]

theorem pc_relation_apply' {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (a : Fin r → ι → K) :
    pc_relation T a = ∑ i, (pc_Q T i * (1 - T i)) *ᵥ a i := by
  simp [pc_relation, pc_c, Matrix.mulVec_mulVec]

/-! ### The form `h(x, y) = star x ⬝ᵥ (H *ᵥ y)` -/

theorem pc_form_invariant {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    (H A : Matrix ι ι K) (hA : Aᴴ * H * A = H) (x y : ι → K) :
    star (A *ᵥ x) ⬝ᵥ (H *ᵥ (A *ᵥ y)) = star x ⬝ᵥ (H *ᵥ y) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hA]

theorem pc_form_star {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    (H : Matrix ι ι K) (hHerm : Hᴴ = H) (x y : ι → K) :
    star (star x ⬝ᵥ (H *ᵥ y)) = star y ⬝ᵥ (H *ᵥ x) := by
  rw [← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, hHerm, dotProduct_comm,
    Matrix.dotProduct_mulVec, dotProduct_comm]

theorem pc_list_prod_invariant {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (H : Matrix ι ι K) :
    ∀ l : List (Matrix ι ι K), (∀ A ∈ l, Aᴴ * H * A = H) → l.prodᴴ * H * l.prod = H
  | [], _ => by simp
  | A :: l, h => by
    rw [List.prod_cons, Matrix.conjTranspose_mul]
    have hl := pc_list_prod_invariant H l (fun B hB => h B (List.mem_cons_of_mem _ hB))
    calc l.prodᴴ * Aᴴ * H * (A * l.prod) = l.prodᴴ * (Aᴴ * H * A) * l.prod := by
          simp only [Matrix.mul_assoc]
      _ = H := by rw [h A List.mem_cons_self, hl]

theorem pc_Q_invariant {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hinv : ∀ i, (T i)ᴴ * H * T i = H) (i : Fin r) :
    (pc_Q T i)ᴴ * H * pc_Q T i = H := by
  rw [pc_Q_eq_take]
  refine pc_list_prod_invariant H _ fun A hA => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hA)
  exact hinv j

theorem pc_det_ne_zero {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (hprod : (List.ofFn T).prod = 1) (i : Fin r) :
    (T i).det ≠ 0 := by
  have h := congrArg Matrix.det hprod
  rw [Matrix.det_one, ← Matrix.coe_detMonoidHom, map_list_prod, List.map_ofFn,
    List.prod_ofFn] at h
  exact (Finset.prod_ne_zero_iff.mp (h ▸ one_ne_zero)) i (Finset.mem_univ _)

theorem pc_Q_det_ne_zero {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (hprod : (List.ofFn T).prod = 1) (i : Fin r) :
    (pc_Q T i).det ≠ 0 := by
  rw [pc_Q, ← Matrix.coe_detMonoidHom, map_list_prod]
  refine List.prod_ne_zero ?_
  intro h
  obtain ⟨A, hA, hA0⟩ := List.mem_map.mp h
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hA
  exact pc_det_ne_zero T hprod j hA0

/-- The partial sums `Σ_{j < k} Q_j c_j` for a natural number `k`. -/

def pc_Fn {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (a : Fin r → ι → K) (k : ℕ) : ι → K :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin r => (j : ℕ) < k), pc_Q T j *ᵥ pc_c T a j

theorem pc_F_eq_Fn {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (a : Fin r → ι → K) (i : Fin r) :
    pc_F T a i = pc_Fn T a i := by
  simp only [pc_F, pc_Fn, Fin.lt_def]

theorem pc_Fn_zero {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (a : Fin r → ι → K) : pc_Fn T a 0 = 0 := by
  simp [pc_Fn]

theorem pc_Fn_r {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (a : Fin r → ι → K) : pc_Fn T a r = pc_relation T a := by
  simp [pc_Fn]
  rfl

theorem pc_Fn_succ {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (a : Fin r → ι → K) (i : Fin r) :
    pc_Fn T a (i + 1) = pc_Fn T a i + pc_Q T i *ᵥ pc_c T a i := by
  have hs : Finset.univ.filter (fun j : Fin r => (j : ℕ) < i + 1) =
      insert i (Finset.univ.filter (fun j : Fin r => (j : ℕ) < i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Nat.lt_succ_iff,
      Fin.ext_iff]
    omega
  rw [pc_Fn, hs, Finset.sum_insert (by simp), add_comm]
  rfl

theorem pc_Fn_const {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (v : ι → K) :
    ∀ k ≤ r, pc_Fn T (fun _ => v) k = v - ((List.ofFn T).take k).prod *ᵥ v
  | 0, _ => by simp [pc_Fn_zero]
  | k + 1, hk => by
    have h := pc_Fn_succ T (fun _ => v) ⟨k, hk⟩
    simp only at h
    rw [h, pc_Fn_const T v k (by omega), pc_take_succ_prod T ⟨k, hk⟩, pc_Q_eq_take]
    rw [pc_c, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec]
    abel

theorem pc_vecMul_list_prod {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → K) : ∀ l : List (Matrix ι ι K), (∀ A ∈ l, φ ᵥ* A = φ) → φ ᵥ* l.prod = φ
  | [], _ => by simp
  | A :: l, h => by
    rw [List.prod_cons, ← Matrix.vecMul_vecMul, h A List.mem_cons_self,
      pc_vecMul_list_prod φ l fun B hB => h B (List.mem_cons_of_mem _ hB)]

theorem pc_vecMul_relation_iff {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (T : Fin r → Matrix ι ι K) (φ : ι → K) :
    (∀ i, φ ᵥ* (pc_Q T i * (1 - T i)) = 0) ↔ ∀ i, φ ᵥ* T i = φ := by
  constructor
  · intro h
    have hP : ∀ k ≤ r, φ ᵥ* ((List.ofFn T).take k).prod = φ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        intro hk
        have hk' := ih (by omega)
        have h1 := h ⟨k, hk⟩
        rw [pc_Q_eq_take] at h1
        rw [← Matrix.vecMul_vecMul, hk', Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero] at h1
        rw [pc_take_succ_prod T ⟨k, hk⟩, pc_Q_eq_take, ← Matrix.vecMul_vecMul, hk', ← h1]
    intro i
    have h1 := h i
    rw [pc_Q_eq_take, ← Matrix.vecMul_vecMul, hP i i.isLt.le, Matrix.vecMul_sub,
      Matrix.vecMul_one, sub_eq_zero] at h1
    exact h1.symm
  · intro h i
    rw [pc_Q_eq_take, ← Matrix.vecMul_vecMul, pc_vecMul_list_prod φ _ fun A hA => ?_,
      Matrix.vecMul_sub, Matrix.vecMul_one, h i, sub_self]
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hA)
    exact h j

theorem pc_mem_fixedTranspose_iff {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (T : Fin r → Matrix ι ι K) (φ : ι → K) :
    φ ∈ pc_fixedTranspose T ↔ ∀ i, φ ᵥ* T i = φ := by
  simp only [pc_fixedTranspose, Submodule.mem_iInf, LinearMap.mem_ker, Matrix.toLin'_apply,
    Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero, Matrix.mulVec_transpose]

theorem pc_mem_fixed_iff {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (T : Fin r → Matrix ι ι K) (w : ι → K) :
    w ∈ pc_fixed T ↔ ∀ i, T i *ᵥ w = w := by
  simp only [pc_fixed, pc_localFixed, Submodule.mem_iInf, LinearMap.mem_ker, Matrix.toLin'_apply,
    Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]

theorem pc_finrank_range_relation {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (T : Fin r → Matrix ι ι K) :
    Module.finrank K (LinearMap.range (pc_relation T)) +
      Module.finrank K (pc_fixedTranspose T) = Fintype.card ι := by
  let M : Matrix ι (Fin r × ι) K := Matrix.of fun x p => (pc_Q T p.1 * (1 - T p.1)) x p.2
  have hR : pc_relation T =
      M.mulVecLin ∘ₗ (LinearEquiv.curry K K (Fin r) ι).symm.toLinearMap := by
    refine LinearMap.ext fun a => funext fun x => ?_
    rw [pc_relation_apply']
    simp [M, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_apply]
  have hrange : LinearMap.range (pc_relation T) = LinearMap.range M.mulVecLin := by
    rw [hR, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  have hker : LinearMap.ker Mᵀ.mulVecLin = pc_fixedTranspose T := by
    ext φ
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose,
      pc_mem_fixedTranspose_iff, ← pc_vecMul_relation_iff]
    constructor
    · intro h i
      funext y
      have := congrFun h (i, y)
      simpa [M, Matrix.vecMul, dotProduct] using this
    · intro h
      funext p
      have := congrFun (h p.1) p.2
      simpa [M, Matrix.vecMul, dotProduct] using this
  have h1 := LinearMap.finrank_range_add_finrank_ker Mᵀ.mulVecLin
  rw [hker, Module.finrank_fintype_fun_eq_card] at h1
  have h2 : Module.finrank K (LinearMap.range Mᵀ.mulVecLin) =
      Module.finrank K (LinearMap.range M.mulVecLin) := Matrix.rank_transpose M
  rw [hrange, ← h2]
  exact h1

/-- `Π_i ker(T_i − 1)` as a product of the local fixed spaces. -/

def pc_localPartEquiv {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) : pc_localPart T ≃ₗ[K] ∀ i, pc_localFixed T i where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ _)⟩
  invFun y := ⟨fun i => (y i).1, fun i _ => (y i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem pc_finrank_trivialPart {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (T : Fin r → Matrix ι ι K) :
    Module.finrank K (pc_trivialPart T) + Module.finrank K (pc_fixed T) =
      Fintype.card ι + ∑ i, Module.finrank K (pc_localFixed T i) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have : Subsingleton (pc_trivialPart T) := inferInstance
    rw [Module.finrank_zero_of_subsingleton, pc_fixed, iInf_of_empty, finrank_top,
      Module.finrank_fintype_fun_eq_card]
    simp
  · let C : (ι → K) →ₗ[K] (Fin r → ι → K) := LinearMap.pi fun _ => LinearMap.id
    have hC : Function.Injective C := fun v w h => congrFun h ⟨0, hr⟩
    have hcob : pc_coboundaries ι r = LinearMap.range C := rfl
    have hinf : pc_coboundaries ι r ⊓ pc_localPart T = (pc_fixed T).map C := by
      ext x
      simp only [hcob, Submodule.mem_inf, LinearMap.mem_range, Submodule.mem_map]
      constructor
      · rintro ⟨⟨v, rfl⟩, hx⟩
        refine ⟨v, ?_, rfl⟩
        simp only [pc_fixed, Submodule.mem_iInf]
        exact fun i => hx i (Set.mem_univ _)
      · rintro ⟨v, hv, rfl⟩
        refine ⟨⟨v, rfl⟩, fun i _ => ?_⟩
        simp only [pc_fixed, Submodule.mem_iInf] at hv
        exact hv i
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (pc_coboundaries ι r) (pc_localPart T)
    rw [hinf, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective C hC _).symm, hcob,
      LinearMap.finrank_range_of_inj hC, Module.finrank_fintype_fun_eq_card,
      LinearEquiv.finrank_eq (pc_localPartEquiv T), Module.finrank_pi_fintype] at h1
    exact h1

section map

variable {K L : Type*} [Field K] [Field L] (f : K →+* L) {ι : Type*} [Fintype ι] [DecidableEq ι]
  {r : ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem pc_comp_mulVec {κ : Type*} [Fintype κ] (M : Matrix ι κ K) (v : κ → K) :
    f ∘ (M *ᵥ v) = M.map f *ᵥ (f ∘ v) :=
  funext fun i => RingHom.map_mulVec f M v i

theorem pc_map_one_sub (A : Matrix ι ι K) : (1 - A).map f = 1 - A.map f := by
  rw [← RingHom.mapMatrix_apply, map_sub, map_one]
  rfl

theorem pc_map_inv (A : Matrix ι ι K) : (A⁻¹).map f = (A.map f)⁻¹ := by
  by_cases h : IsUnit A.det
  · symm
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ f.map_zero f.map_one]
  · have h' : ¬ IsUnit (A.map f).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero, ne_eq,
        map_eq_zero_iff f f.injective, ← ne_eq, ← isUnit_iff_ne_zero]
      exact h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h',
      Matrix.map_zero _ f.map_zero]

theorem pc_Q_map (T : Fin r → Matrix ι ι K) (i : Fin r) :
    pc_Q (fun j => (T j).map f) i = (pc_Q T i).map f := by
  simp only [pc_Q]
  rw [← RingHom.mapMatrix_apply, map_list_prod, List.map_map]
  rfl

theorem pc_c_map (T : Fin r → Matrix ι ι K) (a : Fin r → ι → K) (i : Fin r) :
    f ∘ pc_c T a i = pc_c (fun j => (T j).map f) (fun j => f ∘ a j) i := by
  rw [pc_c, pc_comp_mulVec, pc_map_one_sub]
  rfl

theorem pc_F_map (T : Fin r → Matrix ι ι K) (a : Fin r → ι → K) (i : Fin r) :
    f ∘ pc_F T a i = pc_F (fun j => (T j).map f) (fun j => f ∘ a j) i := by
  funext x
  simp only [pc_F, Function.comp, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RingHom.map_mulVec, pc_Q_map, ← pc_c_map]

theorem pc_relation_map (T : Fin r → Matrix ι ι K) (a : Fin r → ι → K) :
    pc_relation (fun j => (T j).map f) (fun j => f ∘ a j) = f ∘ pc_relation T a := by
  funext x
  change (∑ i, pc_Q _ i *ᵥ pc_c _ _ i) x = f ((∑ i, pc_Q T i *ᵥ pc_c T a i) x)
  simp only [Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.map_mulVec, pc_Q_map, ← pc_c_map]

theorem pc_SInvFree_map [StarRing K] [StarRing L] (hf : ∀ x, f (star x) = star (f x))
    (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K) (a b : Fin r → ι → K) :
    pc_SInvFree (fun j => (T j).map f) (H.map f) (fun j => f ∘ a j) (fun j => f ∘ b j) =
      f (pc_SInvFree T H a b) := by
  simp only [pc_SInvFree, map_sum, RingHom.map_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  · funext x
    simp only [Function.comp, Pi.star_apply, hf, Pi.add_apply, map_add, ← pc_F_map,
      RingHom.map_mulVec, pc_Q_map]
  · rw [pc_comp_mulVec, pc_comp_mulVec, pc_c_map, pc_Q_map]

end map

theorem pc_finrank_ker_of_cert {K : Type*} [Field K] {n k : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin n) (Fin k) K) (C : Matrix (Fin k) (Fin n) K) (M : Matrix (Fin n) (Fin n) K)
    (h1 : A * B = 0) (h2 : C * B = 1) (h3 : B * C + M * A = 1) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' A)) = k := by
  have hker : LinearMap.ker (Matrix.toLin' A) = LinearMap.range (Matrix.toLin' B) := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.mem_range, Matrix.toLin'_apply]
    constructor
    · intro hv
      refine ⟨C *ᵥ v, ?_⟩
      have := congrArg (· *ᵥ v) h3
      simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, add_zero,
        Matrix.one_mulVec] at this
      exact this
    · rintro ⟨w, rfl⟩
      rw [Matrix.mulVec_mulVec, h1, Matrix.zero_mulVec]
  have hinj : Function.Injective (Matrix.toLin' B) := by
    intro x y h
    have := congrArg (C *ᵥ ·) h
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2] using this
  rw [hker, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

theorem pc_finrank_ker_of_cert_map {K L : Type*} [Field K] [Field L] (f : K →+* L) {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin n) (Fin k) K) (C : Matrix (Fin k) (Fin n) K)
    (M : Matrix (Fin n) (Fin n) K) (h1 : A * B = 0) (h2 : C * B = 1) (h3 : B * C + M * A = 1) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' (A.map f))) = k := by
  refine pc_finrank_ker_of_cert _ (B.map f) (C.map f) (M.map f) ?_ ?_ ?_
  · rw [← Matrix.map_mul, h1, Matrix.map_zero _ f.map_zero]
  · rw [← Matrix.map_mul, h2, Matrix.map_one _ f.map_zero f.map_one]
  · rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add f), h3,
      Matrix.map_one _ f.map_zero f.map_one]

theorem pc_fixed_eq_bot_of_cert {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r m : ℕ} (T : Fin r → Matrix ι ι K) (idx : Fin m → Fin r) (L : Fin m → Matrix ι ι K)
    (h : ∑ k, L k * (T (idx k) - 1) = 1) : pc_fixed T = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [pc_mem_fixed_iff] at hv
  rw [Submodule.mem_bot]
  have := congrArg (· *ᵥ v) h
  simp only [Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hv,
    sub_self, Matrix.mulVec_zero, Finset.sum_const_zero] at this
  exact this.symm

theorem pc_independent_of_gram {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r n : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hright : ∀ a x, a ∈ pc_Z T → x ∈ pc_trivialPart T → pc_S T H a x = 0)
    (v : Fin n → Fin r → ι → K) (hv : ∀ a, v a ∈ pc_Z T) (δ : K)
    (G : Matrix (Fin n) (Fin n) K) (hG : G.det ≠ 0)
    (hgram : ∀ a b, δ * pc_S T H (v a) (v b) = G a b) (c : Fin n → K)
    (hc : ∑ a, c a • v a ∈ pc_trivialPart T) : c = 0 := by
  refine Matrix.eq_zero_of_mulVec_eq_zero hG (funext fun b => ?_)
  have h0 := hright (v b) _ (hv b) hc
  have hlin : pc_S T H (v b) (∑ a, c a • v a) = ∑ a, c a * pc_S T H (v b) (v a) := by
    change pc_SForm T H (v b) (∑ a, c a • v a) = _
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rfl
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, ← hgram]
  calc ∑ a, δ * pc_S T H (v b) (v a) * c a = δ * ∑ a, c a * pc_S T H (v b) (v a) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = 0 := by rw [← hlin, h0, mul_zero]

end HodgeLean.Foundations.Program
