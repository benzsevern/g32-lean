import HodgeLean.Foundations.Program.PrymParabolicComparisonDefs
import HodgeLean.Foundations.Program.ParabolicCohomologyLemmas

/-! # Lemmas for stage H3a: the lifted Δ-complex of G32 Figure 1

Partial products `Q_i` and the cyclic order, the deck action on endpoints, the partial sums of
the Shapiro map, and the boundary of a `2`-chain on each edge.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Matrix

namespace HodgeLean.Foundations.Program

/-! ### Partial products and the cyclic order -/

theorem hg_Q_eq_take {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (i : Fin r) :
    hg_Q g i = ((List.ofFn g).take i).prod := by
  rw [hg_Q, pc_filter_lt_eq_take, List.ofFn_eq_map, ← List.map_take]

theorem hg_take_succ_prod {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (i : Fin r) :
    ((List.ofFn g).take (i + 1)).prod = hg_Q g i * g i := by
  rw [hg_Q_eq_take, List.take_add_one, List.prod_append]
  simp

theorem hg_finRotate_val {r : ℕ} (i : Fin r) :
    ((finRotate r i : Fin r) : ℕ) = if (i : ℕ) + 1 = r then 0 else (i : ℕ) + 1 := by
  cases r with
  | zero => exact i.elim0
  | succ r =>
    rw [coe_finRotate]
    by_cases h : (i : ℕ) + 1 = r + 1
    · have : i = Fin.last r := Fin.ext (by simp; omega)
      simp [this]
    · have : i ≠ Fin.last r := fun h' => h (by simp [h'])
      simp [this]
      omega

theorem hg_Q_zero {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (hr : 0 < r) :
    hg_Q g ⟨0, hr⟩ = 1 := by
  simp [hg_Q_eq_take]

theorem hg_Q_succ {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (i : Fin r)
    (hi : (i : ℕ) + 1 < r) : hg_Q g ⟨i + 1, hi⟩ = hg_Q g i * g i := by
  rw [hg_Q_eq_take, ← hg_take_succ_prod]

theorem hg_Q_rotate {G : Type*} [Group G] {r : ℕ} (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) (i : Fin r) :
    hg_Q g (finRotate r i) = hg_Q g i * g i := by
  rw [← hg_take_succ_prod, hg_Q_eq_take, hg_finRotate_val]
  split_ifs with h
  · rw [h, List.take_zero, List.take_of_length_le (by simp), hprod]
    rfl
  · rfl

theorem hg_pc_Q {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) (i : Fin r) :
    pc_Q (pc_tuple σ g) i = σ (hg_Q g i) := by
  rw [pc_Q, hg_Q, map_list_prod, List.map_map]
  rfl

theorem hg_σ_inv_mul {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (σ : G →* Matrix ι ι K) (x : G) : σ x⁻¹ * σ x = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem hg_σ_mul_inv {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (σ : G →* Matrix ι ι K) (x : G) : σ x * σ x⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem hg_σ_inv {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (σ : G →* Matrix ι ι K) (x : G) : (σ x)⁻¹ = σ x⁻¹ :=
  Matrix.inv_eq_right_inv (hg_σ_mul_inv σ x)

theorem hg_σ_inv_mulVec {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (σ : G →* Matrix ι ι K) (x : G) (v : ι → K) :
    σ x⁻¹ *ᵥ (σ x *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, hg_σ_inv_mul, Matrix.one_mulVec]

theorem hg_σ_mulVec_inv {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (σ : G →* Matrix ι ι K) (x : G) (v : ι → K) :
    σ x *ᵥ (σ x⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, hg_σ_mul_inv, Matrix.one_mulVec]

/-! ### The deck action on endpoints and faces -/

theorem hg_tgt_act {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (h : G) (ε : hg_Edge G r) :
    hg_tgt g (hg_actEdge h ε) = hg_actVert g h (hg_tgt g ε) := by
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;>
    simp [hg_tgt, hg_actEdge, hg_actVert, mul_assoc, ]

theorem hg_src_act {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (h : G) (ε : hg_Edge G r) :
    hg_src g (hg_actEdge h ε) = hg_actVert g h (hg_src g ε) := by
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;>
    simp [hg_src, hg_actEdge, hg_actVert, ]

theorem hg_actVert_mul {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (h k : G)
    (v : hg_Vert g) : hg_actVert g h (hg_actVert g k v) = hg_actVert g (h * k) v := by
  rcases v with x | x | ⟨i, c⟩ <;> simp [hg_actVert, mul_assoc, mul_smul]

theorem hg_actEdge_mul {G : Type*} [Group G] {r : ℕ} (h k : G) (ε : hg_Edge G r) :
    hg_actEdge h (hg_actEdge k ε) = hg_actEdge (h * k) ε := by
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;> simp [hg_actEdge, mul_assoc]

theorem hg_actVert_one {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (v : hg_Vert g) :
    hg_actVert g 1 v = v := by
  rcases v with x | x | ⟨i, c⟩ <;> simp [hg_actVert]

theorem hg_delta0_eq {G : Type*} [Group G] {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {r : ℕ} (g : Fin r → G) (φ : hg_Vert g → M)
    (ε : hg_Edge G r) : hg_delta0 R M g φ ε = φ (hg_tgt g ε) - φ (hg_src g ε) := rfl

theorem hg_delta1_eq {G : Type*} [Group G] {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {r : ℕ} (g : Fin r → G) (c : hg_Edge G r → M)
    (τ : hg_Tri G r) :
    hg_delta1 R M g c τ = c (hg_face0 g τ) - c (hg_face1 τ) + c (hg_face2 τ) := rfl

/-- `δ⁰` maps equivariant `0`-cochains to equivariant `1`-cochains. -/
theorem hg_delta0_mem_eqCochain1 {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (φ : hg_Vert g → ι → K) (hφ : φ ∈ hg_eqCochain0 σ g) :
    hg_delta0 K (ι → K) g φ ∈ hg_eqCochain1 σ := by
  intro h ε
  rw [hg_delta0_eq, hg_delta0_eq, hg_tgt_act, hg_src_act, hφ h, hφ h, Matrix.mulVec_sub]

/-! ### Statement 1 -/

theorem hg_delta_comp_lemma {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (hprod : (List.ofFn g).prod = 1) :
    hg_delta1 R M g ∘ₗ hg_delta0 R M g = 0 := by
  ext φ τ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply]
  rw [hg_delta1_eq, hg_delta0_eq, hg_delta0_eq, hg_delta0_eq]
  rcases τ with ⟨i, x⟩ | ⟨i, x⟩
  · simp only [hg_face0, hg_face1, hg_face2, hg_src, hg_tgt]
    abel
  · simp only [hg_face0, hg_face1, hg_face2, hg_src, hg_tgt]
    have hQ : x * (g i)⁻¹ * (hg_Q g i)⁻¹ = x * (hg_Q g (finRotate r i))⁻¹ := by
      rw [hg_Q_rotate g hprod, _root_.mul_inv_rev, mul_assoc]
    have hc : ((x * (g i)⁻¹ : G) : G ⧸ Subgroup.zpowers (g i)) = (x : G ⧸ _) := by
      rw [QuotientGroup.eq]
      simp
    rw [hQ, hc]
    abel

/-! ### Statement 8 -/

theorem hg_fundEval_delta1_lemma {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {G : Type*} [Group G] [Fintype G] {r : ℕ} (g : Fin r → G)
    (c : hg_Edge G r → M) :
    hg_fundEval (hg_delta1 R M g c) = 0 := by
  simp only [hg_fundEval, hg_delta1_eq, hg_face0, hg_face1, hg_face2]
  have h1 : ∀ i : Fin r, ∑ x : G, c (Sum.inr (Sum.inr (i, x * (g i)⁻¹))) =
      ∑ x : G, c (Sum.inr (Sum.inr (i, x))) := fun i =>
    Fintype.sum_equiv (Equiv.mulRight (g i)⁻¹) _ _ (fun _ => rfl)
  have h2 : ∑ i : Fin r, ∑ x : G, c (Sum.inr (Sum.inl (finRotate r i, x))) =
      ∑ i : Fin r, ∑ x : G, c (Sum.inr (Sum.inl (i, x))) :=
    Fintype.sum_equiv (finRotate r) _ _ (fun _ => rfl)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2]
  abel

/-! ### The Shapiro map -/

section Shapiro

variable {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)

theorem hg_shapiro_e (a : Fin r → ι → K) (i : Fin r) (x : G) :
    hg_shapiroCochain σ g a (Sum.inl (i, x)) = σ x *ᵥ a i := rfl

theorem hg_shapiro_f (a : Fin r → ι → K) (i : Fin r) (x : G) :
    hg_shapiroCochain σ g a (Sum.inr (Sum.inl (i, x))) =
      -(σ x *ᵥ (σ (hg_Q g i)⁻¹ *ᵥ pc_F (pc_tuple σ g) a i)) := rfl

theorem hg_shapiro_h (a : Fin r → ι → K) (i : Fin r) (x : G) :
    hg_shapiroCochain σ g a (Sum.inr (Sum.inr (i, x))) =
      -(σ x *ᵥ (σ (hg_Q g i)⁻¹ *ᵥ pc_F (pc_tuple σ g) a i + a i)) := rfl

/-- One step of the recursion `F_{i+1} = F_i + Q_i c_i`, written on the sheet `Q_{i+1}`. -/
theorem hg_shapiro_step (a : Fin r → ι → K) (i : Fin r) :
    σ (g i)⁻¹ *ᵥ (σ (hg_Q g i)⁻¹ *ᵥ pc_F (pc_tuple σ g) a i + a i) - a i =
      σ (hg_Q g i * g i)⁻¹ *ᵥ pc_Fn (pc_tuple σ g) a (i + 1) := by
  rw [pc_Fn_succ, ← pc_F_eq_Fn, hg_pc_Q, _root_.mul_inv_rev, map_mul, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_add, hg_σ_inv_mulVec, pc_c, Matrix.sub_mulVec,
    Matrix.one_mulVec]
  simp only [pc_tuple, Matrix.mulVec_add, Matrix.mulVec_sub, hg_σ_inv_mulVec]
  abel

/-- The value on `f_{i+1}` from the value on `f_i` and `h_i`, for `a ∈ Z` (at `i = r − 1` this
is the relation `Σ_i Q_i c_i = 0`). -/
theorem hg_shapiro_rotate (a : Fin r → ι → K) (ha : a ∈ pc_Z (pc_tuple σ g)) (i : Fin r) :
    σ (hg_Q g (finRotate r i))⁻¹ *ᵥ pc_F (pc_tuple σ g) a (finRotate r i) =
      σ (g i)⁻¹ *ᵥ (σ (hg_Q g i)⁻¹ *ᵥ pc_F (pc_tuple σ g) a i + a i) - a i := by
  rw [hg_shapiro_step, pc_F_eq_Fn]
  by_cases h : (i : ℕ) + 1 = r
  · have h0 : ((finRotate r i : Fin r) : ℕ) = 0 := by rw [hg_finRotate_val]; simp [h]
    rw [h0, pc_Fn_zero, h, pc_Fn_r, ha, Matrix.mulVec_zero, Matrix.mulVec_zero]
  · have hlt : (i : ℕ) + 1 < r := by omega
    have hrot : finRotate r i = ⟨i + 1, hlt⟩ := Fin.ext (by rw [hg_finRotate_val]; simp [h])
    rw [hrot, hg_Q_succ g i hlt]

/-! ### Statement 4 -/

theorem hg_shapiro_cocycle_lemma (a : Fin r → ι → K) (ha : a ∈ pc_Z (pc_tuple σ g)) :
    hg_shapiroCochain σ g a ∈ LinearMap.ker (hg_delta1 K (ι → K) g) := by
  rw [LinearMap.mem_ker]
  funext τ
  rw [hg_delta1_eq]
  rcases τ with ⟨i, x⟩ | ⟨i, x⟩
  · simp only [hg_face0, hg_face1, hg_face2, hg_shapiro_e, hg_shapiro_f, hg_shapiro_h,
      Matrix.mulVec_add, Pi.zero_apply]
    abel
  · simp only [hg_face0, hg_face1, hg_face2, hg_shapiro_e, hg_shapiro_f, hg_shapiro_h,
      Pi.zero_apply]
    rw [hg_shapiro_rotate σ g a ha i, map_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    abel

/-! ### Statement 9 -/

theorem hg_cup_shapiro_lemma [Fintype G] [StarRing K] (H : Matrix ι ι K) (hHerm : Hᴴ = H)
    (hinv : ∀ x, (σ x)ᴴ * H * σ x = H) (a b : Fin r → ι → K) :
    hg_fundEval (hg_cup g H (hg_shapiroCochain σ g a) (hg_shapiroCochain σ g b)) =
      -((Fintype.card G : K) * star (pc_S (pc_tuple σ g) H b a)) := by
  have key : ∀ (i : Fin r) (x : G) (y : ι → K),
      star (σ x *ᵥ a i) ⬝ᵥ (H *ᵥ -(σ x *ᵥ y)) -
          star (σ x *ᵥ a i) ⬝ᵥ (H *ᵥ -(σ (x * (g i)⁻¹) *ᵥ y)) =
        -(star (pc_c (pc_tuple σ g) a i) ⬝ᵥ (H *ᵥ y)) := by
    intro i x y
    rw [map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_neg, ← Matrix.mulVec_neg,
      pc_form_invariant H (σ x) (hinv x), pc_form_invariant H (σ x) (hinv x)]
    have hg := pc_form_invariant H (σ (g i)) (hinv _) (a i) (σ (g i)⁻¹ *ᵥ y)
    rw [hg_σ_mulVec_inv] at hg
    simp only [pc_c, pc_tuple, Matrix.sub_mulVec, Matrix.one_mulVec, star_sub, sub_dotProduct,
      Matrix.mulVec_neg, dotProduct_neg]
    rw [hg]
    ring
  simp only [hg_fundEval, hg_cup, hg_face0, hg_face2, hg_shapiro_e, hg_shapiro_h, key,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [pc_S, star_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pc_form_star H hHerm, hg_pc_Q, hg_σ_inv]
  ring

/-! ### Statement 7 -/

theorem hg_eqCoboundary_average_lemma [Fintype G] (hG : (Fintype.card G : K) ≠ 0)
    (c : hg_Edge G r → ι → K) (hc : c ∈ hg_eqCochain1 σ)
    (hcb : c ∈ LinearMap.range (hg_delta0 K (ι → K) g)) :
    c ∈ hg_eqCoboundaries σ g := by
  obtain ⟨φ, rfl⟩ := hcb
  set n : K := (Fintype.card G : K)
  let ψ : hg_Vert g → ι → K := fun v => n⁻¹ • ∑ h : G, σ h *ᵥ φ (hg_actVert g h⁻¹ v)
  refine ⟨ψ, fun k v => ?_, ?_⟩
  · simp only [ψ, hg_actVert_mul, Matrix.mulVec_smul, Matrix.mulVec_sum]
    congr 1
    rw [← Equiv.sum_comp (Equiv.mulLeft k)]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [Equiv.coe_mulLeft, _root_.mul_inv_rev, map_mul, mul_assoc, inv_mul_cancel,
      mul_one, Matrix.mulVec_mulVec]
  · funext ε
    simp only [hg_delta0_eq, ψ, ← smul_sub, ← Finset.sum_sub_distrib, ← Matrix.mulVec_sub]
    have : ∀ h : G, φ (hg_actVert g h⁻¹ (hg_tgt g ε)) - φ (hg_actVert g h⁻¹ (hg_src g ε)) =
        σ h⁻¹ *ᵥ hg_delta0 K (ι → K) g φ ε := fun h => by
      rw [← hg_tgt_act, ← hg_src_act, ← hg_delta0_eq (R := K), hc]
    simp only [this, hg_σ_mulVec_inv, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hG, one_smul]
    rfl

/-! ### Statement 5 -/

theorem hg_fixed_zpowers (i : Fin r) (k : ι → K) (hk : σ (g i) *ᵥ k = k) :
    ∀ h ∈ Subgroup.zpowers (g i), σ h *ᵥ k = k := by
  let S : Subgroup G :=
    { carrier := {h | σ h *ᵥ k = k}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, ← Matrix.mulVec_mulVec, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [hg_σ_inv_mulVec] }
  exact fun h hh => (Subgroup.zpowers_le (H := S)).mpr hk hh

theorem hg_mem_localFixed_iff (i : Fin r) (k : ι → K) :
    k ∈ pc_localFixed (pc_tuple σ g) i ↔ σ (g i) *ᵥ k = k := by
  simp only [pc_localFixed, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec, sub_eq_zero, pc_tuple]

theorem hg_shapiro_coboundary_iff_lemma (a : Fin r → ι → K) :
    hg_shapiroCochain σ g a ∈ hg_eqCoboundaries σ g ↔ a ∈ pc_trivialPart (pc_tuple σ g) := by
  constructor
  · rintro ⟨φ, hφ, hδ⟩
    have he : ∀ i, a i = φ (Sum.inr (Sum.inr ⟨i, ((1 : G) : G ⧸ Subgroup.zpowers (g i))⟩)) -
        φ (Sum.inl 1) := fun i => by
      have := congrFun hδ (Sum.inl (i, 1))
      rw [hg_delta0_eq, hg_shapiro_e, map_one, Matrix.one_mulVec] at this
      exact this.symm
    refine Submodule.mem_sup.mpr ⟨fun _ => -φ (Sum.inl 1), ⟨-φ (Sum.inl 1), rfl⟩,
      fun i => φ (Sum.inr (Sum.inr ⟨i, ((1 : G) : G ⧸ Subgroup.zpowers (g i))⟩)), ?_, ?_⟩
    · rw [pc_localPart, Submodule.mem_pi]
      intro i _
      rw [hg_mem_localFixed_iff, ← hφ (g i)]
      have h1 : ((g i : G) : G ⧸ Subgroup.zpowers (g i)) = ((1 : G) : G ⧸ _) := by
        rw [QuotientGroup.eq]
        simp
      simp only [hg_actVert, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, h1]
    · funext i
      rw [he i]
      simp only [Pi.add_apply]
      abel
  · intro ha
    obtain ⟨y, ⟨v, hv⟩, z, hz, hyz⟩ := Submodule.mem_sup.mp ha
    have hai : ∀ i, a i = v + z i := fun i => by
      rw [← hyz, ← hv]
      rfl
    have hz' : ∀ i, σ (g i) *ᵥ z i = z i := fun i =>
      (hg_mem_localFixed_iff σ g i (z i)).mp ((Submodule.mem_pi.mp hz) i (Set.mem_univ _))
    let φ : hg_Vert g → ι → K :=
      Sum.elim (fun x => -(σ x *ᵥ v)) (Sum.elim (fun x => -(σ x *ᵥ v))
        (fun p => Quotient.liftOn' p.2 (fun x => σ x *ᵥ z p.1) fun x y hxy => by
          have hm := QuotientGroup.leftRel_apply.mp hxy
          rw [show y = x * (x⁻¹ * y) by group, map_mul, ← Matrix.mulVec_mulVec,
            hg_fixed_zpowers σ g p.1 (z p.1) (hz' p.1) _ hm]))
    have hF : ∀ i, σ (hg_Q g i)⁻¹ *ᵥ
        pc_F (pc_tuple σ g) a i = σ (hg_Q g i)⁻¹ *ᵥ v - v := by
      intro i
      have hc : pc_F (pc_tuple σ g) a i =
          pc_F (pc_tuple σ g) (fun _ => v) i := by
        simp only [pc_F, pc_c]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hai, Matrix.mulVec_add,
          Matrix.sub_mulVec, Matrix.one_mulVec, pc_tuple, hz', sub_self, add_zero]
      rw [hc, pc_F_eq_Fn, pc_Fn_const _ v i i.isLt.le, ← pc_Q_eq_take, hg_pc_Q,
        Matrix.mulVec_sub, hg_σ_inv_mulVec]
    refine ⟨φ, fun h w => ?_, ?_⟩
    · rcases w with x | x | ⟨i, q⟩
      · simp [φ, hg_actVert, map_mul, Matrix.mulVec_neg, Matrix.mulVec_mulVec]
      · simp [φ, hg_actVert, map_mul, Matrix.mulVec_neg, Matrix.mulVec_mulVec]
      · induction q using QuotientGroup.induction_on with
        | H x =>
          change σ (h * x) *ᵥ z i = σ h *ᵥ (σ x *ᵥ z i)
          rw [map_mul, Matrix.mulVec_mulVec]
    · funext ε
      rw [hg_delta0_eq]
      rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
      · change σ x *ᵥ z i - -(σ x *ᵥ v) = hg_shapiroCochain σ g _ (Sum.inl (i, x))
        rw [hg_shapiro_e, hai, Matrix.mulVec_add]
        abel
      · change -(σ (x * (hg_Q g i)⁻¹) *ᵥ v) - -(σ x *ᵥ v) =
          hg_shapiroCochain σ g _ (Sum.inr (Sum.inl (i, x)))
        rw [hg_shapiro_f, hF, map_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
        abel
      · change -(σ (x * (hg_Q g i)⁻¹) *ᵥ v) - σ x *ᵥ z i =
          hg_shapiroCochain σ g _ (Sum.inr (Sum.inr (i, x)))
        rw [hg_shapiro_h, hF, map_mul, ← Matrix.mulVec_mulVec, hai]
        simp only [Matrix.mulVec_add, Matrix.mulVec_sub]
        abel

/-! ### Statement 6 -/

theorem hg_shapiro_surjective_lemma (hprod : (List.ofFn g).prod = 1) (c : hg_Edge G r → ι → K)
    (hc : c ∈ hg_eqCocycles σ g) :
    ∃ a ∈ pc_Z (pc_tuple σ g), c - hg_shapiroCochain σ g a ∈ hg_eqCoboundaries σ g := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    have : c - hg_shapiroCochain σ g 0 = 0 := by
      funext ε
      rcases ε with ⟨i, _⟩ | ⟨i, _⟩ | ⟨i, _⟩ <;> exact i.elim0
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨hc1, hc2⟩ := hc
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hc2
  set i0 : Fin r := ⟨0, hr⟩
  set w := c (Sum.inr (Sum.inl (i0, 1)))
  let ψ0 : hg_Vert g → ι → K := Sum.elim 0 (Sum.elim (fun y => σ y *ᵥ w) 0)
  have hψ0 : ψ0 ∈ hg_eqCochain0 σ g := by
    intro h v
    rcases v with x | x | ⟨i, q⟩
    · simp [ψ0, hg_actVert]
    · simp [ψ0, hg_actVert, map_mul, Matrix.mulVec_mulVec]
    · simp [ψ0, hg_actVert]
  obtain ⟨c', hc'⟩ : ∃ c', c' = c - hg_delta0 K (ι → K) g ψ0 := ⟨_, rfl⟩
  have hc'1 : c' ∈ hg_eqCochain1 σ :=
    hc' ▸ Submodule.sub_mem _ hc1 (hg_delta0_mem_eqCochain1 σ g ψ0 hψ0)
  have hc'2 : hg_delta1 K (ι → K) g c' = 0 := by
    rw [hc', map_sub, hc2, zero_sub, neg_eq_zero]
    exact LinearMap.congr_fun (hg_delta_comp_lemma g hprod) ψ0
  have hf0 : c' (Sum.inr (Sum.inl (i0, 1))) = 0 := by
    rw [hc', Pi.sub_apply, hg_delta0_eq]
    simp [ψ0, hg_tgt, hg_src, i0, hg_Q_zero g hr, w]
  obtain ⟨a, ha⟩ : ∃ a : Fin r → ι → K, ∀ i, a i = c' (Sum.inl (i, 1)) := ⟨_, fun _ => rfl⟩
  have heq : ∀ (ε : Fin r × G → hg_Edge G r), (∀ h i x, hg_actEdge h (ε (i, x)) = ε (i, h * x)) →
      ∀ i x, c' (ε (i, x)) = σ x *ᵥ c' (ε (i, 1)) := fun ε hε i x => by
    rw [← hc'1 x, hε, mul_one]
  have he := heq (fun p => Sum.inl p) (fun _ _ _ => rfl)
  have hf := heq (fun p => Sum.inr (Sum.inl p)) (fun _ _ _ => rfl)
  have hh := heq (fun p => Sum.inr (Sum.inr p)) (fun _ _ _ => rfl)
  have hA : ∀ i, c' (Sum.inr (Sum.inr (i, 1))) = c' (Sum.inr (Sum.inl (i, 1))) - a i := by
    intro i
    have := congrFun hc'2 (Sum.inl (i, 1))
    rw [hg_delta1_eq] at this
    simp only [hg_face0, hg_face1, hg_face2, Pi.zero_apply] at this
    rw [ha]
    rw [← sub_eq_zero, ← this]
    abel
  have hrec : ∀ i, c' (Sum.inr (Sum.inl (finRotate r i, 1))) =
      σ (g i)⁻¹ *ᵥ (c' (Sum.inr (Sum.inl (i, 1))) - a i) + a i := by
    intro i
    have := congrFun hc'2 (Sum.inr (i, 1))
    rw [hg_delta1_eq] at this
    simp only [hg_face0, hg_face1, hg_face2, Pi.zero_apply, one_mul] at this
    rw [hh, hA, ← ha] at this
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel
  have hu : ∀ n (hn : n < r), c' (Sum.inr (Sum.inl (⟨n, hn⟩, 1))) =
      -(σ (hg_Q g ⟨n, hn⟩)⁻¹ *ᵥ pc_F (pc_tuple σ g) a ⟨n, hn⟩) := by
    intro n
    induction n with
    | zero =>
      intro hn
      rw [hf0, pc_F_eq_Fn]
      simp [pc_Fn_zero]
    | succ n ih =>
      intro hn
      have hlt : n < r := by omega
      have hrot : finRotate r ⟨n, hlt⟩ = ⟨n + 1, hn⟩ :=
        Fin.ext (by rw [hg_finRotate_val]; simp; omega)
      rw [← hrot, hrec, ih hlt, hrot, hg_Q_succ g ⟨n, hlt⟩ hn]
      have e : pc_F (pc_tuple σ g) a ⟨n + 1, hn⟩ = pc_Fn (pc_tuple σ g) a (n + 1) :=
        pc_F_eq_Fn _ _ _
      rw [e, ← hg_shapiro_step σ g a ⟨n, hlt⟩]
      simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_neg]
      abel
  have hZ : a ∈ pc_Z (pc_tuple σ g) := by
    have hlt : r - 1 < r := by omega
    have hrot : finRotate r ⟨r - 1, hlt⟩ = i0 :=
      Fin.ext (by rw [hg_finRotate_val]; simp [i0]; omega)
    have h1 := hrec ⟨r - 1, hlt⟩
    rw [hrot, hf0, hu (r - 1) hlt] at h1
    have h2 := hg_shapiro_step σ g a ⟨r - 1, hlt⟩
    have h3 : σ (hg_Q g ⟨r - 1, hlt⟩ * g ⟨r - 1, hlt⟩)⁻¹ *ᵥ
        pc_Fn (pc_tuple σ g) a (((⟨r - 1, hlt⟩ : Fin r) : ℕ) + 1) = 0 := by
      rw [← h2, ← neg_eq_zero]
      convert h1.symm using 1
      simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_neg]
      abel
    have hr1 : ((⟨r - 1, hlt⟩ : Fin r) : ℕ) + 1 = r := by simp; omega
    have h4 := congrArg (fun v => σ (hg_Q g ⟨r - 1, hlt⟩ * g ⟨r - 1, hlt⟩) *ᵥ v) h3
    simp only [hg_σ_mulVec_inv, Matrix.mulVec_zero] at h4
    rw [hr1, pc_Fn_r] at h4
    exact h4
  have hΦ : c' = hg_shapiroCochain σ g a := by
    funext ε
    rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
    · rw [he, hg_shapiro_e, ha]
    · rw [hf, hg_shapiro_f, hu i i.isLt, Matrix.mulVec_neg]
    · rw [hh, hg_shapiro_h, hA, hu i i.isLt]
      simp only [Fin.eta, Matrix.mulVec_neg, Matrix.mulVec_sub, Matrix.mulVec_add]
      abel
  refine ⟨a, hZ, ψ0, hψ0, ?_⟩
  rw [← hΦ, hc', sub_sub_cancel]

end Shapiro

end HodgeLean.Foundations.Program
