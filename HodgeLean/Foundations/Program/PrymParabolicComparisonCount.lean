import HodgeLean.Foundations.Program.PrymParabolicComparisonLemmas

/-! # Counting lemmas for stage H3a: connectivity and the Riemann–Hurwitz count

Locally constant `0`-cochains on the lifted complex are constant for a generating tuple; the
boundary of a `2`-chain on each edge, and the `2`-chains with zero boundary.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Matrix

namespace HodgeLean.Foundations.Program

/-! ### Statement 2 -/

theorem hg_ker_delta0_const {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (hr : 0 < r)
    (hg : Subgroup.closure (Set.range g) = ⊤) (φ : hg_Vert g → M)
    (hφ : φ ∈ LinearMap.ker (hg_delta0 R M g)) : ∀ v, φ v = φ (Sum.inl 1) := by
  rw [LinearMap.mem_ker] at hφ
  have hδ : ∀ ε, φ (hg_tgt g ε) = φ (hg_src g ε) := fun ε => by
    have := congrFun hφ ε
    rwa [hg_delta0_eq, Pi.zero_apply, sub_eq_zero] at this
  have hp : ∀ i (x : G), φ (Sum.inr (Sum.inr ⟨i, (x : G ⧸ Subgroup.zpowers (g i))⟩)) =
      φ (Sum.inl x) := fun i x => hδ (Sum.inl (i, x))
  have hb : ∀ i (y : G), φ (Sum.inl (y * g i)) = φ (Sum.inl y) := fun i y => by
    rw [← hp, ← hp]
    have : ((y * g i : G) : G ⧸ Subgroup.zpowers (g i)) = (y : G ⧸ _) := by
      rw [QuotientGroup.eq]
      simp
    rw [this]
  have hall : ∀ x : G, ∀ y, φ (Sum.inl (y * x)) = φ (Sum.inl y) := by
    intro x
    have hx : x ∈ Subgroup.closure (Set.range g) := hg ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hb i
    | one => simp
    | mul x y _ _ ihx ihy => intro z; rw [← mul_assoc, ihy, ihx]
    | inv x _ ih => intro z; rw [← ih (z * x⁻¹), inv_mul_cancel_right]
  have hb0 : ∀ x, φ (Sum.inl x) = φ (Sum.inl 1) := fun x => by
    rw [← hall x 1, one_mul]
  intro v
  rcases v with x | x | ⟨i, q⟩
  · exact hb0 x
  · have := hδ (Sum.inr (Sum.inl (⟨0, hr⟩, x)))
    simp only [hg_tgt, hg_src, hg_Q_zero g hr, inv_one, mul_one] at this
    rw [this, hb0]
  · induction q using QuotientGroup.induction_on with
    | H x => rw [hp, hb0]

theorem hg_H0_finrank_lemma (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G)
    (hr : 0 < r) (hg : Subgroup.closure (Set.range g) = ⊤) :
    Module.finrank K (LinearMap.ker (hg_delta0 K K g)) = 1 := by
  have h1 : (fun _ => (1 : K)) ∈ LinearMap.ker (hg_delta0 K K g) := by
    rw [LinearMap.mem_ker]
    funext ε
    simp [hg_delta0_eq]
  refine (finrank_eq_one_iff_of_nonzero' (⟨_, h1⟩ : LinearMap.ker (hg_delta0 K K g))
    ?_).mpr ?_
  · intro h
    have := congrFun (congrArg Subtype.val h) (Sum.inl 1)
    simp at this
  · rintro ⟨φ, hφ⟩
    refine ⟨φ (Sum.inl 1), ?_⟩
    ext v
    simp [hg_ker_delta0_const g hr hg φ hφ v]

/-! ### Statement 3 -/

theorem hg_dot_delta1 {K : Type*} [Field K] {G : Type*} [Group G] [Fintype G] {r : ℕ}
    (g : Fin r → G) (w : hg_Tri G r → K) (c : hg_Edge G r → K) :
    ∑ τ, w τ * hg_delta1 K K g c τ =
      ∑ i, ∑ x, ((w (Sum.inl (i, x)) + w (Sum.inr (i, x))) * c (Sum.inl (i, x)) +
        (w (Sum.inl (i, x)) + w (Sum.inr (i, x * g i))) * c (Sum.inr (Sum.inr (i, x))) -
        (w (Sum.inl (i, x)) + w (Sum.inr ((finRotate r).symm i, x))) *
          c (Sum.inr (Sum.inl (i, x)))) := by
  have h1 : ∀ i : Fin r, ∑ x : G, w (Sum.inr (i, x)) * c (Sum.inr (Sum.inr (i, x * (g i)⁻¹))) =
      ∑ x : G, w (Sum.inr (i, x * g i)) * c (Sum.inr (Sum.inr (i, x))) := fun i =>
    Fintype.sum_equiv (Equiv.mulRight (g i)⁻¹) _ _ (fun x => by simp)
  have h2 : ∑ i : Fin r, ∑ x : G, w (Sum.inr (i, x)) * c (Sum.inr (Sum.inl (finRotate r i, x))) =
      ∑ i : Fin r, ∑ x : G, w (Sum.inr ((finRotate r).symm i, x)) *
        c (Sum.inr (Sum.inl (i, x))) :=
    Fintype.sum_equiv (finRotate r) _ _ (fun i => by simp only [Equiv.symm_apply_apply])
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, hg_delta1_eq, hg_face0, hg_face1,
    hg_face2, mul_add, mul_sub, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2]
  ring

theorem hg_annihilator_eq {K : Type*} [Field K] {G : Type*} [Group G] [Fintype G] {r : ℕ}
    (g : Fin r → G) (hr : 0 < r) (hg : Subgroup.closure (Set.range g) = ⊤)
    (w : hg_Tri G r → K) (hw : ∀ c, ∑ τ, w τ * hg_delta1 K K g c τ = 0) :
    w = w (Sum.inl (⟨0, hr⟩, 1)) • fun τ => Sum.elim (fun _ => 1) (fun _ => -1) τ := by
  classical
  have he : ∀ i x, w (Sum.inl (i, x)) + w (Sum.inr (i, x)) = 0 := fun i x => by
    have := hw (fun ε => if ε = Sum.inl (i, x) then 1 else 0)
    rw [hg_dot_delta1] at this
    simpa [ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq] using this
  have hh : ∀ i x, w (Sum.inl (i, x)) + w (Sum.inr (i, x * g i)) = 0 := fun i x => by
    have := hw (fun ε => if ε = Sum.inr (Sum.inr (i, x)) then 1 else 0)
    rw [hg_dot_delta1] at this
    simpa [ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq] using this
  have hf : ∀ i x, w (Sum.inl (i, x)) + w (Sum.inr ((finRotate r).symm i, x)) = 0 :=
    fun i x => by
    have := hw (fun ε => if ε = Sum.inr (Sum.inl (i, x)) then 1 else 0)
    rw [hg_dot_delta1] at this
    simp [ite_and, Finset.sum_ite_eq'] at this ⊢
    linear_combination -this
  have hAg : ∀ i x, w (Sum.inl (i, x * g i)) = w (Sum.inl (i, x)) := fun i x => by
    linear_combination he i (x * g i) - hh i x
  have hArot : ∀ i x, w (Sum.inl (finRotate r i, x)) = w (Sum.inl (i, x)) := fun i x => by
    have := hf (finRotate r i) x
    rw [Equiv.symm_apply_apply] at this
    linear_combination this - he i x
  have hAi : ∀ i x, w (Sum.inl (i, x)) = w (Sum.inl (⟨0, hr⟩, x)) := by
    intro i x
    obtain ⟨n, hn⟩ := i
    induction n with
    | zero => rfl
    | succ n ih =>
      have hrot : finRotate r ⟨n, by omega⟩ = ⟨n + 1, hn⟩ := Fin.ext (by
        rw [hg_finRotate_val]
        simp only
        split_ifs with h <;> omega)
      rw [← ih (by omega), ← hrot, hArot]
  have hAx : ∀ x : G, ∀ y, w (Sum.inl (⟨0, hr⟩, y * x)) = w (Sum.inl (⟨0, hr⟩, y)) := by
    intro x
    have hx : x ∈ Subgroup.closure (Set.range g) := hg ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro y
      rw [← hAi j, hAg, hAi]
    | one => simp
    | mul x y _ _ ihx ihy => intro z; rw [← mul_assoc, ihy, ihx]
    | inv x _ ih => intro z; rw [← ih (z * x⁻¹), inv_mul_cancel_right]
  have hA : ∀ i x, w (Sum.inl (i, x)) = w (Sum.inl (⟨0, hr⟩, 1)) := fun i x => by
    rw [hAi, ← hAx x 1, one_mul]
  funext τ
  rcases τ with ⟨i, x⟩ | ⟨i, x⟩
  · simp [hA i x]
  · have := he i x
    simp only [Pi.smul_apply, Sum.elim_inr, smul_eq_mul, mul_neg, mul_one]
    linear_combination this - hA i x

theorem hg_finrank_range_delta1 (K : Type*) [Field K] {G : Type*} [Group G] [Fintype G]
    {r : ℕ} (g : Fin r → G) (hr : 0 < r) (hg : Subgroup.closure (Set.range g) = ⊤) :
    Module.finrank K (LinearMap.range (hg_delta1 K K g)) + 1 = Nat.card (hg_Tri G r) := by
  classical
  set D := hg_delta1 K K g
  set A := LinearMap.toMatrix' D
  have hD : ∀ c, D c = A *ᵥ c := fun c => by
    rw [← Matrix.mulVecLin_apply]
    exact (LinearMap.congr_fun (Matrix.toLin'_toMatrix' D) c).symm
  have hdot : ∀ v c, ∑ τ, v τ * D c τ = (Aᵀ *ᵥ v) ⬝ᵥ c := fun v c => by
    rw [hD, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    rfl
  set o : hg_Tri G r → K := fun τ => Sum.elim (fun _ => 1) (fun _ => -1) τ
  have hzero : ∀ v, (∀ c, (Aᵀ *ᵥ v) ⬝ᵥ c = 0) → Aᵀ *ᵥ v = 0 := fun v hv => by
    funext ε
    simpa using hv (Pi.single ε 1)
  have hker : LinearMap.ker Aᵀ.mulVecLin = K ∙ o := by
    ext w
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_span_singleton]
    constructor
    · intro hw
      refine ⟨w (Sum.inl (⟨0, hr⟩, 1)), ?_⟩
      refine (hg_annihilator_eq g hr hg w fun c => ?_).symm
      rw [hdot, hw, zero_dotProduct]
    · rintro ⟨t, rfl⟩
      rw [Matrix.mulVec_smul]
      have : Aᵀ *ᵥ o = 0 := hzero o fun c => by
        rw [← hdot, hg_dot_delta1]
        simp [o]
      rw [this, smul_zero]
  have ho : o ≠ 0 := fun h => by
    have := congrFun h (Sum.inl (⟨0, hr⟩, 1))
    simp [o] at this
  have hrank : Module.finrank K (LinearMap.range D) = A.rank := by
    rw [Matrix.rank]
    have : A.mulVecLin = D := Matrix.toLin'_toMatrix' D
    rw [this]
  rw [hrank, ← Matrix.rank_transpose, Matrix.rank, ← finrank_span_singleton (K := K) ho, ← hker,
    LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

theorem hg_H1_finrank_lemma (K : Type*) [Field K] {G : Type*} [Group G] [Finite G] {r : ℕ}
    (g : Fin r → G) (hprod : (List.ofFn g).prod = 1)
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    (Module.finrank K (hg_H1 K g) : ℤ) + 2 * Nat.card G +
        ∑ i, (Nat.card (G ⧸ Subgroup.zpowers (g i)) : ℤ) =
      r * Nat.card G + 2 := by
  classical
  cases nonempty_fintype G
  obtain rfl | hr := Nat.eq_zero_or_pos r
  · have hG : Nat.card G = 1 := by
      rw [← Subgroup.card_top, ← hg, Set.range_eq_empty, Subgroup.closure_empty,
        Subgroup.card_bot]
    have hZ : Module.finrank K (LinearMap.ker (hg_delta1 K K g)) = 0 := by
      apply Nat.eq_zero_of_le_zero
      refine (Submodule.finrank_le _).trans ?_
      simp
    have := Submodule.finrank_quotient_le
      ((LinearMap.range (hg_delta0 K K g)).comap (LinearMap.ker (hg_delta1 K K g)).subtype)
    have hH : Module.finrank K (hg_H1 K g) = 0 := by
      exact Nat.le_zero.mp (this.trans hZ.le)
    rw [hG, hH]
    simp
  · have hle : LinearMap.range (hg_delta0 K K g) ≤ LinearMap.ker (hg_delta1 K K g) :=
      LinearMap.range_le_ker_iff.mpr (hg_delta_comp_lemma g hprod)
    have h1 := Submodule.finrank_quotient_add_finrank
      ((LinearMap.range (hg_delta0 K K g)).comap (LinearMap.ker (hg_delta1 K K g)).subtype)
    rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h1
    have h2 := LinearMap.finrank_range_add_finrank_ker (hg_delta0 K K g)
    have h3 := LinearMap.finrank_range_add_finrank_ker (hg_delta1 K K g)
    have h4 := hg_finrank_range_delta1 K g hr hg
    rw [hg_H0_finrank_lemma K g hr hg] at h2
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card, Nat.card_sum,
      Nat.card_prod, Nat.card_sigma, Nat.card_fin]
      at h2 h3 h4
    change Module.finrank K (hg_H1 K g) + _ = _ at h1
    zify at h1 h2 h3 h4
    linarith

end HodgeLean.Foundations.Program
