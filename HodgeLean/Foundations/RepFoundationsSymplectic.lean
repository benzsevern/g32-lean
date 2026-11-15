import HodgeLean.Foundations.RepFoundationsPairing

/-! # Representation foundations: symplectic determinants

A nondegenerate alternating form on a finite-dimensional space has a basis with Gram matrix the
standard `J`, so an endomorphism preserving the form has a symplectic matrix and determinant one
(`Matrix.SymplecticGroup.det_eq_one`). Applied to the pairing of a multiplicity space with
itself, this gives the orthogonal case of the multiplicity determinants.
-/

noncomputable section

namespace HodgeLean.Foundations

open CategoryTheory Matrix

theorem rfd_J_inl_inl {n : ℕ} (a b : Fin n) :
    Matrix.J (Fin n) ℂ (Sum.inl a) (Sum.inl b) = 0 := by
  simp [Matrix.J]

theorem rfd_J_inl_inr {n : ℕ} (a b : Fin n) :
    Matrix.J (Fin n) ℂ (Sum.inl a) (Sum.inr b) = -(if a = b then 1 else 0) := by
  simp [Matrix.J, Matrix.one_apply]

theorem rfd_J_inr_inl {n : ℕ} (a b : Fin n) :
    Matrix.J (Fin n) ℂ (Sum.inr a) (Sum.inl b) = if a = b then 1 else 0 := by
  simp [Matrix.J, Matrix.one_apply]

theorem rfd_J_inr_inr {n : ℕ} (a b : Fin n) :
    Matrix.J (Fin n) ℂ (Sum.inr a) (Sum.inr b) = 0 := by
  simp [Matrix.J]

/-- A nondegenerate alternating form has a family with Gram matrix `J` of full length. -/
theorem rfd_exists_sympFamily (k : ℕ) {M : Type} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (γ : LinearMap.BilinForm ℂ M) (halt : ∀ a, γ a a = 0)
    (hnd : ∀ a, (∀ b, γ a b = 0) → a = 0) (hk : Module.finrank ℂ M = k) :
    ∃ n, ∃ v : Fin n ⊕ Fin n → M, (∀ i j, γ (v i) (v j) = Matrix.J (Fin n) ℂ i j) ∧
      2 * n = Module.finrank ℂ M := by
  induction k using Nat.strong_induction_on generalizing M with
  | _ k ih =>
  have hskew : ∀ a b, γ a b = -γ b a := fun a b => by
    have h := halt (a + b)
    simp only [map_add, LinearMap.add_apply, halt a, halt b, zero_add, add_zero] at h
    linear_combination h
  by_cases h0 : Module.finrank ℂ M = 0
  · refine ⟨0, fun i => i.elim (fun a => a.elim0) (fun a => a.elim0),
      fun i => i.elim (fun a => a.elim0) (fun a => a.elim0), by rw [h0]⟩
  obtain ⟨e, he⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (Nat.pos_of_ne_zero h0)
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, γ e f₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact he (hnd e h)
  let f := (γ e f₀)⁻¹ • f₀
  have hef : γ e f = 1 := by simp [f, inv_mul_cancel₀ hf₀]
  have hfe : γ f e = -1 := by rw [hskew, hef]
  let L : M →ₗ[ℂ] ℂ × ℂ := LinearMap.prod (γ e) (γ f)
  let W := LinearMap.ker L
  have hW : ∀ w, w ∈ W ↔ γ e w = 0 ∧ γ f w = 0 := fun w => by
    simp [W, L, LinearMap.mem_ker]
  have hLsurj : LinearMap.range L = ⊤ := by
    refine LinearMap.range_eq_top.2 fun p => ⟨p.1 • f - p.2 • e, ?_⟩
    simp [L, hef, hfe, halt]
  have hdim : Module.finrank ℂ W + 2 = Module.finrank ℂ M := by
    have := LinearMap.finrank_range_add_finrank_ker L
    rw [hLsurj, finrank_top, Module.finrank_prod, Module.finrank_self] at this
    change 1 + 1 + Module.finrank ℂ W = _ at this
    omega
  let γ' : LinearMap.BilinForm ℂ W := γ.compl₁₂ W.subtype W.subtype
  have halt' : ∀ a, γ' a a = 0 := fun a => halt a
  have hnd' : ∀ a, (∀ b, γ' a b = 0) → a = 0 := by
    intro w hw
    refine Subtype.ext (hnd w fun x => ?_)
    have hr : x - ((γ e x) • f - (γ f x) • e) ∈ W := by
      rw [hW]
      simp [hef, hfe, halt]
    have h1 := hw ⟨_, hr⟩
    have hwe : γ w e = 0 := by rw [hskew, ((hW w).1 w.2).1, neg_zero]
    have hwf : γ w f = 0 := by rw [hskew, ((hW w).1 w.2).2, neg_zero]
    change γ w (x - ((γ e x) • f - (γ f x) • e)) = 0 at h1
    simpa [hwe, hwf] using h1
  obtain ⟨n, v, hv, hn⟩ := ih (Module.finrank ℂ W) (by omega) γ' halt' hnd' rfl
  have hvW : ∀ i, γ e (v i) = 0 ∧ γ f (v i) = 0 := fun i => (hW _).1 (v i).2
  have hvW' : ∀ i, γ (v i) e = 0 ∧ γ (v i) f = 0 := fun i =>
    ⟨by rw [hskew, (hvW i).1, neg_zero], by rw [hskew, (hvW i).2, neg_zero]⟩
  let w : Fin (n + 1) ⊕ Fin (n + 1) → M := fun i => i.elim
    (fun a => Fin.cases f (fun j => (v (Sum.inl j) : M)) a)
    (fun a => Fin.cases e (fun j => (v (Sum.inr j) : M)) a)
  refine ⟨n + 1, w, ?_, by omega⟩
  have hv' : ∀ i j, γ (v i) (v j) = Matrix.J (Fin n) ℂ i j := hv
  rintro (a | a) (b | b) <;> refine Fin.cases ?_ (fun a => ?_) a <;>
    refine Fin.cases ?_ (fun b => ?_) b <;>
    simp [w, rfd_J_inl_inl, rfd_J_inl_inr, rfd_J_inr_inl, rfd_J_inr_inr, halt, hef, hfe,
      hvW, hvW', Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm, hv']

/-- A family with Gram matrix `J` is linearly independent. -/
theorem rfd_sympFamily_linearIndependent {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (γ : LinearMap.BilinForm ℂ M) (v : Fin n ⊕ Fin n → M)
    (hv : ∀ i j, γ (v i) (v j) = Matrix.J (Fin n) ℂ i j) :
    LinearIndependent ℂ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hpair : ∀ j, ∑ i, g i * Matrix.J (Fin n) ℂ i j = 0 := fun j => by
    have := congrArg (fun x => γ x (v j)) hg
    simpa [map_sum, hv] using this
  rintro (a | a)
  · have := hpair (Sum.inr a)
    simpa [Fintype.sum_sum_type, rfd_J_inl_inr, rfd_J_inr_inr] using this
  · have := hpair (Sum.inl a)
    simpa [Fintype.sum_sum_type, rfd_J_inl_inl, rfd_J_inr_inl] using this

/-- An endomorphism preserving a nondegenerate alternating form has determinant one. -/
theorem rfd_det_eq_one_of_alt {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (γ : LinearMap.BilinForm ℂ M) (halt : ∀ a, γ a a = 0)
    (hnd : ∀ a, (∀ b, γ a b = 0) → a = 0) (A : Module.End ℂ M)
    (hA : ∀ a b, γ (A a) (A b) = γ a b) : LinearMap.det A = 1 := by
  obtain ⟨n, v, hv, hn⟩ := rfd_exists_sympFamily _ γ halt hnd rfl
  have hli := rfd_sympFamily_linearIndependent γ v hv
  let b := Module.Basis.mk hli
    (hli.span_eq_top_of_card_eq_finrank' (by simp; omega)).ge
  have hb : ∀ i, b i = v i := fun i => by simp [b]
  have hG : LinearMap.toMatrix₂ b b γ = Matrix.J (Fin n) ℂ := by
    ext i j
    rw [LinearMap.toMatrix₂_apply, hb, hb, hv]
  have hγA : γ.compl₁₂ A A = γ := LinearMap.ext₂ hA
  have hmat : (LinearMap.toMatrix b b A)ᵀ * Matrix.J (Fin n) ℂ *
      LinearMap.toMatrix b b A = Matrix.J (Fin n) ℂ := by
    rw [← hG, ← LinearMap.toMatrix₂_compl₁₂ b b b b, hγA]
  rw [← LinearMap.det_toMatrix b]
  exact SymplecticGroup.det_eq_one (SymplecticGroup.mem_iff'.2 hmat)

variable {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

theorem rfd_det_orthogonal' (ρ : Representation ℂ G V) (ω : LinearMap.BilinForm ℂ V)
    (hω : ω.Nondegenerate) (hωalt : ω.IsAlt) (hωG : ∀ g x y, ω (ρ g x) (ρ g y) = ω x y)
    (σ : FDRep ℂ G) (hσ : Simple σ) (hν : rfd_indicator σ = 1)
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ))
    (huω : ∀ x y, ω (u x) (u y) = ω x y) :
    rfd_det σ ρ u hu = 1 := by
  obtain ⟨-, hzero, hsym, -, -⟩ := rfd_indicator_cases σ hσ
  have hreal : ∀ g, star (σ.character g) = σ.character g := by
    by_contra h
    have := hzero.2 h
    rw [hν] at this
    exact one_ne_zero this
  have hd : Module.finrank ℂ (rfd_invForms σ) = 1 := (rfd_finrank_invForms σ hσ).2.2 hreal
  obtain ⟨B, hB, hB0, hBs⟩ := hsym.1 hν
  have hspan : ∀ π ∈ rfd_invPairs σ σ, ∃ c : ℂ, π = c • B := by
    intro π hπ
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨B, hB⟩ : rfd_invForms σ)
      (fun h => hB0 (congrArg Subtype.val h))).1 hd ⟨π, hπ⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  have : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  obtain ⟨x₀, hx₀⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero hB0
    (LinearMap.BilinForm.isSymm_iff.1 hBs)
  have hl := rfd_multPair_left ρ ω hω hωG σ σ hσ B hB hspan x₀ x₀ hx₀
  exact rfd_det_eq_one_of_alt (rfd_multPair ρ ω σ σ x₀ x₀) (fun φ => hωalt.self_eq_zero _) hl _
    (rfd_multPair_act ρ ω σ σ x₀ x₀ u hu huω)

end HodgeLean.Foundations
