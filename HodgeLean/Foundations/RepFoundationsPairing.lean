import HodgeLean.Foundations.RepFoundationsIndicator

/-! # Representation foundations: invariant pairings and multiplicity spaces

The invariant pairings `τ × τ' → ℂ` of two representations have dimension
`|G|⁻¹ Σ_g χ_τ(g) χ_τ'(g)`. A nondegenerate `G`-invariant form `ω` on `V` and a spanning invariant
pairing `β` of `τ × τ'` give a pairing `γ` of the multiplicity spaces with
`ω(φ x, ψ y) = γ(φ, ψ) β(x, y)`, nondegenerate on the side of a simple `τ`; a centralizer element
preserving `ω` preserves `γ`.
-/

noncomputable section

namespace HodgeLean.Foundations

open CategoryTheory
open scoped Matrix

section Trace

variable {X Y : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
  [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]

/-- The action `β ↦ β(A·, B·)` of a pair of endomorphisms on pairings. -/
def rfd_pairAct (A : Module.End ℂ X) (B : Module.End ℂ Y) :
    Module.End ℂ (X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) where
  toFun β := β.compl₁₂ A B
  map_add' β β' := by ext; simp
  map_smul' c β := by ext; simp

omit [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y] in
@[simp] theorem rfd_pairAct_apply (A : Module.End ℂ X) (B : Module.End ℂ Y)
    (β : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (x : X) (y : Y) : rfd_pairAct A B β x y = β (A x) (B y) := rfl

theorem rfd_trace_matrix' {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (L : Module.End ℂ (Matrix n m ℂ)) :
    LinearMap.trace ℂ _ L = ∑ i, ∑ j, L (Matrix.single i j 1) i j := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ n m), Matrix.trace,
    Fintype.sum_prod_type]
  simp [LinearMap.toMatrix_apply, Matrix.stdBasis, Matrix.single_eq_of_single_single]

/-- The trace of `β ↦ β(A·, B·)` is `tr A · tr B`. -/
theorem rfd_trace_pairAct (A : Module.End ℂ X) (B : Module.End ℂ Y) :
    LinearMap.trace ℂ _ (rfd_pairAct A B) = LinearMap.trace ℂ X A * LinearMap.trace ℂ Y B := by
  classical
  let b₁ := Module.finBasis ℂ X
  let b₂ := Module.finBasis ℂ Y
  let e : (X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) ≃ₗ[ℂ] Matrix _ _ ℂ := LinearMap.toMatrix₂ b₁ b₂
  rw [← LinearMap.trace_conj' _ e, rfd_trace_matrix', LinearMap.trace_eq_matrix_trace ℂ b₁,
    LinearMap.trace_eq_matrix_trace ℂ b₂, Matrix.trace, Matrix.trace, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : e.conj (rfd_pairAct A B) (Matrix.single i j 1) =
      (LinearMap.toMatrix b₁ b₁ A)ᵀ * Matrix.single i j (1 : ℂ) * LinearMap.toMatrix b₂ b₂ B := by
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    change e ((e.symm (Matrix.single i j 1)).compl₁₂ A B) = _
    rw [LinearMap.toMatrix₂_compl₁₂ b₁ b₂ b₁ b₂, LinearEquiv.apply_symm_apply]
  rw [h]
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]

end Trace

variable {G : Type} [Group G] [Fintype G]

/-- The invariant pairings `τ × τ' → ℂ`. -/
def rfd_invPairs (τ τ' : FDRep ℂ G) : Submodule ℂ (τ →ₗ[ℂ] τ' →ₗ[ℂ] ℂ) where
  carrier := {β | ∀ g x y, β (τ.ρ g x) (τ'.ρ g y) = β x y}
  add_mem' {β β'} hβ hβ' g x y := by
    simp only [LinearMap.add_apply, hβ g x y, hβ' g x y]
  zero_mem' g x y := rfl
  smul_mem' c β hβ g x y := by
    simp only [LinearMap.smul_apply, hβ g x y]

/-- The averaging projector onto invariant pairings. -/
def rfd_pairAvg (τ τ' : FDRep ℂ G) : Module.End ℂ (τ →ₗ[ℂ] τ' →ₗ[ℂ] ℂ) :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, rfd_pairAct (τ.ρ g) (τ'.ρ g)

theorem rfd_pairAvg_apply (τ τ' : FDRep ℂ G) (β : τ →ₗ[ℂ] τ' →ₗ[ℂ] ℂ) (x : τ) (y : τ') :
    rfd_pairAvg τ τ' β x y = (Fintype.card G : ℂ)⁻¹ * ∑ g, β (τ.ρ g x) (τ'.ρ g y) := by
  simp [rfd_pairAvg, LinearMap.sum_apply]

theorem rfd_isProj_pairAvg (τ τ' : FDRep ℂ G) :
    LinearMap.IsProj (rfd_invPairs τ τ') (rfd_pairAvg τ τ') where
  map_mem β h x y := by
    rw [rfd_pairAvg_apply, rfd_pairAvg_apply]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => by
      simp [map_mul, Module.End.mul_apply]
  map_id β hβ := by
    ext x y
    rw [rfd_pairAvg_apply]
    simp only [hβ _ x y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (by simp), one_mul]

/-- `dim (invariant pairings τ × τ') = |G|⁻¹ Σ_g χ_τ(g) χ_τ'(g)`. -/
theorem rfd_finrank_invPairs (τ τ' : FDRep ℂ G) :
    (Module.finrank ℂ (rfd_invPairs τ τ') : ℂ) =
      (Fintype.card G : ℂ)⁻¹ * ∑ g, τ.character g * τ'.character g := by
  rw [← (rfd_isProj_pairAvg τ τ').trace, rfd_pairAvg, map_smul, map_sum, smul_eq_mul]
  simp only [rfd_trace_pairAct]
  rfl

/-- For simple `σ` and `σbar` with the conjugate character, the invariant pairings of `σ × σbar`
form a line. -/
theorem rfd_finrank_invPairs_conj (σ σbar : FDRep ℂ G) (hσ : Simple σ)
    (hchar : ∀ g, σbar.character g = star (σ.character g)) :
    Module.finrank ℂ (rfd_invPairs σ σbar) = 1 := by
  have h := (FDRep.simple_iff_char_is_norm_one σ).1 hσ
  rw [Nat.card_eq_fintype_card] at h
  have h1 : (Module.finrank ℂ (rfd_invPairs σ σbar) : ℂ) = 1 := by
    rw [rfd_finrank_invPairs]
    simp only [hchar, rfd_star_character]
    rw [h, inv_mul_cancel₀ (by simp)]
  exact_mod_cast h1

/-- A representation whose character is the conjugate of a simple character is simple. -/
theorem rfd_simple_conj (σ σbar : FDRep ℂ G) (hσ : Simple σ)
    (hchar : ∀ g, σbar.character g = star (σ.character g)) : Simple σbar := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have h := (FDRep.simple_iff_char_is_norm_one σ).1 hσ
  have := congrArg star h
  simp only [star_sum, star_mul', star_natCast] at this
  rw [← this]
  exact Finset.sum_congr rfl fun g _ => by rw [hchar, hchar]

/-- Determinants of maps preserving a perfect pairing multiply to one. -/
theorem rfd_det_mul_of_pairing {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁]
    [FiniteDimensional ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂] [FiniteDimensional ℂ M₂]
    (γ : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (hl : ∀ a, (∀ b, γ a b = 0) → a = 0)
    (hr : ∀ b, (∀ a, γ a b = 0) → b = 0) (A : Module.End ℂ M₁) (B : Module.End ℂ M₂)
    (h : ∀ a b, γ (A a) (B b) = γ a b) :
    LinearMap.det A * LinearMap.det B = 1 := by
  have hinj : Function.Injective γ.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    exact hr b fun a => LinearMap.congr_fun hb a
  have hinj' : Function.Injective γ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact hl a fun b => LinearMap.congr_fun ha b
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := LinearMap.finrank_le_finrank_of_injective hinj'
  rw [Subspace.dual_finrank_eq] at h1 h2
  let e : M₂ ≃ₗ[ℂ] Module.Dual ℂ M₁ := LinearMap.linearEquivOfInjective γ.flip hinj (by
    rw [Subspace.dual_finrank_eq]; omega)
  have he : ∀ b a, e b a = γ a b := fun _ _ => rfl
  have key : ((e.symm : _ →ₗ[ℂ] M₂) ∘ₗ A.dualMap ∘ₗ (e : M₂ →ₗ[ℂ] _)) ∘ₗ B = LinearMap.id := by
    refine LinearMap.ext fun b => e.injective ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LinearMap.id_apply]
    refine LinearMap.ext fun a => ?_
    rw [LinearMap.dualMap_apply, he, he, h]
  have := congrArg LinearMap.det key
  rw [LinearMap.det_comp, LinearMap.det_id] at this
  have hc := LinearMap.det_conj A.dualMap e.symm
  rw [LinearEquiv.symm_symm] at hc
  rwa [hc, LinearMap.det_dualMap] at this

section Mult

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- For a nonzero `φ ∈ Hom_G(τ, V)` with `τ` simple there is an equivariant `π : V → τ` with
`π ∘ φ = 1`: average `g⁻¹ ∘ π₀ ∘ g` for a rank-one `π₀` with `tr (π₀ ∘ φ) ≠ 0`, then use
Schur. -/
theorem rfd_exists_retraction (ρ : Representation ℂ G V) (τ : FDRep ℂ G) (hτ : Simple τ)
    (φ : rfd_mult τ ρ) (hφ : φ ≠ 0) :
    ∃ π : V →ₗ[ℂ] τ, (∀ g, π ∘ₗ ρ g = τ.ρ g ∘ₗ π) ∧ π ∘ₗ φ.1 = LinearMap.id := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, φ.1 x₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (Subtype.ext (LinearMap.ext h))
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f (φ.1 x₀) ≠ 0 := by
    by_contra h
    push Not at h
    exact hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
  let π₀ : V →ₗ[ℂ] τ := f.smulRight x₀
  let π : V →ₗ[ℂ] τ := ∑ g, τ.ρ g⁻¹ ∘ₗ π₀ ∘ₗ ρ g
  have hπapp : ∀ v, π v = ∑ g, τ.ρ g⁻¹ (π₀ (ρ g v)) := fun v => by
    simp [π, LinearMap.sum_apply]
  have hπ : ∀ h, π ∘ₗ ρ h = τ.ρ h ∘ₗ π := fun h => LinearMap.ext fun v => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hπapp, hπapp, map_sum]
    refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => ?_
    simp only [Equiv.coe_mulRight, mul_inv_rev, map_mul, Module.End.mul_apply]
    rw [← Module.End.mul_apply (τ.ρ h), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hτ' := hτ
  let F : Representation.IntertwiningMap τ.ρ τ.ρ :=
    ⟨π ∘ₗ φ.1, fun g => by
      rw [LinearMap.comp_assoc, φ.2 g, ← LinearMap.comp_assoc, hπ g, LinearMap.comp_assoc]⟩
  obtain ⟨c, hc⟩ := rfd_intertwining_eq_smul τ F
  have hF : π ∘ₗ φ.1 = c • LinearMap.id :=
    congrArg Representation.IntertwiningMap.toLinearMap hc
  have htr : LinearMap.trace ℂ τ (π ∘ₗ φ.1) = Fintype.card G * f (φ.1 x₀) := by
    have : π ∘ₗ φ.1 = ∑ g, τ.ρ g⁻¹ ∘ₗ ((π₀ ∘ₗ φ.1) ∘ₗ τ.ρ g) := LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, hπapp, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← LinearMap.comp_apply (ρ g), ← φ.2 g, LinearMap.comp_apply]
    rw [this, map_sum]
    have h1 : ∀ g, LinearMap.trace ℂ τ (τ.ρ g⁻¹ ∘ₗ ((π₀ ∘ₗ φ.1) ∘ₗ τ.ρ g)) = f (φ.1 x₀) := by
      intro g
      rw [LinearMap.trace_comp_comm' (R := ℂ) ((π₀ ∘ₗ φ.1) ∘ₗ τ.ρ g) (τ.ρ g⁻¹), LinearMap.comp_assoc, ← Module.End.mul_eq_comp
        (τ.ρ g), ← map_mul, mul_inv_cancel, map_one, Module.End.one_eq_id, LinearMap.comp_id]
      have : π₀ ∘ₗ φ.1 = (f ∘ₗ φ.1).smulRight x₀ := LinearMap.ext fun x => rfl
      rw [this, LinearMap.trace_smulRight]
      rfl
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [hF, zero_smul, map_zero] at htr
    exact mul_ne_zero (by simp) hf htr.symm
  refine ⟨c⁻¹ • π, fun g => ?_, ?_⟩
  · rw [LinearMap.smul_comp, hπ g, LinearMap.comp_smul]
  · rw [LinearMap.smul_comp, hF, smul_smul, inv_mul_cancel₀ hc0, one_smul]

/-- For a nonzero `φ ∈ Hom_G(τ, V)` with `τ` simple and a nonzero invariant pairing `β` of
`τ × τ'`, some `ψ ∈ Hom_G(τ', V)` has `ω(φ x, ψ y) ≠ 0`: take `ψ` with
`ω(v, ψ y) = β(π v, y)`. -/
theorem rfd_exists_mult_pair (ρ : Representation ℂ G V) (ω : LinearMap.BilinForm ℂ V)
    (hω : ω.Nondegenerate) (hωG : ∀ g x y, ω (ρ g x) (ρ g y) = ω x y)
    (τ τ' : FDRep ℂ G) (hτ : Simple τ) (β : τ →ₗ[ℂ] τ' →ₗ[ℂ] ℂ) (hβ : β ∈ rfd_invPairs τ τ')
    (hβ0 : β ≠ 0) (φ : rfd_mult τ ρ) (hφ : φ ≠ 0) :
    ∃ ψ : rfd_mult τ' ρ, ∃ x y, ω (φ.1 x) (ψ.1 y) ≠ 0 := by
  obtain ⟨π, hπG, hπφ⟩ := rfd_exists_retraction ρ τ hτ φ hφ
  obtain ⟨x, y, hxy⟩ : ∃ x y, β x y ≠ 0 := by
    by_contra h
    push Not at h
    exact hβ0 (LinearMap.ext₂ h)
  let lam : τ' →ₗ[ℂ] Module.Dual ℂ V := (β.compl₁₂ π LinearMap.id).flip
  let ψ : τ' →ₗ[ℂ] V := (ω.flip.toDual hω.flip).symm.toLinearMap ∘ₗ lam
  have hψ : ∀ v y, ω v (ψ y) = β (π v) y := fun v y =>
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := hω.flip) (lam y) v
  have hπg : ∀ g v, π (ρ g v) = τ.ρ g (π v) := fun g v => LinearMap.congr_fun (hπG g) v
  have hψG : ∀ g, ψ ∘ₗ τ'.ρ g = ρ g ∘ₗ ψ := fun g => LinearMap.ext fun y => by
    refine sub_eq_zero.1 (hω.2 _ fun v => ?_)
    rw [map_sub]
    change ω v (ψ (τ'.ρ g y)) - ω v (ρ g (ψ y)) = 0
    rw [hψ]
    have hρ : ρ g (ρ g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have hτρ : τ.ρ g (τ.ρ g⁻¹ (π v)) = π v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h1 : ω v (ρ g (ψ y)) = ω (ρ g⁻¹ v) (ψ y) := by
      conv_lhs => rw [← hρ]
      exact hωG _ _ _
    rw [h1, hψ, hπg, ← hβ g (τ.ρ g⁻¹ (π v)) y, hτρ, sub_self]
  refine ⟨⟨ψ, hψG⟩, x, y, ?_⟩
  change ω (φ.1 x) (ψ y) ≠ 0
  rw [hψ, ← LinearMap.comp_apply π, hπφ, LinearMap.id_apply]
  exact hxy

/-- The pairing `(φ, ψ) ↦ ω(φ x₀, ψ y₀)` of multiplicity spaces. -/
def rfd_multPair (ρ : Representation ℂ G V) (ω : LinearMap.BilinForm ℂ V) (τ τ' : FDRep ℂ G)
    (x₀ : τ) (y₀ : τ') : rfd_mult τ ρ →ₗ[ℂ] rfd_mult τ' ρ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun φ ψ => ω (φ.1 x₀) (ψ.1 y₀))
    (fun φ φ' ψ => by simp) (fun c φ ψ => by simp) (fun φ ψ ψ' => by simp)
    (fun c φ ψ => by simp)

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem rfd_multPair_apply (ρ : Representation ℂ G V) (ω : LinearMap.BilinForm ℂ V)
    (τ τ' : FDRep ℂ G) (x₀ : τ) (y₀ : τ') (φ : rfd_mult τ ρ) (ψ : rfd_mult τ' ρ) :
    rfd_multPair ρ ω τ τ' x₀ y₀ φ ψ = ω (φ.1 x₀) (ψ.1 y₀) := rfl

omit [Fintype G] [FiniteDimensional ℂ V] in
/-- If `β` spans the invariant pairings, `ω(φ x, ψ y) β(x₀, y₀) = γ(φ, ψ) β(x, y)`. -/
theorem rfd_multPair_spec (ρ : Representation ℂ G V) (ω : LinearMap.BilinForm ℂ V)
    (hωG : ∀ g x y, ω (ρ g x) (ρ g y) = ω x y) (τ τ' : FDRep ℂ G)
    (β : τ →ₗ[ℂ] τ' →ₗ[ℂ] ℂ) (hspan : ∀ π ∈ rfd_invPairs τ τ', ∃ c : ℂ, π = c • β)
    (x₀ : τ) (y₀ : τ') (φ : rfd_mult τ ρ) (ψ : rfd_mult τ' ρ) (x : τ) (y : τ') :
    ω (φ.1 x) (ψ.1 y) * β x₀ y₀ = rfd_multPair ρ ω τ τ' x₀ y₀ φ ψ * β x y := by
  have hmem : ω.compl₁₂ φ.1 ψ.1 ∈ rfd_invPairs τ τ' := fun g x y => by
    simp only [LinearMap.compl₁₂_apply]
    rw [← LinearMap.comp_apply φ.1, φ.2 g, ← LinearMap.comp_apply ψ.1, ψ.2 g,
      LinearMap.comp_apply, LinearMap.comp_apply, hωG]
  obtain ⟨c, hc⟩ := hspan _ hmem
  have h1 : ∀ x y, ω (φ.1 x) (ψ.1 y) = c * β x y := fun x y => by
    have := LinearMap.congr_fun₂ hc x y
    simpa using this
  rw [rfd_multPair_apply, h1, h1]
  ring

omit [Fintype G] [FiniteDimensional ℂ V] in
/-- A centralizer element preserving `ω` preserves the pairing of multiplicity spaces. -/
theorem rfd_multPair_act (ρ : Representation ℂ G V) (ω : LinearMap.BilinForm ℂ V)
    (τ τ' : FDRep ℂ G) (x₀ : τ) (y₀ : τ') (u : Module.End ℂ V)
    (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) (huω : ∀ x y, ω (u x) (u y) = ω x y)
    (φ : rfd_mult τ ρ) (ψ : rfd_mult τ' ρ) :
    rfd_multPair ρ ω τ τ' x₀ y₀ (rfd_multAct τ ρ u hu φ) (rfd_multAct τ' ρ u hu ψ) =
      rfd_multPair ρ ω τ τ' x₀ y₀ φ ψ :=
  huω _ _

/-- The pairing of multiplicity spaces is nondegenerate on the side of a simple `τ`. -/
theorem rfd_multPair_left (ρ : Representation ℂ G V) (ω : LinearMap.BilinForm ℂ V)
    (hω : ω.Nondegenerate) (hωG : ∀ g x y, ω (ρ g x) (ρ g y) = ω x y)
    (τ τ' : FDRep ℂ G) (hτ : Simple τ) (β : τ →ₗ[ℂ] τ' →ₗ[ℂ] ℂ) (hβ : β ∈ rfd_invPairs τ τ')
    (hspan : ∀ π ∈ rfd_invPairs τ τ', ∃ c : ℂ, π = c • β)
    (x₀ : τ) (y₀ : τ') (h₀ : β x₀ y₀ ≠ 0) (φ : rfd_mult τ ρ)
    (hφ : ∀ ψ, rfd_multPair ρ ω τ τ' x₀ y₀ φ ψ = 0) : φ = 0 := by
  by_contra hφ0
  have hβ0 : β ≠ 0 := fun h => h₀ (by rw [h]; rfl)
  obtain ⟨ψ, x, y, hxy⟩ := rfd_exists_mult_pair ρ ω hω hωG τ τ' hτ β hβ hβ0 φ hφ0
  have := rfd_multPair_spec ρ ω hωG τ τ' β hspan x₀ y₀ φ ψ x y
  rw [hφ ψ, zero_mul] at this
  exact mul_ne_zero hxy h₀ this

omit [Fintype G] in
/-- A line of invariant pairings has a spanning element, nonzero at some `(x₀, y₀)`. -/
theorem rfd_exists_spanning (τ τ' : FDRep ℂ G) (h : Module.finrank ℂ (rfd_invPairs τ τ') = 1) :
    ∃ β ∈ rfd_invPairs τ τ', ∃ x₀ y₀, β x₀ y₀ ≠ 0 ∧
      ∀ π ∈ rfd_invPairs τ τ', ∃ c : ℂ, π = c • β := by
  obtain ⟨β, hβ⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (h ▸ Nat.one_pos)
  have hspan := (finrank_eq_one_iff_of_nonzero' β hβ).1 h
  obtain ⟨x₀, y₀, h₀⟩ : ∃ x₀ y₀, β.1 x₀ y₀ ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hβ (Subtype.ext (LinearMap.ext₂ h'))
  refine ⟨β.1, β.2, x₀, y₀, h₀, fun π hπ => ?_⟩
  obtain ⟨c, hc⟩ := hspan ⟨π, hπ⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem rfd_det_mul_dual' (ρ : Representation ℂ G V) (ω : LinearMap.BilinForm ℂ V)
    (hω : ω.Nondegenerate) (hωG : ∀ g x y, ω (ρ g x) (ρ g y) = ω x y)
    (σ σbar : FDRep ℂ G) (hσ : Simple σ)
    (hchar : ∀ g, σbar.character g = star (σ.character g))
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ))
    (huω : ∀ x y, ω (u x) (u y) = ω x y) :
    rfd_det σbar ρ u hu * rfd_det σ ρ u hu = 1 := by
  have hσb := rfd_simple_conj σ σbar hσ hchar
  have hchar' : ∀ g, σ.character g = star (σbar.character g) := fun g => by
    rw [hchar, star_star]
  obtain ⟨β, hβ, x₀, y₀, h₀, hspan⟩ :=
    rfd_exists_spanning σ σbar (rfd_finrank_invPairs_conj σ σbar hσ hchar)
  obtain ⟨β', hβ', x₀', y₀', h₀', hspan'⟩ :=
    rfd_exists_spanning σbar σ (rfd_finrank_invPairs_conj σbar σ hσb hchar')
  have hωG' : ∀ g x y, ω.flip (ρ g x) (ρ g y) = ω.flip x y := fun g x y => hωG g y x
  have hl := rfd_multPair_left ρ ω hω hωG σ σbar hσ β hβ hspan x₀ y₀ h₀
  have hr : ∀ ψ, (∀ φ, rfd_multPair ρ ω σ σbar x₀ y₀ φ ψ = 0) → ψ = 0 := by
    intro ψ hψ
    refine rfd_multPair_left ρ ω.flip hω.flip hωG' σbar σ hσb β' hβ' hspan' x₀' y₀' h₀' ψ
      fun φ => ?_
    have h1 : ∀ x y, ω (φ.1 x) (ψ.1 y) = 0 := fun x y => by
      have := rfd_multPair_spec ρ ω hωG σ σbar β hspan x₀ y₀ φ ψ x y
      rw [hψ φ, zero_mul] at this
      exact (mul_eq_zero.1 this).resolve_right h₀
    exact h1 y₀' x₀'
  rw [mul_comm]
  exact rfd_det_mul_of_pairing _ hl hr _ _
    (rfd_multPair_act ρ ω σ σbar x₀ y₀ u hu huω)

end Mult

end HodgeLean.Foundations
