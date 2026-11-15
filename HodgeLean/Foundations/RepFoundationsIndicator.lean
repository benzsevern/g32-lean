import HodgeLean.Foundations.RepFoundationsEigen

/-! # Representation foundations: the Frobenius–Schur indicator

For a representation `σ`, the averaging operator `P = |G|⁻¹ Σ_g (B ↦ B(g·, g·))` on bilinear
forms projects onto the invariant forms, and so do its products with the projectors onto
symmetric and skew forms. Their traces give `dim (invariant forms) = |G|⁻¹ Σ_g χ(g)²` and
`dim (symmetric invariant) - dim (skew invariant) = |G|⁻¹ Σ_g χ(g²) = ν(σ)`. For simple `σ`,
`|G|⁻¹ Σ_g |χ(g) - conj χ(g)|² = 2 - 2 dim (invariant forms)` bounds the dimension by one, with
equality exactly when `χ` is real.
-/

noncomputable section

namespace HodgeLean.Foundations

open CategoryTheory
open scoped Matrix

section Trace

variable {X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]

/-- The action `B ↦ B(A·, A·)` of an endomorphism on bilinear forms. -/
def rfd_formAct (A : Module.End ℂ X) : Module.End ℂ (LinearMap.BilinForm ℂ X) where
  toFun B := B.compl₁₂ A A
  map_add' B C := by ext; simp
  map_smul' c B := by ext; simp

/-- The transpose `B ↦ B(·₂, ·₁)` of bilinear forms. -/
def rfd_formSwap : Module.End ℂ (LinearMap.BilinForm ℂ X) where
  toFun B := B.flip
  map_add' B C := by ext; simp
  map_smul' c B := by ext; simp

omit [FiniteDimensional ℂ X] in
@[simp] theorem rfd_formAct_apply (A : Module.End ℂ X) (B : LinearMap.BilinForm ℂ X) (x y : X) :
    rfd_formAct A B x y = B (A x) (A y) := rfl

omit [FiniteDimensional ℂ X] in
@[simp] theorem rfd_formSwap_apply (B : LinearMap.BilinForm ℂ X) (x y : X) :
    rfd_formSwap B x y = B y x := rfl

theorem rfd_trace_matrix {n : Type} [Fintype n] [DecidableEq n]
    (L : Module.End ℂ (Matrix n n ℂ)) :
    LinearMap.trace ℂ _ L = ∑ i, ∑ j, L (Matrix.single i j 1) i j := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ n n), Matrix.trace,
    Fintype.sum_prod_type]
  simp [LinearMap.toMatrix_apply, Matrix.stdBasis, Matrix.single_eq_of_single_single]

/-- The trace of `B ↦ B(A·, A·)` is `(tr A)²`. -/
theorem rfd_trace_formAct (A : Module.End ℂ X) :
    LinearMap.trace ℂ _ (rfd_formAct A) = LinearMap.trace ℂ X A ^ 2 := by
  classical
  let b := Module.finBasis ℂ X
  let e : LinearMap.BilinForm ℂ X ≃ₗ[ℂ] Matrix _ _ ℂ := LinearMap.toMatrix₂ b b
  rw [← LinearMap.trace_conj' _ e, rfd_trace_matrix, LinearMap.trace_eq_matrix_trace ℂ b,
    Matrix.trace, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : e.conj (rfd_formAct A) (Matrix.single i j 1) =
      (LinearMap.toMatrix b b A)ᵀ * Matrix.single i j 1 * LinearMap.toMatrix b b A := by
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    change e ((e.symm (Matrix.single i j 1)).compl₁₂ A A) = _
    rw [LinearMap.toMatrix₂_compl₁₂ b b b b, LinearEquiv.apply_symm_apply]
  rw [h]
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]

/-- The trace of `B ↦ B(A·₂, A·₁)` is `tr (A²)`. -/
theorem rfd_trace_formAct_swap (A : Module.End ℂ X) :
    LinearMap.trace ℂ _ (rfd_formAct A ∘ₗ rfd_formSwap) = LinearMap.trace ℂ X (A * A) := by
  classical
  let b := Module.finBasis ℂ X
  let e : LinearMap.BilinForm ℂ X ≃ₗ[ℂ] Matrix _ _ ℂ := LinearMap.toMatrix₂ b b
  rw [← LinearMap.trace_conj' _ e, rfd_trace_matrix, LinearMap.trace_eq_matrix_trace ℂ b,
    Matrix.trace, LinearMap.toMatrix_mul]
  simp only [Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hflip : ∀ B : LinearMap.BilinForm ℂ X, e B.flip = (e B)ᵀ := fun B => by
    ext k l
    simp [e, LinearMap.toMatrix₂_apply]
  have h : e.conj (rfd_formAct A ∘ₗ rfd_formSwap) (Matrix.single i j 1) =
      (LinearMap.toMatrix b b A)ᵀ * (Matrix.single i j 1)ᵀ * LinearMap.toMatrix b b A := by
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    change e ((e.symm (Matrix.single i j 1)).flip.compl₁₂ A A) = _
    rw [LinearMap.toMatrix₂_compl₁₂ b b b b, hflip, LinearEquiv.apply_symm_apply]
  rw [h]
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul, mul_comm]

end Trace

section Forms

variable {X : Type} [AddCommGroup X] [Module ℂ X]

/-- The symmetric bilinear forms. -/
def rfd_symForms : Submodule ℂ (LinearMap.BilinForm ℂ X) where
  carrier := {B | ∀ x y, B x y = B y x}
  add_mem' {B C} hB hC x y := by simp only [LinearMap.add_apply, hB x y, hC x y]
  zero_mem' x y := rfl
  smul_mem' c B hB x y := by simp only [LinearMap.smul_apply, hB x y]

/-- The skew bilinear forms. -/
def rfd_skewForms : Submodule ℂ (LinearMap.BilinForm ℂ X) where
  carrier := {B | ∀ x y, B x y = -B y x}
  add_mem' {B C} hB hC x y := by simp only [LinearMap.add_apply, hB x y, hC x y, neg_add]
  zero_mem' x y := by simp
  smul_mem' c B hB x y := by simp only [LinearMap.smul_apply, hB x y, smul_neg]

theorem rfd_mem_skewForms_iff (B : LinearMap.BilinForm ℂ X) :
    B ∈ rfd_skewForms ↔ B.IsAlt := by
  constructor
  · intro h x
    have hx : B x x = -B x x := h x x
    have : (2 : ℂ) * B x x = 0 := by rw [two_mul]; nth_rw 1 [hx]; exact neg_add_cancel _
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  · intro h x y
    rw [← LinearMap.BilinForm.IsAlt.neg_eq h x y, neg_neg]

/-- The projector `B ↦ (B + Bᵗ)/2` onto symmetric forms. -/
def rfd_symProj : Module.End ℂ (LinearMap.BilinForm ℂ X) :=
  (2 : ℂ)⁻¹ • (1 + rfd_formSwap)

/-- The projector `B ↦ (B - Bᵗ)/2` onto skew forms. -/
def rfd_skewProj : Module.End ℂ (LinearMap.BilinForm ℂ X) :=
  (2 : ℂ)⁻¹ • (1 - rfd_formSwap)

@[simp] theorem rfd_symProj_apply (B : LinearMap.BilinForm ℂ X) (x y : X) :
    rfd_symProj B x y = (2 : ℂ)⁻¹ * (B x y + B y x) := by
  simp [rfd_symProj, mul_add]

@[simp] theorem rfd_skewProj_apply (B : LinearMap.BilinForm ℂ X) (x y : X) :
    rfd_skewProj B x y = (2 : ℂ)⁻¹ * (B x y - B y x) := by
  simp [rfd_skewProj, mul_sub]

end Forms

section Indicator

variable {G : Type} [Group G] [Fintype G]

/-- The averaging projector `B ↦ |G|⁻¹ Σ_g B(g·, g·)` onto invariant forms. -/
def rfd_formAvg (σ : FDRep ℂ G) : Module.End ℂ (LinearMap.BilinForm ℂ σ) :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, rfd_formAct (σ.ρ g)

theorem rfd_formAvg_apply (σ : FDRep ℂ G) (B : LinearMap.BilinForm ℂ σ) (x y : σ) :
    rfd_formAvg σ B x y = (Fintype.card G : ℂ)⁻¹ * ∑ g, B (σ.ρ g x) (σ.ρ g y) := by
  simp [rfd_formAvg, LinearMap.sum_apply]

theorem rfd_formAvg_mem (σ : FDRep ℂ G) (B : LinearMap.BilinForm ℂ σ) :
    rfd_formAvg σ B ∈ rfd_invForms σ := by
  intro h x y
  rw [rfd_formAvg_apply, rfd_formAvg_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => by
    simp [map_mul, Module.End.mul_apply]

theorem rfd_formAvg_of_mem (σ : FDRep ℂ G) {B : LinearMap.BilinForm ℂ σ}
    (hB : B ∈ rfd_invForms σ) : rfd_formAvg σ B = B := by
  ext x y
  rw [rfd_formAvg_apply]
  simp only [hB _ x y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by simp), one_mul]

theorem rfd_formAvg_symm (σ : FDRep ℂ G) {s : ℂ} {B : LinearMap.BilinForm ℂ σ}
    (hB : ∀ x y, B x y = s * B y x) (x y : σ) :
    rfd_formAvg σ B x y = s * rfd_formAvg σ B y x := by
  rw [rfd_formAvg_apply, rfd_formAvg_apply, mul_left_comm s, Finset.mul_sum _ _ s]
  congr 1
  exact Finset.sum_congr rfl fun g _ => hB _ _

theorem rfd_isProj_sym (σ : FDRep ℂ G) :
    LinearMap.IsProj (rfd_invForms σ ⊓ rfd_symForms) (rfd_formAvg σ ∘ₗ rfd_symProj) where
  map_mem B := ⟨rfd_formAvg_mem σ _, fun x y => by
    have := rfd_formAvg_symm σ (B := rfd_symProj B) (s := 1) (fun x y => by
      simp only [rfd_symProj_apply, one_mul]; ring) x y
    rw [one_mul] at this
    exact this⟩
  map_id B hB := by
    have h1 : rfd_symProj B = B := by
      ext x y
      rw [rfd_symProj_apply, ← hB.2 x y]
      ring
    rw [LinearMap.comp_apply, h1, rfd_formAvg_of_mem σ hB.1]

theorem rfd_isProj_skew (σ : FDRep ℂ G) :
    LinearMap.IsProj (rfd_invForms σ ⊓ rfd_skewForms) (rfd_formAvg σ ∘ₗ rfd_skewProj) where
  map_mem B := ⟨rfd_formAvg_mem σ _, fun x y => by
    have := rfd_formAvg_symm σ (B := rfd_skewProj B) (s := -1) (fun x y => by
      simp only [rfd_skewProj_apply]; ring) x y
    rw [neg_one_mul] at this
    exact this⟩
  map_id B hB := by
    have h1 : rfd_skewProj B = B := by
      ext x y
      rw [rfd_skewProj_apply, hB.2 x y]
      ring
    rw [LinearMap.comp_apply, h1, rfd_formAvg_of_mem σ hB.1]

theorem rfd_isProj_avg (σ : FDRep ℂ G) :
    LinearMap.IsProj (rfd_invForms σ) (rfd_formAvg σ) where
  map_mem B := rfd_formAvg_mem σ B
  map_id _ hB := rfd_formAvg_of_mem σ hB

theorem rfd_trace_formAvg (σ : FDRep ℂ G) :
    LinearMap.trace ℂ _ (rfd_formAvg σ) =
      (Fintype.card G : ℂ)⁻¹ * ∑ g, σ.character g ^ 2 := by
  rw [rfd_formAvg, map_smul, map_sum, smul_eq_mul]
  simp only [rfd_trace_formAct]
  rfl

theorem rfd_trace_formAvg_swap (σ : FDRep ℂ G) :
    LinearMap.trace ℂ _ (rfd_formAvg σ ∘ₗ rfd_formSwap) = rfd_indicator σ := by
  have h : rfd_formAvg σ ∘ₗ rfd_formSwap =
      (Fintype.card G : ℂ)⁻¹ • ∑ g, rfd_formAct (σ.ρ g) ∘ₗ rfd_formSwap := by
    ext B x y
    simp [rfd_formAvg, LinearMap.sum_apply]
  rw [h, map_smul, map_sum, smul_eq_mul]
  simp only [rfd_trace_formAct_swap, ← map_mul]
  rfl

/-- The numbers `s = dim (symmetric invariant)`, `a = dim (skew invariant)` and
`d = dim (invariant)` satisfy `s + a = d`, `s - a = ν(σ)` and `d = |G|⁻¹ Σ_g χ(g)²`. -/
theorem rfd_finrank_forms (σ : FDRep ℂ G) :
    Module.finrank ℂ ↥(rfd_invForms σ ⊓ rfd_symForms) +
        Module.finrank ℂ ↥(rfd_invForms σ ⊓ rfd_skewForms) =
      Module.finrank ℂ (rfd_invForms σ) ∧
    (Module.finrank ℂ ↥(rfd_invForms σ ⊓ rfd_symForms) : ℂ) -
        Module.finrank ℂ ↥(rfd_invForms σ ⊓ rfd_skewForms) = rfd_indicator σ ∧
    (Module.finrank ℂ (rfd_invForms σ) : ℂ) =
      (Fintype.card G : ℂ)⁻¹ * ∑ g, σ.character g ^ 2 := by
  have hs := (rfd_isProj_sym σ).trace
  have ha := (rfd_isProj_skew σ).trace
  have hd := (rfd_isProj_avg σ).trace
  have hadd : rfd_formAvg σ ∘ₗ rfd_symProj + rfd_formAvg σ ∘ₗ rfd_skewProj = rfd_formAvg σ := by
    rw [← LinearMap.comp_add]
    convert LinearMap.comp_id (rfd_formAvg σ)
    ext B x y
    simp; ring
  have hsub : rfd_formAvg σ ∘ₗ rfd_symProj - rfd_formAvg σ ∘ₗ rfd_skewProj =
      rfd_formAvg σ ∘ₗ rfd_formSwap := by
    rw [← LinearMap.comp_sub]
    congr 1
    ext B x y
    simp; ring
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (LinearMap.trace ℂ _) hadd
    rw [map_add, hs, ha, hd] at this
    exact_mod_cast this
  · rw [← hs, ← ha, ← map_sub, hsub, rfd_trace_formAvg_swap]
  · rw [← hd, rfd_trace_formAvg]

/-- For simple `σ`, the invariant forms have dimension at most one, with equality exactly when
the character is real: `Σ_g |χ(g) - conj χ(g)|² = 2 |G| (1 - d)`. -/
theorem rfd_finrank_invForms (σ : FDRep ℂ G) (hσ : Simple σ) :
    Module.finrank ℂ (rfd_invForms σ) ≤ 1 ∧
      (Module.finrank ℂ (rfd_invForms σ) = 1 ↔ ∀ g, star (σ.character g) = σ.character g) := by
  set d := Module.finrank ℂ (rfd_invForms σ)
  have hN : (Fintype.card G : ℂ) ≠ 0 := by simp
  have hd := (rfd_finrank_forms σ).2.2
  have hT : ∑ g, σ.character g ^ 2 = (Fintype.card G : ℂ) * d := by
    rw [hd, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]
  have hS : ∑ g, star (σ.character g) * σ.character g = Fintype.card G := by
    have h := (FDRep.simple_iff_char_is_norm_one σ).1 hσ
    rw [Nat.card_eq_fintype_card] at h
    rw [← h]
    exact Finset.sum_congr rfl fun g _ => by rw [rfd_star_character, mul_comm]
  set R : ℝ := ∑ g, Complex.normSq (σ.character g - star (σ.character g)) with hRdef
  have hpt : ∀ g, (Complex.normSq (σ.character g - star (σ.character g)) : ℂ) =
      2 * (star (σ.character g) * σ.character g) - σ.character g ^ 2 -
        star (σ.character g ^ 2) := fun g => by
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, star_sub, star_star, star_pow]
    ring
  have hR : (R : ℂ) = ((2 * Fintype.card G * (1 - d) : ℝ) : ℂ) := by
    rw [hRdef, Complex.ofReal_sum]
    simp only [hpt]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hS, ← star_sum, hT]
    simp only [star_mul', star_natCast]
    push_cast
    ring
  have hR' := Complex.ofReal_injective hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun g _ => Complex.normSq_nonneg _
  have hNpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hle : d ≤ 1 := by
    by_contra h
    have h2 : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
    nlinarith
  refine ⟨hle, ?_⟩
  have h1 : d = 1 ↔ R = 0 := by
    rw [hR']
    constructor
    · intro h; rw [h]; simp
    · intro h
      have : (1 : ℝ) - d = 0 := by
        rcases mul_eq_zero.1 h with h | h
        · exfalso; nlinarith
        · exact h
      exact_mod_cast (sub_eq_zero.1 this).symm
  rw [h1, hRdef, Finset.sum_eq_zero_iff_of_nonneg fun g _ => Complex.normSq_nonneg _]
  simp only [Finset.mem_univ, true_implies, Complex.normSq_eq_zero, sub_eq_zero]
  exact forall_congr' fun g => eq_comm

theorem rfd_mem_symForms_iff {X : Type} [AddCommGroup X] [Module ℂ X]
    (B : LinearMap.BilinForm ℂ X) : B ∈ rfd_symForms ↔ B.IsSymm :=
  (LinearMap.BilinForm.isSymm_def).symm

theorem rfd_indicator_cases (σ : FDRep ℂ G) (hσ : Simple σ) :
    (rfd_indicator σ = 1 ∨ rfd_indicator σ = 0 ∨ rfd_indicator σ = -1) ∧
      (rfd_indicator σ = 0 ↔ ¬ ∀ g, star (σ.character g) = σ.character g) ∧
      (rfd_indicator σ = 1 ↔ ∃ B ∈ rfd_invForms σ, B ≠ 0 ∧ B.IsSymm) ∧
      (rfd_indicator σ = -1 ↔ ∃ B ∈ rfd_invForms σ, B ≠ 0 ∧ B.IsAlt) ∧
      (rfd_indicator σ = 0 ↔ rfd_invForms σ = ⊥) := by
  obtain ⟨hsa, hdiff, -⟩ := rfd_finrank_forms σ
  obtain ⟨hle, hreal⟩ := rfd_finrank_invForms σ hσ
  set s := Module.finrank ℂ ↥(rfd_invForms σ ⊓ rfd_symForms)
  set a := Module.finrank ℂ ↥(rfd_invForms σ ⊓ rfd_skewForms)
  set d := Module.finrank ℂ (rfd_invForms σ)
  have hz : ∀ k : ℤ, rfd_indicator σ = k ↔ (s : ℤ) - a = k := fun k => by
    rw [← hdiff, ← Int.cast_inj (α := ℂ)]
    push_cast
    rfl
  have h1 : rfd_indicator σ = 1 ↔ (s : ℤ) - a = 1 := by simpa using hz 1
  have h0 : rfd_indicator σ = 0 ↔ (s : ℤ) - a = 0 := by simpa using hz 0
  have hm : rfd_indicator σ = -1 ↔ (s : ℤ) - a = -1 := by simpa using hz (-1)
  have hs0 : s ≠ 0 ↔ ∃ B ∈ rfd_invForms σ, B ≠ 0 ∧ B.IsSymm := by
    rw [Ne, Submodule.finrank_eq_zero, ← Ne, Submodule.ne_bot_iff]
    constructor
    · rintro ⟨B, ⟨hi, hs⟩, hne⟩
      exact ⟨B, hi, hne, (rfd_mem_symForms_iff B).1 hs⟩
    · rintro ⟨B, hi, hne, hs⟩
      exact ⟨B, ⟨hi, (rfd_mem_symForms_iff B).2 hs⟩, hne⟩
  have ha0 : a ≠ 0 ↔ ∃ B ∈ rfd_invForms σ, B ≠ 0 ∧ B.IsAlt := by
    rw [Ne, Submodule.finrank_eq_zero, ← Ne, Submodule.ne_bot_iff]
    constructor
    · rintro ⟨B, ⟨hi, hs⟩, hne⟩
      exact ⟨B, hi, hne, (rfd_mem_skewForms_iff B).1 hs⟩
    · rintro ⟨B, hi, hne, hs⟩
      exact ⟨B, ⟨hi, (rfd_mem_skewForms_iff B).2 hs⟩, hne⟩
  have hd0 : d = 0 ↔ rfd_invForms σ = ⊥ := Submodule.finrank_eq_zero
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h1, h0, hm]; omega
  · rw [h0, ← hreal]; omega
  · rw [h1, ← hs0]; omega
  · rw [hm, ← ha0]; omega
  · rw [h0, ← hd0]; omega

end Indicator

end HodgeLean.Foundations
