import HodgeLean.Foundations.Program.G32PropFourSixPacked0008

noncomputable section

open HodgeLean.Papers CategoryTheory

namespace HodgeLean.Foundations.Program

theorem g32p_linRep_character {G : Type} [Group G] (χ : G →* ℂˣ) (g : G) :
    (papersLinRep χ).character g = (χ g : ℂ) := by
  change LinearMap.trace ℂ ℂ (Algebra.lmul ℂ ℂ (χ g : ℂ)) = _
  rw [← Algebra.trace_apply, Algebra.trace_self_apply]

theorem g32p_linRep_simple {G : Type} [Group G] [Finite G] (χ : G →* ℂˣ) :
    Simple (papersLinRep χ) := by
  classical
  letI := Fintype.ofFinite G
  apply (FDRep.simple_iff_char_is_norm_one (papersLinRep χ)).mpr
  simp [g32p_linRep_character, Nat.card_eq_fintype_card]

theorem g32p_linRep_conjugate {G : Type} [Group G] [Finite G] (χ : G →* ℂˣ) (g : G) :
    (papersLinRep χ⁻¹).character g = star ((papersLinRep χ).character g) := by
  rw [g32p_linRep_character, g32p_linRep_character]
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  exact Complex.inv_eq_conj
    (((Units.coeHom ℂ).comp χ).isOfFinOrder (isOfFinOrder_of_finite g)).norm_eq_one

def g32p_determinantRep : FDRep ℂ g32p_G := papersLinRep g32p_determinant

def g32p_determinantConjugateRep : FDRep ℂ g32p_G := papersLinRep g32p_determinant⁻¹

theorem g32p_determinantRep_simple : Simple g32p_determinantRep :=
  g32p_linRep_simple _

theorem g32p_determinantConjugateRep_simple : Simple g32p_determinantConjugateRep :=
  g32p_linRep_simple _

theorem g32p_determinantRep_conjugate (g : g32p_G) :
    g32p_determinantConjugateRep.character g = star (g32p_determinantRep.character g) :=
  g32p_linRep_conjugate _ _

theorem g32p_determinantRep_not_selfDual : ¬ g32p_SelfDual g32p_determinantRep := by
  intro h
  have hh := h (b4b_generators 0)
  change star ((papersLinRep g32p_determinant).character _) =
    (papersLinRep g32p_determinant).character _ at hh
  rw [g32p_linRep_character, g32p_determinant_val, g32p_generator_determinant] at hh
  change star g32h_omega = g32h_omega at hh
  have hi := congrArg Complex.im hh
  simp [Complex.conj_im] at hi
  exact omega_im_ne_zero g32h_omega g32h_omega_sq_add (by linarith)

theorem g32p_scalar_rank (c : ℂ) :
    Module.finrank ℂ (LinearMap.range (Algebra.lmul ℂ ℂ c - 1)) =
      if c = 1 then 0 else 1 := by
  classical
  have he : Algebra.lmul ℂ ℂ c - 1 = Algebra.lmul ℂ ℂ (c - 1) := by
    rw [map_sub, map_one]
  rw [he]
  split_ifs with h
  · rw [h, sub_self, map_zero, LinearMap.range_zero]
    exact finrank_bot ℂ ℂ
  · have hinj : Function.Injective (Algebra.lmul ℂ ℂ (c - 1)) := by
      intro a b hab
      change (c - 1) * a = (c - 1) * b at hab
      exact mul_left_cancel₀ (sub_ne_zero.mpr h) hab
    exact (LinearMap.finrank_range_of_inj hinj).trans (by simp)

theorem g32p_linRep_rank {G : Type} [Group G] (χ : G →* ℂˣ) (g : G) :
    Module.finrank ℂ (LinearMap.range ((papersLinRep χ).ρ g - 1)) =
      if (χ g : ℂ) = 1 then 0 else 1 := by
  exact g32p_scalar_rank (χ g : ℂ)


theorem g32p_class_determinant (j : Fin 13) :
    Matrix.det (b4b_toMatrix (g32p_classDatum j)) =
      if j.val < 6 then g32h_omega else if j.val < 12 then g32h_omega ^ 2 else 1 := by
  have h0 := g32p_generator_determinant 0
  have h1 := g32p_generator_determinant 1
  have h2 := g32p_generator_determinant 2
  fin_cases j <;> first
  | exact h0
  | exact h1
  | (change Matrix.det (b4b_toMatrix (b4b_generators 2 * b4b_generators 2)) = 1
     rw [map_mul, Matrix.det_mul, h2]
     norm_num)

theorem g32p_determinantRep_cwMult : g32p_cwMult g32p_determinantRep = 10 := by
  classical
  have hω : g32h_omega ≠ 1 := g32p_omega_primitive.ne_one (by decide)
  have hω2 : g32h_omega ^ 2 ≠ 1 :=
    g32p_omega_primitive.pow_ne_one_of_pos_of_lt (by decide) (by decide)
  unfold g32p_cwMult g32p_determinantRep
  simp only [g32p_linRep_rank, g32p_determinant_val, g32p_class_determinant]
  change -2 * (Module.finrank ℂ ℂ : ℤ) + _ = 10
  norm_num [Fin.sum_univ_succ, hω, hω2]

theorem g32p_linRep_inverse_cwMult (χ : g32p_G →* ℂˣ) :
    g32p_cwMult (papersLinRep χ⁻¹) = g32p_cwMult (papersLinRep χ) := by
  classical
  unfold g32p_cwMult
  simp only [g32p_linRep_rank, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_eq_one]
  rfl

theorem g32p_determinantConjugateRep_cwMult :
    g32p_cwMult g32p_determinantConjugateRep = 10 := by
  rw [g32p_determinantConjugateRep, g32p_linRep_inverse_cwMult]
  exact g32p_determinantRep_cwMult

theorem g32p_determinantRep_not_iso_conjugate :
    IsEmpty (g32p_determinantRep ≅ g32p_determinantConjugateRep) := by
  refine ⟨fun h => g32p_determinantRep_not_selfDual ?_⟩
  intro g
  exact (g32p_determinantRep_conjugate g).symm.trans (congrFun (FDRep.char_iso h) g).symm

theorem g32p_determinantRep_not_iso_rho : IsEmpty (g32p_determinantRep ≅ g32p_rho) := by
  refine ⟨fun h => ?_⟩
  have hc := congrFun (FDRep.char_iso h) 1
  rw [FDRep.char_one, FDRep.char_one] at hc
  have h1 : Module.finrank ℂ g32p_determinantRep = 1 := by
    change Module.finrank ℂ ℂ = 1
    simp
  have h4 : Module.finrank ℂ g32p_rho = 4 := by
    change Module.finrank ℂ (Fin 4 → ℂ) = 4
    simp
  rw [h1, h4] at hc
  norm_num at hc


open scoped Classical in
theorem g32p_top_mult (V : FDRep ℂ g32p_G) [Simple V] (χ : g32p_G →* ℂˣ) :
    papersMult ⊤ V (χ.comp (⊤ : Subgroup g32p_G).subtype) =
      if Nonempty (V ≅ papersLinRep χ) then 1 else 0 := by
  classical
  letI := Fintype.ofFinite (⊤ : Subgroup g32p_G)
  letI : Simple (papersLinRep χ) := g32p_linRep_simple χ
  have hn : 0 < Nat.card g32p_G := Nat.card_pos
  letI : Invertible (Nat.card g32p_G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr hn.ne')
  let e : (⊤ : Subgroup g32p_G) ≃ g32p_G := Subgroup.topEquiv.toEquiv
  have hs : (∑ h : (⊤ : Subgroup g32p_G),
      V.character h * (χ (h : g32p_G)⁻¹ : ℂ)) =
      ∑ g : g32p_G, V.character g * (χ g⁻¹ : ℂ) := by
    exact e.sum_comp (fun g => V.character g * (χ g⁻¹ : ℂ))
  have hc : Fintype.card (⊤ : Subgroup g32p_G) = Fintype.card g32p_G :=
    Fintype.card_congr e
  have hp : papersInner (papersRes ⊤ V.character)
      (papersLinChar (χ.comp (⊤ : Subgroup g32p_G).subtype)) =
      if Nonempty (V ≅ papersLinRep χ) then (1 : ℂ) else 0 := by
    change (Fintype.card (⊤ : Subgroup g32p_G) : ℂ)⁻¹ *
      (∑ h : (⊤ : Subgroup g32p_G), V.character h * (χ (h : g32p_G)⁻¹ : ℂ)) = _
    rw [hc, hs]
    simpa only [Nat.card_eq_fintype_card, g32p_linRep_character] using
      (FDRep.char_orthonormal V (papersLinRep χ))
  apply Nat.cast_injective (R := ℂ)
  rw [← papers_g32_mult_eq_inner]
  simpa only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hp


theorem g32p_determinant_power (g : g32p_G) :
    g32p_determinant g =
      g32p_omegaUnit ^ (Multiplicative.toAdd (g32p_determinantExponent g)).val := by
  have hl : g32p_omegaUnit_primitive.zmodEquivZPowers
      (Multiplicative.toAdd (g32p_determinantExponent g)) =
      Additive.ofMul (g32p_determinantToPowers g) :=
    g32p_omegaUnit_primitive.zmodEquivZPowers.apply_symm_apply _
  have hp := g32p_omegaUnit_primitive.zmodEquivZPowers_apply_coe_nat
    (Multiplicative.toAdd (g32p_determinantExponent g)).val
  rw [ZMod.natCast_zmod_val] at hp
  exact congrArg (fun x : Additive (Subgroup.zpowers g32p_omegaUnit) =>
    (Additive.toMul x : Subgroup.zpowers g32p_omegaUnit).val) (hl.symm.trans hp)

theorem g32p_determinantSupplier_complexCharacter :
    g32p_complexCharacter g32p_determinantSupplier =
      g32p_determinant.comp (⊤ : Subgroup g32p_G).subtype := by
  symm
  apply g32p_complexCharacter_unique g32p_determinantSupplier
    (g32p_determinant.comp (⊤ : Subgroup g32p_G).subtype)
  intro h
  change (g32p_determinant h : ℂ) =
    g32h_omega ^ (Multiplicative.toAdd (g32p_determinantExponent h)).val
  simpa only [Units.val_pow_eq_pow_val, g32p_omegaUnit_val] using
    congrArg (fun u : ℂˣ => (u : ℂ)) (g32p_determinant_power h)

theorem g32p_determinantSupplier_mult :
    papersMult g32p_determinantSupplier.H g32p_determinantRep
      (g32p_complexCharacter g32p_determinantSupplier) = 1 := by
  rw [g32p_determinantSupplier_complexCharacter]
  change papersMult ⊤ (papersLinRep g32p_determinant)
    (g32p_determinant.comp (⊤ : Subgroup g32p_G).subtype) = 1
  letI : Simple (papersLinRep g32p_determinant) := g32p_linRep_simple _
  rw [g32p_top_mult]
  simp only [show Nonempty (papersLinRep g32p_determinant ≅
    papersLinRep g32p_determinant) from ⟨Iso.refl _⟩, if_true]

theorem g32p_determinantSupplier_conjugate_mult :
    papersMult g32p_determinantSupplier.H g32p_determinantConjugateRep
      (g32p_complexCharacter g32p_determinantSupplier) = 0 := by
  rw [g32p_determinantSupplier_complexCharacter]
  change papersMult ⊤ g32p_determinantConjugateRep
    (g32p_determinant.comp (⊤ : Subgroup g32p_G).subtype) = 0
  letI := g32p_determinantConjugateRep_simple
  rw [g32p_top_mult]
  have hn : ¬ Nonempty (g32p_determinantConjugateRep ≅ papersLinRep g32p_determinant) := by
    rintro ⟨h⟩
    exact g32p_determinantRep_not_iso_conjugate.false h.symm
  exact if_neg hn

end HodgeLean.Foundations.Program
