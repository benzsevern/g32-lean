import HodgeLean.Adapters.IntersectionProductMovingRobertsPairs

/-! # The diagonal near an unramified point

If the linear projection `π_ℓ : V(I) → ℙⁿ` is unramified at a point `y`, the diagonal of
`V(I) ×_{ℙⁿ} V(I)` is open near `(y, y)`: a pair specializing to a diagonal pair `(y, y)` is itself
diagonal (`a3r_diag_of_unramified`). The proof uses the diagonal idempotent
`Algebra.FormallyUnramified.elem` of the unramified algebra `A_f`, mapped into the localizations
of the two pair domains at `f ⊗ f`.

Source: EGA IV, 17.4.2 (an unramified morphism has open diagonal); J. Roberts, *Chow's moving
lemma* (1972), proof of the Main Lemma; Mathlib, `Algebra.FormallyUnramified.elem`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open TensorProduct

namespace HodgeLean.Adapters

/-- Two maps from `A` to a ring `L`, agreeing on `R` and inverting `f`, induce a map
`A_f ⊗_R A_f → L`. -/
theorem a3r_exists_tensor_hom {R A L : Type} [CommRing R] [CommRing A] [Algebra R A] [CommRing L]
    (f : A) (a₁ a₂ : A →+* L) (h₁ : IsUnit (a₁ f)) (h₂ : IsUnit (a₂ f))
    (hR : a₁.comp (algebraMap R A) = a₂.comp (algebraMap R A)) :
    ∃ Φ : Localization.Away f ⊗[R] Localization.Away f →+* L, ∀ x y,
      Φ (x ⊗ₜ y) = IsLocalization.Away.lift f h₁ x * IsLocalization.Away.lift f h₂ y := by
  let _ : Algebra R L := (a₁.comp (algebraMap R A)).toAlgebra
  let l₁ : Localization.Away f →ₐ[R] L :=
    { IsLocalization.Away.lift f h₁ with
      commutes' := fun r => by
        change IsLocalization.Away.lift f h₁ (algebraMap R (Localization.Away f) r) = _
        rw [IsScalarTower.algebraMap_apply R A (Localization.Away f), IsLocalization.Away.lift_eq]
        rfl }
  let l₂ : Localization.Away f →ₐ[R] L :=
    { IsLocalization.Away.lift f h₂ with
      commutes' := fun r => by
        change IsLocalization.Away.lift f h₂ (algebraMap R (Localization.Away f) r) = _
        rw [IsScalarTower.algebraMap_apply R A (Localization.Away f), IsLocalization.Away.lift_eq]
        exact (congrArg (fun φ : R →+* L => φ r) hR).symm }
  exact ⟨(Algebra.TensorProduct.lift l₁ l₂ fun _ _ => Commute.all _ _).toRingHom, fun x y =>
    Algebra.TensorProduct.lift_tmul _ _ _ x y⟩

section Diag

open MvPolynomial

variable {ρ σ : Type} [Fintype ρ] [Fintype σ]

omit [Fintype ρ] in
theorem a3r_le_comap_inl (I : Ideal (MvPolynomial σ ℂ)) (ℓ : Matrix ρ σ ℂ)
    (P : Ideal (MvPolynomial (σ ⊕ σ) ℂ)) (hP : a3r_pairIdeal I ℓ ≤ P) :
    I ≤ P.comap (a3r_inl : MvPolynomial σ ℂ →ₐ[ℂ] _).toRingHom :=
  Ideal.map_le_iff_le_comap.1 ((a3r_map_inl_le I ℓ).trans hP)

omit [Fintype ρ] in
theorem a3r_le_comap_inr (I : Ideal (MvPolynomial σ ℂ)) (ℓ : Matrix ρ σ ℂ)
    (P : Ideal (MvPolynomial (σ ⊕ σ) ℂ)) (hP : a3r_pairIdeal I ℓ ≤ P) :
    I ≤ P.comap (a3r_inr : MvPolynomial σ ℂ →ₐ[ℂ] _).toRingHom :=
  Ideal.map_le_iff_le_comap.1 ((a3r_map_inr_le I ℓ).trans hP)

omit [Fintype ρ] in
/-- The diagonal argument: if the projection is unramified at the first point of a pair `𝔔'` on
the diagonal, then every pair `𝔔` specializing to `𝔔'` is already on the diagonal. Uses the
diagonal idempotent of the unramified algebra `A_f`.
Source: J. Roberts, *Chow's moving lemma* (1972), proof of the Main Lemma; EGA IV, 17.4.2 (the
diagonal of an unramified morphism is open); Mathlib, `Algebra.FormallyUnramified.elem`. -/
theorem a3r_diag_of_unramified (I : Ideal (MvPolynomial σ ℂ)) (ℓ : Matrix ρ σ ℂ)
    (hfin : ((Ideal.Quotient.mk I).comp (a3r_lin ℓ).toRingHom).Finite) (f : MvPolynomial σ ℂ)
    (hunr : letI : Algebra (MvPolynomial ρ ℂ) (MvPolynomial σ ℂ ⧸ I) :=
        ((Ideal.Quotient.mk I).comp (a3r_lin ℓ).toRingHom).toAlgebra
      Algebra.FormallyUnramified (MvPolynomial ρ ℂ) (Localization.Away (Ideal.Quotient.mk I f)))
    (𝔔 𝔔' : Ideal (MvPolynomial (σ ⊕ σ) ℂ)) [𝔔.IsPrime] [𝔔'.IsPrime]
    (hK : a3r_pairIdeal I ℓ ≤ 𝔔) (hle : 𝔔 ≤ 𝔔') (hdiag : ∀ k, a3r_δ k ∈ 𝔔')
    (hf : a3r_inl f ∉ 𝔔') : ∀ k, a3r_δ k ∈ 𝔔 := by
  classical
  set R := MvPolynomial ρ ℂ
  set A := MvPolynomial σ ℂ ⧸ I
  let _ : Algebra R A := ((Ideal.Quotient.mk I).comp (a3r_lin ℓ).toRingHom).toAlgebra
  set Af := Localization.Away (Ideal.Quotient.mk I f)
  have : Algebra.FormallyUnramified R Af := hunr
  have : Module.Finite R A := hfin
  have : Algebra.FiniteType R Af := Algebra.FiniteType.trans (S := A) inferInstance
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (Ideal.Quotient.mk I f)) Af)
  have : Algebra.EssFiniteType R Af := Algebra.EssFiniteType.of_finiteType R Af
  set e := Algebra.FormallyUnramified.elem R Af
  have hK' : a3r_pairIdeal I ℓ ≤ 𝔔' := hK.trans hle
  -- the two maps `A → T/𝔔` and `A → T/𝔔'`
  let left : A →+* MvPolynomial (σ ⊕ σ) ℂ ⧸ 𝔔 :=
    Ideal.quotientMap 𝔔 (a3r_inl : MvPolynomial σ ℂ →ₐ[ℂ] _).toRingHom (a3r_le_comap_inl I ℓ 𝔔 hK)
  let right : A →+* MvPolynomial (σ ⊕ σ) ℂ ⧸ 𝔔 :=
    Ideal.quotientMap 𝔔 (a3r_inr : MvPolynomial σ ℂ →ₐ[ℂ] _).toRingHom (a3r_le_comap_inr I ℓ 𝔔 hK)
  let left' : A →+* MvPolynomial (σ ⊕ σ) ℂ ⧸ 𝔔' :=
    Ideal.quotientMap 𝔔' (a3r_inl : MvPolynomial σ ℂ →ₐ[ℂ] _).toRingHom (a3r_le_comap_inl I ℓ 𝔔' hK')
  let right' : A →+* MvPolynomial (σ ⊕ σ) ℂ ⧸ 𝔔' :=
    Ideal.quotientMap 𝔔' (a3r_inr : MvPolynomial σ ℂ →ₐ[ℂ] _).toRingHom (a3r_le_comap_inr I ℓ 𝔔' hK')
  have hleft : ∀ F, left (Ideal.Quotient.mk I F) = Ideal.Quotient.mk 𝔔 (a3r_inl F) :=
    fun _ => Ideal.quotientMap_mk
  have hright : ∀ F, right (Ideal.Quotient.mk I F) = Ideal.Quotient.mk 𝔔 (a3r_inr F) :=
    fun _ => Ideal.quotientMap_mk
  have hleft' : ∀ F, left' (Ideal.Quotient.mk I F) = Ideal.Quotient.mk 𝔔' (a3r_inl F) :=
    fun _ => Ideal.quotientMap_mk
  have hright' : ∀ F, right' (Ideal.Quotient.mk I F) = Ideal.Quotient.mk 𝔔' (a3r_inr F) :=
    fun _ => Ideal.quotientMap_mk
  have hR : left.comp (algebraMap R A) = right.comp (algebraMap R A) := by
    refine RingHom.ext fun F => ?_
    change left (Ideal.Quotient.mk I (a3r_lin ℓ F)) = right (Ideal.Quotient.mk I (a3r_lin ℓ F))
    rw [hleft, hright, Ideal.Quotient.eq]
    exact hK (a3r_inl_lin_sub_inr_lin_mem I ℓ F)
  have hR' : left'.comp (algebraMap R A) = right'.comp (algebraMap R A) := by
    refine RingHom.ext fun F => ?_
    change left' (Ideal.Quotient.mk I (a3r_lin ℓ F)) = right' (Ideal.Quotient.mk I (a3r_lin ℓ F))
    rw [hleft', hright', Ideal.Quotient.eq]
    exact hK' (a3r_inl_lin_sub_inr_lin_mem I ℓ F)
  -- the element `u = f ⊗ f`
  set u := a3r_inl f * a3r_inr f
  have hfr : a3r_inr f ∉ 𝔔' := fun h => hf (by
    have := add_mem (a3r_inl_sub_inr_mem 𝔔' hdiag f) h
    rwa [sub_add_cancel] at this)
  have hu' : u ∉ 𝔔' := fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hf hfr
  have hu : u ∉ 𝔔 := fun h => hu' (hle h)
  have hu0 : Ideal.Quotient.mk 𝔔 u ≠ 0 := fun h => hu (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hu0' : Ideal.Quotient.mk 𝔔' u ≠ 0 := fun h => hu' (Ideal.Quotient.eq_zero_iff_mem.1 h)
  set Lq := Localization.Away (Ideal.Quotient.mk 𝔔 u)
  set Lq' := Localization.Away (Ideal.Quotient.mk 𝔔' u)
  have : IsDomain Lq := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hu0)
  have : IsDomain Lq' := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hu0')
  -- units
  have hunit : ∀ (P : Ideal (MvPolynomial (σ ⊕ σ) ℂ)) (L : Type) [CommRing L]
      [Algebra (MvPolynomial (σ ⊕ σ) ℂ ⧸ P) L] [IsLocalization.Away (Ideal.Quotient.mk P u) L],
      IsUnit (algebraMap _ L (Ideal.Quotient.mk P (a3r_inl f))) ∧
        IsUnit (algebraMap _ L (Ideal.Quotient.mk P (a3r_inr f))) := by
    intro P L _ _ _
    have h := IsLocalization.Away.algebraMap_isUnit (S := L) (Ideal.Quotient.mk P u)
    rw [map_mul, map_mul] at h
    exact ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩
  set a₁ := (algebraMap _ Lq).comp left
  set a₂ := (algebraMap _ Lq).comp right
  set a₁' := (algebraMap _ Lq').comp left'
  set a₂' := (algebraMap _ Lq').comp right'
  have h₁ : IsUnit (a₁ (Ideal.Quotient.mk I f)) := by
    simp only [a₁, RingHom.comp_apply, hleft]; exact (hunit 𝔔 Lq).1
  have h₂ : IsUnit (a₂ (Ideal.Quotient.mk I f)) := by
    simp only [a₂, RingHom.comp_apply, hright]; exact (hunit 𝔔 Lq).2
  have h₁' : IsUnit (a₁' (Ideal.Quotient.mk I f)) := by
    simp only [a₁', RingHom.comp_apply, hleft']; exact (hunit 𝔔' Lq').1
  have h₂' : IsUnit (a₂' (Ideal.Quotient.mk I f)) := by
    simp only [a₂', RingHom.comp_apply, hright']; exact (hunit 𝔔' Lq').2
  have hRq : a₁.comp (algebraMap R A) = a₂.comp (algebraMap R A) := by
    simp only [a₁, a₂, RingHom.comp_assoc, hR]
  have hRq' : a₁'.comp (algebraMap R A) = a₂'.comp (algebraMap R A) := by
    simp only [a₁', a₂', RingHom.comp_assoc, hR']
  obtain ⟨Φ, hΦ⟩ := a3r_exists_tensor_hom (R := R) _ a₁ a₂ h₁ h₂ hRq
  obtain ⟨Φ', hΦ'⟩ := a3r_exists_tensor_hom (R := R) _ a₁' a₂' h₁' h₂' hRq'
  set l₁ := IsLocalization.Away.lift (S := Af) _ h₁
  set l₂ := IsLocalization.Away.lift (S := Af) _ h₂
  set l₁' := IsLocalization.Away.lift (S := Af) _ h₁'
  set l₂' := IsLocalization.Away.lift (S := Af) _ h₂'
  -- the map `π : Lq → Lq'`
  let π : Lq →+* Lq' := IsLocalization.map (M := Submonoid.powers (Ideal.Quotient.mk 𝔔 u))
    (T := Submonoid.powers (Ideal.Quotient.mk 𝔔' u)) Lq' (Ideal.Quotient.factor hle)
    (Submonoid.powers_le.2 (Submonoid.mem_powers (Ideal.Quotient.mk 𝔔' u)))
  have hπ : ∀ z, π (algebraMap _ Lq z) = algebraMap _ Lq' (Ideal.Quotient.factor hle z) :=
    fun z => IsLocalization.map_eq _ z
  have hfl : ∀ F, Ideal.Quotient.factor hle (left (Ideal.Quotient.mk I F)) =
      left' (Ideal.Quotient.mk I F) := by
    intro F; rw [hleft, hleft']; rfl
  have hfr' : ∀ F, Ideal.Quotient.factor hle (right (Ideal.Quotient.mk I F)) =
      right' (Ideal.Quotient.mk I F) := by
    intro F; rw [hright, hright']; rfl
  have hl₁ : ∀ a, l₁ (algebraMap A Af a) = a₁ a := IsLocalization.Away.lift_eq _ h₁
  have hl₂ : ∀ a, l₂ (algebraMap A Af a) = a₂ a := IsLocalization.Away.lift_eq _ h₂
  have hl₁' : ∀ a, l₁' (algebraMap A Af a) = a₁' a := IsLocalization.Away.lift_eq _ h₁'
  have hl₂' : ∀ a, l₂' (algebraMap A Af a) = a₂' a := IsLocalization.Away.lift_eq _ h₂'
  have hπl₁ : π.comp l₁ = l₁' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk I f)) ?_
    refine RingHom.ext fun a => ?_
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective a
    change π (l₁ (algebraMap A Af _)) = l₁' (algebraMap A Af _)
    rw [hl₁, hl₁']
    change π (algebraMap _ Lq (left _)) = algebraMap _ Lq' (left' _)
    rw [hπ, hfl]
  have hπl₂ : π.comp l₂ = l₂' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk I f)) ?_
    refine RingHom.ext fun a => ?_
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective a
    change π (l₂ (algebraMap A Af _)) = l₂' (algebraMap A Af _)
    rw [hl₂, hl₂']
    change π (algebraMap _ Lq (right _)) = algebraMap _ Lq' (right' _)
    rw [hπ, hfr']
  have hl' : l₁' = l₂' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk I f)) ?_
    refine RingHom.ext fun a => ?_
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective a
    change l₁' (algebraMap A Af _) = l₂' (algebraMap A Af _)
    rw [hl₁', hl₂']
    change algebraMap _ Lq' (left' _) = algebraMap _ Lq' (right' _)
    rw [hleft', hright', Ideal.Quotient.eq.2 (a3r_inl_sub_inr_mem 𝔔' hdiag F)]
  -- `Φ' = l₁' ∘ μ` and `Φ' = π ∘ Φ`
  have hΦ'μ : ∀ z, Φ' z = l₁' (Algebra.TensorProduct.lmul' R z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      rw [hΦ', Algebra.TensorProduct.lmul'_apply_tmul]
      exact (congrArg (l₁' x * ·) (RingHom.congr_fun hl' y).symm).trans (map_mul l₁' x y).symm
    | add x y hx hy =>
      rw [RingHom.map_add Φ' x y, hx, hy, ← RingHom.map_add l₁']
      exact congrArg l₁'
        ((Algebra.TensorProduct.lmul' R : Af ⊗[R] Af →ₐ[R] Af).toRingHom.map_add x y).symm
  have hπΦ : ∀ z, π (Φ z) = Φ' z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      rw [hΦ, hΦ', map_mul π]
      exact congr_arg₂ (· * ·) (RingHom.congr_fun hπl₁ x) (RingHom.congr_fun hπl₂ y)
    | add x y hx hy => rw [RingHom.map_add Φ x y, RingHom.map_add π, hx, hy, RingHom.map_add Φ' x y]
  have he : Φ e ≠ 0 := by
    intro h0
    have := hπΦ e
    rw [h0, RingHom.map_zero, hΦ'μ, Algebra.FormallyUnramified.lmul_elem, RingHom.map_one] at this
    exact zero_ne_one this
  intro k
  set a := algebraMap A Af (Ideal.Quotient.mk I (X k))
  have h0 := congrArg Φ (Algebra.FormallyUnramified.one_tmul_sub_tmul_one_mul_elem (R := R) a)
  rw [RingHom.map_mul, RingHom.map_zero] at h0
  have h1 : Φ (1 ⊗ₜ[R] a - a ⊗ₜ[R] 1) = 0 := (mul_eq_zero.1 h0).resolve_right he
  rw [RingHom.map_sub, hΦ, hΦ, RingHom.map_one, RingHom.map_one, one_mul, mul_one, sub_eq_zero] at h1
  rw [hl₁, hl₂] at h1
  change algebraMap _ Lq (right _) = algebraMap _ Lq (left _) at h1
  rw [hleft, hright] at h1
  have h2 := IsLocalization.injective Lq (powers_le_nonZeroDivisors_of_noZeroDivisors hu0) h1
  have h3 := Ideal.Quotient.eq.1 h2
  have : a3r_δ k = -(a3r_inr (X k) - a3r_inl (X k)) := by simp
  rw [this]
  exact neg_mem h3

end Diag

end HodgeLean.Adapters
