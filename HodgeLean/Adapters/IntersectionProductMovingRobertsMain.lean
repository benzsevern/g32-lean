import HodgeLean.Adapters.IntersectionProductMovingRobertsDiagonal

/-! # Roberts' main lemma

Let `π_ℓ : X → ℙⁿ` be a finite linear projection of `X = V(I_X) ⊂ ℙᴺ`, `Z` and `W` subvarieties of
`X`, and `Z'` a component of `π_ℓ⁻¹(π_ℓ(Z)) = C_L(Z) ∩ X` other than `Z`. A point `y` of
`Z' ∩ W` is the first point of a pair `(y, z)` with `z ∈ Z` and the same projection
(`a3r_exists_pair_prime`, `a3r_exists_pair_prime_over`). Either the pair is off the diagonal, and
the secant bound gives `y` the expected dimension (`a3r_secant_dim`), or `z = y ∈ Z ∩ W`; then
`π_ℓ` is ramified at `y` (`a3r_diag_of_unramified`), so `y` is a proper specialization of a
component of `Z ∩ W`, which loses one unit of excess (`a3r_dim_add_one_le`). This is
`a3r_roberts_main`.

Dimensions are those of affine cones (`ringKrullDim (ℂ[x]/P)`), one more than projective
dimensions; the excess condition `dim Y + dim X ≤ dim Z + dim W + k` reads the same in both.

Source: J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970*, Wolters-Noordhoff
(1972), 89–96, Main Lemma; Fulton, *Intersection Theory*, second edition, Example 11.4.1.
HC no distance; AV milestone no distance.
-/

noncomputable section

open MvPolynomial TensorProduct

namespace HodgeLean.Adapters

section Main

variable {ρ σ : Type} [Fintype ρ] [Fintype σ]

/-- A proper specialization drops the dimension. -/
theorem a3r_dim_add_one_le (P Y : Ideal (MvPolynomial σ ℂ)) [P.IsPrime] [Y.IsPrime] (hlt : P < Y) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Y) + 1 ≤ ringKrullDim (MvPolynomial σ ℂ ⧸ P) := by
  set D := MvPolynomial σ ℂ ⧸ P
  have : Algebra.FiniteType ℂ D :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have hker : RingHom.ker (Ideal.Quotient.mk P) ≤ Y := by rw [Ideal.mk_ker]; exact hlt.le
  set Q := Y.map (Ideal.Quotient.mk P)
  have hQ : Q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have h := hc9k8_height_add_ringKrullDim_quotient (k := ℂ) Q
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hlt.le)] at h
  have hne : Q ≠ ⊥ := by
    obtain ⟨y, hyY, hyP⟩ := IsConcreteLE.exists_of_lt hlt
    intro hQb
    have : Ideal.Quotient.mk P y ∈ Q := Ideal.mem_map_of_mem _ hyY
    rw [hQb, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hyP this
  have hht : (1 : ℕ∞) ≤ Q.height := by
    rw [Order.one_le_iff_ne_zero]
    exact fun h0 => hne (Ideal.height_eq_zero_iff_eq_bot.1 h0)
  rw [← h, add_comm]
  gcongr
  exact_mod_cast hht

/-- The difference coordinates `x_k ⊗ 1 - 1 ⊗ x_k` of `ℂ[x]/P ⊗ ℂ[x]/P'`. -/
abbrev a3r_δD (P P' : Ideal (MvPolynomial σ ℂ)) (k : σ) :
    (MvPolynomial σ ℂ ⧸ P) ⊗[ℂ] (MvPolynomial σ ℂ ⧸ P') :=
  Ideal.Quotient.mk P (X k) ⊗ₜ 1 - 1 ⊗ₜ Ideal.Quotient.mk P' (X k)

/-- The secant bound for one pair: if pairs `(w, z)` with `w ∈ V(P_W)`, `z ∈ V(P_Z)`, `w ≠ z` and the
same projection have the expected dimension, then so does the first point of such a pair. -/
theorem a3r_secant_dim (PW PZ : Ideal (MvPolynomial σ ℂ)) [PW.IsPrime] [PZ.IsPrime]
    (ℓ : Matrix ρ σ ℂ)
    (hsec : ∀ (j : σ) (𝔓 : Ideal ((MvPolynomial σ ℂ ⧸ PW) ⊗[ℂ] (MvPolynomial σ ℂ ⧸ PZ))),
      𝔓.IsPrime → a3r_δD PW PZ j ∉ 𝔓 →
      (∀ i, ∑ k, algebraMap ℂ _ (ℓ i k) * a3r_δD PW PZ k - 0 ∈ 𝔓) →
      ringKrullDim (_ ⧸ 𝔓) + Fintype.card ρ ≤
        ringKrullDim ((MvPolynomial σ ℂ ⧸ PW) ⊗[ℂ] (MvPolynomial σ ℂ ⧸ PZ)))
    (𝔔' : Ideal (MvPolynomial (σ ⊕ σ) ℂ)) [𝔔'.IsPrime] (hW : PW ≤ 𝔔'.comap a3r_inl)
    (hZ : PZ ≤ 𝔔'.comap a3r_inr)
    (hΛ : ∀ i, a3r_inl (a3r_lin ℓ (X i)) - a3r_inr (a3r_lin ℓ (X i)) ∈ 𝔔') (j : σ)
    (hj : a3r_δ j ∉ 𝔔') :
    ringKrullDim (MvPolynomial σ ℂ ⧸ 𝔔'.comap a3r_inl) + Fintype.card ρ ≤
      ringKrullDim (MvPolynomial σ ℂ ⧸ PW) + ringKrullDim (MvPolynomial σ ℂ ⧸ PZ) := by
  classical
  set T := MvPolynomial (σ ⊕ σ) ℂ
  set D := (MvPolynomial σ ℂ ⧸ PW) ⊗[ℂ] (MvPolynomial σ ℂ ⧸ PZ)
  let θ₁ : MvPolynomial σ ℂ ⧸ PW →ₐ[ℂ] T ⧸ 𝔔' := Ideal.quotientMapₐ 𝔔' a3r_inl hW
  let θ₂ : MvPolynomial σ ℂ ⧸ PZ →ₐ[ℂ] T ⧸ 𝔔' := Ideal.quotientMapₐ 𝔔' a3r_inr hZ
  let Θ : D →ₐ[ℂ] T ⧸ 𝔔' := Algebra.TensorProduct.lift θ₁ θ₂ fun _ _ => Commute.all _ _
  have hΘ1 : ∀ F, Θ (Ideal.Quotient.mk PW F ⊗ₜ 1) = Ideal.Quotient.mk 𝔔' (a3r_inl F) := by
    intro F
    change θ₁ (Ideal.Quotient.mk PW F) * θ₂ 1 = _
    rw [map_one, mul_one]
    rfl
  have hΘ2 : ∀ F, Θ (1 ⊗ₜ Ideal.Quotient.mk PZ F) = Ideal.Quotient.mk 𝔔' (a3r_inr F) := by
    intro F
    change θ₁ 1 * θ₂ (Ideal.Quotient.mk PZ F) = _
    rw [map_one, one_mul]
    rfl
  have hδ : ∀ k, Θ (a3r_δD PW PZ k) = Ideal.Quotient.mk 𝔔' (a3r_δ k) := by
    intro k
    rw [map_sub, hΘ1, hΘ2, rename_X, rename_X, map_sub]
  -- surjectivity
  have hsurj : Function.Surjective Θ := by
    intro y
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction F using MvPolynomial.induction_on with
    | C c => exact ⟨algebraMap ℂ D c, by rw [AlgHom.commutes]; rfl⟩
    | add F G hF hG =>
      obtain ⟨a, ha⟩ := hF
      obtain ⟨b, hb⟩ := hG
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | mul_X F k hF =>
      obtain ⟨a, ha⟩ := hF
      rcases k with k | k
      · refine ⟨a * (Ideal.Quotient.mk PW (X k) ⊗ₜ 1), ?_⟩
        rw [map_mul, ha, hΘ1, rename_X, map_mul]
      · refine ⟨a * (1 ⊗ₜ Ideal.Quotient.mk PZ (X k)), ?_⟩
        rw [map_mul, ha, hΘ2, rename_X, map_mul]
  set 𝔓 := RingHom.ker (Θ : D →+* T ⧸ 𝔔')
  have h𝔓 : 𝔓.IsPrime := RingHom.ker_isPrime _
  have hj' : a3r_δD PW PZ j ∉ 𝔓 := by
    rw [RingHom.mem_ker]
    change Θ _ ≠ 0
    rw [hδ]
    exact fun h => hj (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have heq : ∀ i, ∑ k, algebraMap ℂ D (ℓ i k) * a3r_δD PW PZ k - 0 ∈ 𝔓 := by
    intro i
    rw [sub_zero, RingHom.mem_ker]
    change Θ _ = 0
    rw [map_sum]
    simp only [map_mul, AlgHom.commutes, hδ]
    have : ∑ k, algebraMap ℂ (T ⧸ 𝔔') (ℓ i k) * Ideal.Quotient.mk 𝔔' (a3r_δ k) =
        Ideal.Quotient.mk 𝔔' (a3r_inl (a3r_lin ℓ (X i)) - a3r_inr (a3r_lin ℓ (X i))) := by
      rw [a3r_lin_X, map_sum, map_sum, ← Finset.sum_sub_distrib, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [map_mul, rename_C, rename_X, ← mul_sub]
      rfl
    rw [this, Ideal.Quotient.eq_zero_iff_mem]
    exact hΛ i
  have hb := hsec j 𝔓 h𝔓 hj' heq
  -- dimensions
  have : Nontrivial (MvPolynomial σ ℂ ⧸ PW) :=
    Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
  have : Nontrivial (MvPolynomial σ ℂ ⧸ PZ) :=
    Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ PW) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ PZ) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have hD : ringKrullDim D = ringKrullDim (MvPolynomial σ ℂ ⧸ PW) +
      ringKrullDim (MvPolynomial σ ℂ ⧸ PZ) := hc9k8_ringKrullDim_tensorProduct
  have hDP : ringKrullDim (D ⧸ 𝔓) = ringKrullDim (T ⧸ 𝔔') :=
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective
      (f := (Θ : D →+* T ⧸ 𝔔')) hsurj)
  rw [hD, hDP] at hb
  -- the first point embeds in the pair
  have hle : 𝔔'.comap a3r_inl ≤ Ideal.comap (a3r_inl : MvPolynomial σ ℂ →ₐ[ℂ] T) 𝔔' := le_rfl
  let ι := Ideal.quotientMapₐ 𝔔' (a3r_inl : MvPolynomial σ ℂ →ₐ[ℂ] T) hle
  have hι : Function.Injective ι := Ideal.quotientMap_injective
  have : Algebra.FiniteType ℂ (T ⧸ 𝔔') :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ 𝔔'.comap a3r_inl) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have hdim := a3m_ringKrullDim_le_of_injective ι hι
  calc _ ≤ ringKrullDim (T ⧸ 𝔔') + Fintype.card ρ := by gcongr
    _ ≤ _ := hb

/-- Roberts' main lemma, algebraic form. Let `π_ℓ : X = V(I_X) → ℙⁿ` be a finite linear
projection, `Z = V(P_Z)` and `W = V(P_W)` subvarieties of `X`, and `Z' = V(Q')` another component
of `π_ℓ⁻¹(π_ℓ(Z))`. Suppose that pairs `(w, z) ∈ W × Z` off the diagonal with the same projection
have the expected dimension (`hsec`), that `π_ℓ` is unramified at the generic points of the
components of `Z ∩ W` (`hunr`), and that `Z ∩ W` has excess at most `k + 1`. Then every point of
`Z' ∩ W` has excess at most `k`: the residual intersections lose one unit of excess.
Source: J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970* (1972), 89–96,
Main Lemma; Fulton, *Intersection Theory*, second edition, Example 11.4.1. -/
theorem a3r_roberts_main (IX PZ PW : Ideal (MvPolynomial σ ℂ)) [IX.IsPrime] [PZ.IsPrime]
    [PW.IsPrime] (hXZ : IX ≤ PZ) (ℓ : Matrix ρ σ ℂ)
    (hdimX : ringKrullDim (MvPolynomial σ ℂ ⧸ IX) = Fintype.card ρ)
    (hfin : ((Ideal.Quotient.mk IX).comp (a3r_lin ℓ).toRingHom).Finite)
    (hsec : ∀ (j : σ) (𝔓 : Ideal ((MvPolynomial σ ℂ ⧸ PW) ⊗[ℂ] (MvPolynomial σ ℂ ⧸ PZ))),
      𝔓.IsPrime → a3r_δD PW PZ j ∉ 𝔓 →
      (∀ i, ∑ k, algebraMap ℂ _ (ℓ i k) * a3r_δD PW PZ k - 0 ∈ 𝔓) →
      ringKrullDim (_ ⧸ 𝔓) + Fintype.card ρ ≤
        ringKrullDim ((MvPolynomial σ ℂ ⧸ PW) ⊗[ℂ] (MvPolynomial σ ℂ ⧸ PZ)))
    (hunr : ∀ 𝔶 ∈ (PZ ⊔ PW).minimalPrimes, (∃ j, X j ∉ 𝔶) → ∃ f ∉ 𝔶,
      letI : Algebra (MvPolynomial ρ ℂ) (MvPolynomial σ ℂ ⧸ IX) :=
        ((Ideal.Quotient.mk IX).comp (a3r_lin ℓ).toRingHom).toAlgebra
      Algebra.FormallyUnramified (MvPolynomial ρ ℂ) (Localization.Away (Ideal.Quotient.mk IX f)))
    (k : ℕ) (hexc : ∀ 𝔶 ∈ (PZ ⊔ PW).minimalPrimes, (∃ j, X j ∉ 𝔶) →
      ringKrullDim (MvPolynomial σ ℂ ⧸ 𝔶) + ringKrullDim (MvPolynomial σ ℂ ⧸ IX) ≤
        ringKrullDim (MvPolynomial σ ℂ ⧸ PZ) + ringKrullDim (MvPolynomial σ ℂ ⧸ PW) + (k + 1 : ℕ))
    (Q' : Ideal (MvPolynomial σ ℂ)) [Q'.IsPrime] (hXQ : IX ≤ Q')
    (hQ : Q'.comap (a3r_lin ℓ) = PZ.comap (a3r_lin ℓ)) (hne : Q' ≠ PZ)
    (Y : Ideal (MvPolynomial σ ℂ)) [Y.IsPrime] (hY : Q' ⊔ PW ≤ Y) (hYrel : ∃ j, X j ∉ Y) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Y) + ringKrullDim (MvPolynomial σ ℂ ⧸ IX) ≤
      ringKrullDim (MvPolynomial σ ℂ ⧸ PZ) + ringKrullDim (MvPolynomial σ ℂ ⧸ PW) + k := by
  classical
  obtain ⟨𝔔, h𝔔, hK, h𝔔l, h𝔔r⟩ := a3r_exists_pair_prime IX ℓ Q' PZ hXQ hXZ hQ
  obtain ⟨𝔔', h𝔔', hle, h𝔔'l⟩ := a3r_exists_pair_prime_over IX ℓ hfin 𝔔 hK Y
    (h𝔔l ▸ le_sup_left.trans hY)
  have hK' : a3r_pairIdeal IX ℓ ≤ 𝔔' := hK.trans hle
  have hΛ : ∀ i, a3r_inl (a3r_lin ℓ (X i)) - a3r_inr (a3r_lin ℓ (X i)) ∈ 𝔔' :=
    fun i => hK' (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  by_cases hd : ∀ k, a3r_δ k ∈ 𝔔'
  · -- the pair specializes to the diagonal: `Y ⊇ P_Z`
    have hlr : ∀ F, F ∈ 𝔔'.comap a3r_inl ↔ F ∈ 𝔔'.comap a3r_inr := by
      intro F
      rw [Ideal.mem_comap, Ideal.mem_comap]
      have := a3r_inl_sub_inr_mem 𝔔' hd F
      constructor
      · intro h
        have := sub_mem h this
        rwa [sub_sub_cancel] at this
      · intro h
        have := add_mem this h
        rwa [sub_add_cancel] at this
    have hZY : PZ ≤ Y := by
      intro F hF
      rw [← h𝔔'l, hlr]
      exact hle (by rw [← h𝔔r] at hF; exact hF)
    obtain ⟨𝔶, h𝔶, h𝔶Y⟩ := Ideal.exists_minimalPrimes_le (sup_le hZY (le_sup_right.trans hY))
    have h𝔶p : 𝔶.IsPrime := h𝔶.1.1
    have h𝔶rel : ∃ j, X j ∉ 𝔶 := let ⟨j, hj⟩ := hYrel; ⟨j, fun h => hj (h𝔶Y h)⟩
    rcases eq_or_lt_of_le h𝔶Y with heq | hlt
    · -- unramified at `Y`: contradiction with `Q' ≠ P_Z`
      exfalso
      obtain ⟨f, hf, hunrf⟩ := hunr 𝔶 h𝔶 h𝔶rel
      rw [heq] at hf
      have hfQ : a3r_inl f ∉ 𝔔' := fun h => hf (by rw [← h𝔔'l]; exact h)
      have hd𝔔 := a3r_diag_of_unramified IX ℓ hfin f hunrf 𝔔 𝔔' hK hle hd hfQ
      apply hne
      ext F
      rw [← h𝔔l, ← h𝔔r, Ideal.mem_comap, Ideal.mem_comap]
      have := a3r_inl_sub_inr_mem 𝔔 hd𝔔 F
      constructor
      · intro h
        have := sub_mem h this
        rwa [sub_sub_cancel] at this
      · intro h
        have := add_mem this h
        rwa [sub_add_cancel] at this
    · -- a proper specialization of a component of `Z ∩ W`
      have h1 := a3r_dim_add_one_le 𝔶 Y hlt
      have h2 := hexc 𝔶 h𝔶 h𝔶rel
      refine a3r_withBot_le_of_add_le_add 1 ?_
      calc ringKrullDim (MvPolynomial σ ℂ ⧸ Y) + ringKrullDim (MvPolynomial σ ℂ ⧸ IX) + (1 : ℕ)
          = ringKrullDim (MvPolynomial σ ℂ ⧸ Y) + 1 + ringKrullDim (MvPolynomial σ ℂ ⧸ IX) := by
            rw [add_right_comm]; rfl
        _ ≤ ringKrullDim (MvPolynomial σ ℂ ⧸ 𝔶) + ringKrullDim (MvPolynomial σ ℂ ⧸ IX) := by
            gcongr
        _ ≤ _ := h2
        _ = _ := by push_cast; simp only [add_assoc]
  · -- a secant pair
    push Not at hd
    obtain ⟨j, hj⟩ := hd
    have hW : PW ≤ 𝔔'.comap a3r_inl := h𝔔'l ▸ le_sup_right.trans hY
    have hZ : PZ ≤ 𝔔'.comap a3r_inr := by
      rw [← h𝔔r]
      exact Ideal.comap_mono hle
    have h := a3r_secant_dim PW PZ ℓ hsec 𝔔' hW hZ hΛ j hj
    rw [h𝔔'l, ← hdimX] at h
    calc _ ≤ ringKrullDim (MvPolynomial σ ℂ ⧸ PW) + ringKrullDim (MvPolynomial σ ℂ ⧸ PZ) := h
      _ ≤ _ := by rw [add_comm (ringKrullDim (MvPolynomial σ ℂ ⧸ PW))]; exact le_add_of_nonneg_right (Nat.cast_nonneg' k)

end Main

end HodgeLean.Adapters
