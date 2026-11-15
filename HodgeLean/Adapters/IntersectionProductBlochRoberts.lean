import HodgeLean.Adapters.IntersectionProductMovingRoberts

/-! # Roberts' main lemma with a relevance condition

Roberts' main lemma (`a3r_roberts_main`) asks for the excess and unramifiedness hypotheses at the
components of `Z ∩ W` which are relevant, that is, not inside the vertex `x = 0` of the affine
cone, and concludes for relevant points. Over `ℙ¹_t` the relative affine cone over `X × 𝔸¹` lives
in `ℂ[x, t]` and its irrelevant locus is the vertex line `x = 0`, cut out by the `x`-variables
only. This file restates the main lemma for an arbitrary relevance condition `rel` stable under
generization (`a3k_roberts_main_rel`); the proof is Roberts' and uses relevance only to pass from
a point to the components of `Z ∩ W` below it.

Source: J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970*, Wolters-Noordhoff
(1972), 89–96, Main Lemma; Fulton, *Intersection Theory*, second edition, Example 11.4.1;
S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994), §2 (the main
lemma over a base). HC no distance; AV milestone no distance.
-/

noncomputable section

open MvPolynomial TensorProduct

namespace HodgeLean.Adapters

section MainRel

variable {ρ σ : Type} [Fintype ρ] [Fintype σ]

/-- Roberts' main lemma, algebraic form, for a relevance condition `rel` stable under
generization: with the hypotheses of `a3r_roberts_main` at the relevant components of `Z ∩ W`,
every relevant point of `Z' ∩ W` has excess at most `k`.
Source: J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970* (1972), 89–96,
Main Lemma; Fulton, *Intersection Theory*, second edition, Example 11.4.1. -/
theorem a3k_roberts_main_rel (IX PZ PW : Ideal (MvPolynomial σ ℂ)) [IX.IsPrime] [PZ.IsPrime]
    [PW.IsPrime] (hXZ : IX ≤ PZ) (ℓ : Matrix ρ σ ℂ) (rel : Ideal (MvPolynomial σ ℂ) → Prop)
    (hrel : ∀ P Q, P ≤ Q → rel Q → rel P)
    (hdimX : ringKrullDim (MvPolynomial σ ℂ ⧸ IX) = Fintype.card ρ)
    (hfin : ((Ideal.Quotient.mk IX).comp (a3r_lin ℓ).toRingHom).Finite)
    (hsec : ∀ (j : σ) (𝔓 : Ideal ((MvPolynomial σ ℂ ⧸ PW) ⊗[ℂ] (MvPolynomial σ ℂ ⧸ PZ))),
      𝔓.IsPrime → a3r_δD PW PZ j ∉ 𝔓 →
      (∀ i, ∑ k, algebraMap ℂ _ (ℓ i k) * a3r_δD PW PZ k - 0 ∈ 𝔓) →
      ringKrullDim (_ ⧸ 𝔓) + Fintype.card ρ ≤
        ringKrullDim ((MvPolynomial σ ℂ ⧸ PW) ⊗[ℂ] (MvPolynomial σ ℂ ⧸ PZ)))
    (hunr : ∀ 𝔶 ∈ (PZ ⊔ PW).minimalPrimes, rel 𝔶 → ∃ f ∉ 𝔶,
      letI : Algebra (MvPolynomial ρ ℂ) (MvPolynomial σ ℂ ⧸ IX) :=
        ((Ideal.Quotient.mk IX).comp (a3r_lin ℓ).toRingHom).toAlgebra
      Algebra.FormallyUnramified (MvPolynomial ρ ℂ) (Localization.Away (Ideal.Quotient.mk IX f)))
    (k : ℕ) (hexc : ∀ 𝔶 ∈ (PZ ⊔ PW).minimalPrimes, rel 𝔶 →
      ringKrullDim (MvPolynomial σ ℂ ⧸ 𝔶) + ringKrullDim (MvPolynomial σ ℂ ⧸ IX) ≤
        ringKrullDim (MvPolynomial σ ℂ ⧸ PZ) + ringKrullDim (MvPolynomial σ ℂ ⧸ PW) + (k + 1 : ℕ))
    (Q' : Ideal (MvPolynomial σ ℂ)) [Q'.IsPrime] (hXQ : IX ≤ Q')
    (hQ : Q'.comap (a3r_lin ℓ) = PZ.comap (a3r_lin ℓ)) (hne : Q' ≠ PZ)
    (Y : Ideal (MvPolynomial σ ℂ)) [Y.IsPrime] (hY : Q' ⊔ PW ≤ Y) (hYrel : rel Y) :
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
    have h𝔶rel : rel 𝔶 := hrel 𝔶 Y h𝔶Y hYrel
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


/-- With the relevance of `a3r_roberts_main`, the relevant version gives Roberts' lemma back. -/
example (IX PZ PW : Ideal (MvPolynomial σ ℂ)) [IX.IsPrime] [PZ.IsPrime] [PW.IsPrime]
    (hXZ : IX ≤ PZ) (ℓ : Matrix ρ σ ℂ)
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
      ringKrullDim (MvPolynomial σ ℂ ⧸ PZ) + ringKrullDim (MvPolynomial σ ℂ ⧸ PW) + k :=
  a3k_roberts_main_rel IX PZ PW hXZ ℓ (fun P => ∃ j, X j ∉ P)
    (fun _ _ hPQ ⟨j, hj⟩ => ⟨j, fun h => hj (hPQ h)⟩) hdimX hfin hsec hunr k hexc Q' hXQ hQ hne
    Y hY hYrel

end MainRel

end HodgeLean.Adapters
