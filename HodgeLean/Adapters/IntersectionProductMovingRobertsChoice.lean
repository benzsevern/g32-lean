import HodgeLean.Adapters.IntersectionProductMovingRobertsUnramified

/-! # Choosing the cone and the translate

`a3r_exists_cone_translate` assembles Roberts' construction in the homogeneous coordinate ring of
`ℙᴺ`: a generic projection `ℓ` (finite, with generic secants and unramified at the components of
each `Z ∩ W`) gives the cone `C = C_L(Z)`, a homogeneous prime of the expected dimension whose
residual intersection with `X` meets each `W` with smaller excess (`a3r_roberts_main`); a generic
matrix `M` gives a translate `M⁻¹ C` meeting `Z` and each `W` properly
(`a3r_generic_translate`). These are the inputs of the family of translates
`a3m_family_components`.

Source: J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970* (1972), 89–96;
Fulton, *Intersection Theory*, second edition, Example 11.4.1; Kleiman, *The transversality of a
general translate* (1974). HC no distance; AV milestone no distance.
-/

noncomputable section

open MvPolynomial TensorProduct

namespace HodgeLean.Adapters

section Choice

variable {N n : ℕ}

/-- An implication with a decidable premise is generic when its conclusion is. -/
theorem a3r_generic_of_imp {ι : Type} (p : Prop) (P : (ι → ℂ) → Prop)
    (h : p → a3r_Generic {a | P a}) : a3r_Generic {a | p → P a} := by
  by_cases hp : p
  · exact (h hp).mono fun a ha _ => ha
  · exact a3r_generic_univ.mono fun a _ h => absurd h hp

/-- The relevant primes of `ℂ[x]/I` lying over a relevant prime containing `I`. -/
theorem a3r_map_mk_relevant (I 𝔶 : Ideal (MvPolynomial (Fin (N + 1)) ℂ)) [𝔶.IsPrime]
    (hI : I ≤ 𝔶) (j : Fin (N + 1)) (hj : X j ∉ 𝔶) :
    Ideal.Quotient.mk I (X j) ∉ 𝔶.map (Ideal.Quotient.mk I) := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, sup_eq_left.2 hI]
  exact hj

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- Roberts' construction in the homogeneous coordinate ring. Let `X = V(I_X) ⊂ ℙᴺ` have affine
cone of dimension `n + 1` and differentials of rank at most `n + 1` at its relevant points (`X`
smooth), let `Z = V(P_Z) ⊂ X` have cone of dimension `d + 1` with `d < n`, and let `Z ∩ W` have
excess at most `k + 1` for the finitely many `W = V(P_W)`. Then there are a cone `C = V(I_C)` with
linear vertex over `Z` and a matrix `M` such that
* `C` is a homogeneous prime of affine dimension `d + 1 + N - n` containing `Z`, and `C ∩ X` has
  affine dimension at most `d + 1` (the hypotheses of `a3m_family_components`);
* every component `Z' ≠ Z` of `C ∩ X` of the dimension of `Z` meets each `W` with excess at most
  `k` (Roberts' main lemma);
* the translate `M⁻¹ C` meets `Z` and each `W` properly (transversality of a general translate).
Source: J. Roberts, *Chow's moving lemma* (1972), Main Lemma and §2; Fulton, *Intersection
Theory*, second edition, Example 11.4.1. -/
theorem a3r_exists_cone_translate (IX PZ : Ideal (MvPolynomial (Fin (N + 1)) ℂ)) [IX.IsPrime]
    [PZ.IsPrime] (hPZ : PZ.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℂ))
    (hIX : IX.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℂ)) (hXZ : IX ≤ PZ)
    (hdimX : ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ IX) = (n + 1 : ℕ)) (d : ℕ)
    (hdimZ : ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ PZ) = (d + 1 : ℕ))
    (SW : Finset (Ideal (MvPolynomial (Fin (N + 1)) ℂ))) (hSW : ∀ W ∈ SW, W.IsPrime) (k : ℕ)
    (hexc : ∀ W ∈ SW, ∀ 𝔶 ∈ (PZ ⊔ W).minimalPrimes, (∃ j, X j ∉ 𝔶) →
      ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ 𝔶) +
          ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ IX) ≤
        ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ PZ) +
          ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ W) + (k + 1 : ℕ))
    (hsm : ∀ (𝔶 : Ideal (MvPolynomial (Fin (N + 1)) ℂ ⧸ IX)) [𝔶.IsPrime],
      (∃ j, Ideal.Quotient.mk IX (X j) ∉ 𝔶) →
      Module.finrank 𝔶.ResidueField
        (𝔶.ResidueField ⊗[MvPolynomial (Fin (N + 1)) ℂ ⧸ IX]
          Ω[MvPolynomial (Fin (N + 1)) ℂ ⧸ IX⁄ℂ]) ≤ n + 1) :
    ∃ (IC : Ideal (MvPolynomial (Fin (N + 1)) ℂ)) (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ),
      IC.IsPrime ∧ IC.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℂ) ∧ IC ≤ PZ ∧
      ((d + Fintype.card (Fin (N + 1)) : ℕ) : WithBot ℕ∞) =
        ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ IC) + n ∧
      (∀ P : Ideal (MvPolynomial (Fin (N + 1)) ℂ), P.IsPrime → IX ⊔ IC ≤ P →
        ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ P) ≤ (d + 1 : ℕ)) ∧
      (∀ Q' : Ideal (MvPolynomial (Fin (N + 1)) ℂ), Q'.IsPrime → IX ⊔ IC ≤ Q' →
        ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ Q') = (d + 1 : ℕ) → Q' ≠ PZ →
        ∀ W ∈ SW, ∀ Y : Ideal (MvPolynomial (Fin (N + 1)) ℂ), Y.IsPrime → Q' ⊔ W ≤ Y →
          (∃ j, X j ∉ Y) →
          ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ Y) +
              ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ IX) ≤
            ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ Q') +
              ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ W) + k) ∧
      (∀ W ∈ insert PZ SW, ∀ Q : Ideal (MvPolynomial (Fin (N + 1)) ℂ), Q.IsPrime → W ≤ Q →
        (∀ F ∈ IC, a3r_lin M F ∈ Q) → (∃ j, X j ∉ Q) →
        ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ Q) + Fintype.card (Fin (N + 1)) ≤
          ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ IC) +
            ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ W)) := by
  classical
  set B := MvPolynomial (Fin (N + 1)) ℂ
  set R := MvPolynomial (Fin (n + 1)) ℂ
  -- `n ≤ N`
  have hnN : n ≤ N := by
    have h1 := ringKrullDim_quotient_le IX
    rw [hdimX, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      ENat.card_eq_coe_fintype_card, Fintype.card_fin, zero_add] at h1
    have : ((n + 1 : ℕ) : ℕ∞) ≤ ((N + 1 : ℕ) : ℕ∞) := by exact_mod_cast h1
    have : n + 1 ≤ N + 1 := by exact_mod_cast this
    omega
  -- the generic projection
  set G : Set (Fin (n + 1) × Fin (N + 1) → ℂ) :=
    {a | ((Ideal.Quotient.mk IX).comp (a3r_lin (a3r_mat a)).toRingHom).Finite} ∩
    {a | IsUnit (a3r_ext (a3r_mat a)).det} ∩
    {a | ∀ W ∈ (SW : Set (Ideal B)), ∀ (j : Fin (N + 1))
      (𝔓 : Ideal ((B ⧸ W) ⊗[ℂ] (B ⧸ PZ))),
      𝔓.IsPrime → a3r_δD W PZ j ∉ 𝔓 →
      (∀ i, ∑ k, algebraMap ℂ _ (a3r_mat a i k) * a3r_δD W PZ k - 0 ∈ 𝔓) →
      ringKrullDim (_ ⧸ 𝔓) + Fintype.card (Fin (n + 1)) ≤ ringKrullDim ((B ⧸ W) ⊗[ℂ] (B ⧸ PZ))} ∩
    {a | ∀ W ∈ (SW : Set (Ideal B)), ∀ 𝔶 ∈ (PZ ⊔ W).minimalPrimes, (∃ j, X j ∉ 𝔶) →
      ((Ideal.Quotient.mk IX).comp (a3r_lin (a3r_mat a)).toRingHom).Finite → ∃ f ∉ 𝔶,
      letI : Algebra R (B ⧸ IX) := ((Ideal.Quotient.mk IX).comp (a3r_lin (a3r_mat a)).toRingHom).toAlgebra
      Algebra.FormallyUnramified R (Localization.Away (Ideal.Quotient.mk IX f))}
  have hG : a3r_Generic G := by
    refine (((a3r_generic_finite IX hIX hdimX).inter (a3r_generic_ext_det)).inter
      (a3r_generic_biInter _ SW.finite_toSet _ fun W hW => ?_)).inter
      (a3r_generic_biInter _ SW.finite_toSet _ fun W hW => ?_)
    · exact a3r_generic_secant W PZ
    · have := hSW W hW
      refine a3r_generic_biInter _ (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _) _
        fun 𝔶 h𝔶 => a3r_generic_of_imp _ _ fun hrel => ?_
      have h𝔶p : 𝔶.IsPrime := h𝔶.1.1
      have hX𝔶 : IX ≤ 𝔶 := hXZ.trans (le_sup_left.trans h𝔶.1.2)
      have : (𝔶.map (Ideal.Quotient.mk IX)).IsPrime := Ideal.map_isPrime_of_surjective
        Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
      obtain ⟨j, hj⟩ := hrel
      refine (a3r_generic_isUnramifiedAt (ρ := Fin (n + 1)) IX _
        ((hsm _ ⟨j, a3r_map_mk_relevant IX 𝔶 hX𝔶 j hj⟩).trans (by simp))).mono fun a ha hfin => ?_
      let _ : Algebra R (B ⧸ IX) :=
        ((Ideal.Quotient.mk IX).comp (a3r_lin (a3r_mat a)).toRingHom).toAlgebra
      have : Algebra.IsUnramifiedAt R (𝔶.map (Ideal.Quotient.mk IX)) := ha
      have : Module.Finite R (B ⧸ IX) := hfin
      have : Algebra.EssFiniteType R (B ⧸ IX) := Algebra.EssFiniteType.of_finiteType R _
      obtain ⟨f', hf', hunr⟩ :=
        Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := R) (𝔶.map (Ideal.Quotient.mk IX))
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f'
      exact ⟨f, fun h => hf' (Ideal.mem_map_of_mem _ h), hunr⟩
  obtain ⟨a, ⟨⟨⟨hfin, hdet⟩, hsec⟩, hunr⟩⟩ := hG.nonempty
  set ℓ := a3r_mat a
  have hℓ : (a3r_ext ℓ).submatrix (Fin.castLE (by omega : n + 1 ≤ N + 1)) id = ℓ :=
    a3r_ext_submatrix hnN ℓ
  have hcone := a3r_cone_isPrime (a3r_ext ℓ) hdet _
    (Fin.castLE_injective (by omega : n + 1 ≤ N + 1)) PZ
  rw [hℓ] at hcone
  obtain ⟨hICp, hICdim⟩ := hcone
  set IC := a3r_cone ℓ PZ
  set 𝔭 := PZ.comap (a3r_lin ℓ)
  have hdim𝔭 : ringKrullDim (R ⧸ 𝔭) = (d + 1 : ℕ) := by
    rw [← a3r_dim_eq_of_finite IX ℓ hfin PZ hXZ, hdimZ]
  have h𝔭le : ∀ P : Ideal B, IC ≤ P → 𝔭 ≤ P.comap (a3r_lin ℓ) :=
    fun P hP F hF => hP (Ideal.mem_map_of_mem _ hF)
  -- the general translate
  have hT : a3r_Generic {b : Fin (N + 1) × Fin (N + 1) → ℂ | ∀ W ∈ ((insert PZ SW : Finset _) :
      Set (Ideal B)), ∀ Q : Ideal B, Q.IsPrime → W ≤ Q →
      (∀ F ∈ IC, a3r_lin (a3r_mat b) F ∈ Q) → ∀ j, X j ∉ Q →
      ringKrullDim (B ⧸ Q) + Fintype.card (Fin (N + 1)) ≤
        ringKrullDim (B ⧸ IC) + ringKrullDim (B ⧸ W)} := by
    refine a3r_generic_biInter _ (Finset.finite_toSet _) _ fun W hW => ?_
    have : W.IsPrime := by
      rcases Finset.mem_insert.1 hW with rfl | hW
      · infer_instance
      · exact hSW W hW
    exact a3r_generic_translate IC W
  obtain ⟨b, hb⟩ := hT.nonempty
  refine ⟨IC, a3r_mat b, hICp, a3r_cone_isHomogeneous ℓ PZ hPZ, a3r_cone_le ℓ PZ, ?_, ?_, ?_, ?_⟩
  · rw [hICdim, hdim𝔭, Fintype.card_fin, Fintype.card_fin]
    have : d + (N + 1) = d + 1 + (N + 1 - (n + 1)) + n := by omega
    rw [this]
    push_cast
    rfl
  · intro P hP hle
    rw [a3r_dim_eq_of_finite IX ℓ hfin P (le_sup_left.trans hle), ← hdim𝔭]
    exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective (h𝔭le P (le_sup_right.trans hle)))
  · intro Q' hQ' hle hdQ hne W hW Y hY hWY hYrel
    have hXQ : IX ≤ Q' := le_sup_left.trans hle
    have hcomap : Q'.comap (a3r_lin ℓ) = 𝔭 := by
      refine le_antisymm ?_ (h𝔭le Q' (le_sup_right.trans hle))
      by_contra hlt'
      have hlt : 𝔭 < Q'.comap (a3r_lin ℓ) := lt_of_le_of_ne (h𝔭le Q' (le_sup_right.trans hle))
        (fun h => hlt' h.ge)
      have h1 := a3r_dim_add_one_le 𝔭 (Q'.comap (a3r_lin ℓ)) hlt
      rw [← a3r_dim_eq_of_finite IX ℓ hfin Q' hXQ, hdQ, hdim𝔭] at h1
      have : ((d + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h1
      have : d + 1 + 1 ≤ d + 1 := by exact_mod_cast this
      omega
    have hW' : W.IsPrime := hSW W hW
    have hmain := a3r_roberts_main IX PZ W hXZ ℓ (by rw [hdimX, Fintype.card_fin]) hfin
      (hsec W hW) (fun 𝔶 h𝔶 hrel => hunr W hW 𝔶 h𝔶 hrel hfin) k (hexc W hW) Q' hXQ hcomap hne
      Y hWY hYrel
    rwa [hdimZ, ← hdQ] at hmain
  · intro W hW Q hQ hWQ hCQ hrel
    obtain ⟨j, hj⟩ := hrel
    exact hb W (by simpa using hW) Q hQ hWQ hCQ j hj

end Choice

end HodgeLean.Adapters
