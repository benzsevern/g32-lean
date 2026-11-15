import HodgeLean.Adapters.IntersectionProductMovingRobertsRank

/-! # Chow's moving lemma: Roberts' construction

Stage A3.2 of track A3, the existence of a moving family (`a3m_exists_movingFamily`) and with it
Roberts' step and the moving lemma. Roberts' construction is split into the following sub-steps,
each a lemma below; the proofs are in the `IntersectionProductMovingRoberts*` files.

1. A general linear projection is finite (`a3m_roberts_projection`): for `X ⊂ ℙᴺ` with affine cone
   of dimension `n + 1`, a generic centre `L = V(ℓ_0, …, ℓ_n)` misses `X`, so
   `ℂ[x]/I_X` is finite over `ℂ[ℓ]`. Generic centres are the non-vanishing locus of a nonzero
   polynomial in the coefficients of `ℓ` (an affine chart of matrices).
2. Roberts' main lemma (`a3m_roberts_mainLemma`): for a finite projection with generic secants that
   is unramified at the components of `Z ∩ W`, every component `Z' ≠ Z` of `C_L(Z) ∩ X` meets `W`
   with excess at most `max (e - 1) 0`. Generic secants and generic unramifiedness are dimension
   counts (`a3r_generic_secant`, `a3r_generic_isUnramifiedAt`).
3. A general translate (`a3m_roberts_translate`): for a generic matrix `M`, `M⁻¹(C)` meets each
   `W` properly; this is Kleiman's dimension count for matrices acting on `𝔸^{N+1}`.
4. The family (`a3m_roberts_family`): `t ↦ h_t⁻¹(C)` over `ℙ¹`, met with `X × ℙ¹`, gives the
   fields of `a3m_MovingFamily`, given the rank condition on the differentials of the affine cone
   over `X`.
5. The rank condition (`a3m_roberts_rank`): at every relevant point of the affine cone over a
   smooth `X` of dimension `n`, the Kähler differentials have rank at most `n + 1`.

Source: J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970*, Wolters-Noordhoff
(1972), 89–96; Fulton, *Intersection Theory*, second edition, §11.4 and Example 11.4.1; Kleiman,
*The transversality of a general translate*, Compositio Math. 28 (1974).
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial TensorProduct

namespace HodgeLean.Adapters

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## The sub-steps -/

/-- Step 1: a generic linear projection of `X ⊂ ℙᴺ` to `ℙⁿ`, `n + 1` the dimension of the affine
cone over `X`, is finite.
Source: Shafarevich, *Basic Algebraic Geometry 1*, I.5.3, Theorem 1.15; J. Roberts, *Chow's moving
lemma* (1972), §1. -/
theorem a3m_roberts_projection {σ : Type} [Fintype σ] {n : ℕ} (I : Ideal (MvPolynomial σ ℂ))
    [I.IsPrime] (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ))
    (hdim : ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (n + 1 : ℕ)) :
    a3r_Generic {a : Fin (n + 1) × σ → ℂ |
      ((Ideal.Quotient.mk I).comp (a3r_lin (a3r_mat a)).toRingHom).Finite} :=
  a3r_generic_finite I hI hdim

/-- Step 2: Roberts' main lemma, for a finite projection with generic secants that is unramified
at the components of `Z ∩ W`.
Source: J. Roberts, *Chow's moving lemma* (1972), Main Lemma; Fulton, *Intersection Theory*,
second edition, Example 11.4.1. -/
theorem a3m_roberts_mainLemma {ρ σ : Type} [Fintype ρ] [Fintype σ]
    (IX PZ PW : Ideal (MvPolynomial σ ℂ)) [IX.IsPrime] [PZ.IsPrime]
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
      ringKrullDim (MvPolynomial σ ℂ ⧸ PZ) + ringKrullDim (MvPolynomial σ ℂ ⧸ PW) + k :=
  a3r_roberts_main IX PZ PW hXZ ℓ hdimX hfin hsec hunr k hexc Q' hXQ hQ hne Y hY hYrel

/-- Step 3: a general translate of a cone meets a subvariety properly.
Source: Kleiman, *The transversality of a general translate*, Compositio Math. 28 (1974),
Theorem 2. -/
theorem a3m_roberts_translate {σ : Type} [Fintype σ] [DecidableEq σ]
    (IC PW : Ideal (MvPolynomial σ ℂ)) [IC.IsPrime] [PW.IsPrime] :
    a3r_Generic {a : σ × σ → ℂ | ∀ Q : Ideal (MvPolynomial σ ℂ), Q.IsPrime → PW ≤ Q →
      (∀ F ∈ IC, a3r_lin (a3r_mat a) F ∈ Q) → ∀ j, X j ∉ Q →
      ringKrullDim (MvPolynomial σ ℂ ⧸ Q) + Fintype.card σ ≤
        ringKrullDim (MvPolynomial σ ℂ ⧸ IC) + ringKrullDim (MvPolynomial σ ℂ ⧸ PW)} :=
  a3r_generic_translate IC PW

/-- Step 4: Roberts' moving family, given the rank condition on the differentials of the affine
cone over `X`.
Source: J. Roberts, *Chow's moving lemma* (1972), §2; Fulton, *Intersection Theory*, second
edition, §1.6 and Example 11.4.1. -/
theorem a3m_roberts_family (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom] (n : ℕ)
    (hn : Order.height (genericPoint X.left) = n)
    (hsm : ∀ (𝔶 : Ideal (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X)) [𝔶.IsPrime],
      (∃ j, Ideal.Quotient.mk (a3s_IX X) (MvPolynomial.X j) ∉ 𝔶) →
      Module.finrank 𝔶.ResidueField
        (𝔶.ResidueField ⊗[MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X]
          Ω[MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X⁄ℂ]) ≤ n + 1)
    (S : Set X.left) (hS : S.Finite) (p k d : ℕ) (hp : 0 < p) (u : X.left)
    (hu : Order.coheight u = p) (hd : Order.height u = d)
    (he : a3m_ExcessLE X.left S u (k + 1)) :
    Nonempty (a3m_MovingFamily X S p k d u) :=
  a3s_movingFamily_of_rank X n hn hsm S hS p k d hp u hu hd he

/-- Step 5: on the affine cone over a smooth projective variety of dimension `n`, the Kähler
differentials have rank at most `n + 1` at every point other than the vertex.
Source: Hartshorne, *Algebraic Geometry*, II, Theorem 8.15 and Exercise 8.4 (the cone over a
smooth projective variety is smooth away from the vertex); Stacks Project, Tag 00TT. -/
theorem a3m_roberts_rank (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (n : ℕ) (hn : Order.height (genericPoint X.left) = n)
    (𝔶 : Ideal (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X)) [𝔶.IsPrime]
    (hrel : ∃ j, Ideal.Quotient.mk (a3s_IX X) (MvPolynomial.X j) ∉ 𝔶) :
    Module.finrank 𝔶.ResidueField
      (𝔶.ResidueField ⊗[MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X]
        Ω[MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X⁄ℂ]) ≤ n + 1 :=
  a3t_rank X n hn 𝔶 hrel

/-! ## Roberts' step and the moving lemma -/

/-- The existence of a moving family for a subvariety of positive codimension: Roberts'
construction. For an embedding `X ⊂ ℙᴺ`, a general linear centre `L` of codimension `dim X + 1`
gives the cone `C = C_L(closure {u})`, and a general matrix `M` the translate `M⁻¹ C`. With
`T = X × ℙ¹` and the family `t ↦ h_t⁻¹(C)`, `h_t = (1 - t) + t M`, the member `closure {y}` is the
component of the family met with `X × ℙ¹` through `closure {u} × {0}`: its fibre over `0` lies in
`C ∩ X = π_L⁻¹(π_L(closure {u}))`, whose components other than `closure {u}` have excess at most
`max (e - 1) 0` (Roberts' main lemma), and its fibre over `1` lies in `M⁻¹(C) ∩ X`, which meets
every member of `S` properly and does not contain `closure {u}` (transversality of a general
translate).
Source: J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970* (1972), 89–96,
Main Lemma and §2; Fulton, *Intersection Theory*, second edition, Example 11.4.1; Kleiman,
*The transversality of a general translate*, Compositio Math. 28 (1974), Theorem 2. -/
theorem a3m_exists_movingFamily (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (S : Set X.left) (hS : S.Finite) (p k d : ℕ) (hp : 0 < p) (u : X.left)
    (hu : Order.coheight u = p) (hd : Order.height u = d)
    (he : a3m_ExcessLE X.left S u (k + 1)) :
    Nonempty (a3m_MovingFamily X S p k d u) := by
  obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg (X := X) (genericPoint X.left)
  exact a3m_roberts_family X n hn (fun 𝔶 _ hrel => a3m_roberts_rank X n hn 𝔶 hrel) S hS p k d hp u
    hu hd he

/-- Roberts' step: on a smooth projective variety, a subvariety of codimension `p` whose excess
against finitely many subvarieties is at most `k + 1` is rationally equivalent to a cycle of
codimension `p` whose components have excess at most `k`.
Source: J. Roberts, *Chow's moving lemma* (1972), Main Lemma (the cone `C_L(V)` with a general
linear vertex `L`, and `C_L(V) · X = V + residual`); Fulton, *Intersection Theory*, second
edition, Example 11.4.1. -/
theorem a3m_roberts_step (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (S : Set X.left) (hS : S.Finite) (p k : ℕ) (u : X.left)
    (hu : Order.coheight u = p) (he : a3m_ExcessLE X.left S u (k + 1)) :
    a3m_Movable X.left S p k u := by
  classical
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · refine ⟨Function.locallyFinsuppWithin.single u 1,
      a3m_single_mem_codimCycles X.left 0 u hu, ?_, ?_⟩
    · convert (a3i_ratAll X.left).zero_mem using 1
      exact sub_self _
    · intro x hx
      rw [Function.locallyFinsuppWithin.single_apply] at hx
      split_ifs at hx with h
      · subst h
        exact a3m_excessLE_mono (Nat.zero_le k)
          (a3m_excessLE_zero_of_coheight_eq_zero S x (by exact_mod_cast hu))
      · exact (hx rfl).elim
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, Order.height u = d := by
      obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg (X := X) u
      exact ⟨n, hn⟩
    exact a3m_movable_of_family X S p k d u hd
      (a3m_exists_movingFamily X S hS p k d hp u hu hd he).some

/-- Chow's moving lemma on a smooth projective variety.
Source: Fulton, *Intersection Theory*, second edition, §11.4; J. Roberts, *Chow's moving lemma*
(1972). -/
theorem a3m_moving (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ) (α β : AlgebraicCycle X.left ℚ)
    (hα : α ∈ a3i_codimCycles X.left ℚ p) :
    ∃ α' ∈ a3i_codimCycles X.left ℚ p, α' - α ∈ a3i_ratAll X.left ∧
      a3i_CyclesMeetProperly X.left α' β :=
  a3m_moving_of_step X.left p (a3m_coheight_component_le_of_smooth X)
    (fun S hS k u hu he => a3m_roberts_step X S hS p k u hu he) α β hα

end HodgeLean.Adapters
