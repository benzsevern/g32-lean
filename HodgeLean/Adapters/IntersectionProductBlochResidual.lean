import HodgeLean.Adapters.IntersectionProductBlochAssembly
import HodgeLean.Adapters.IntersectionProductBlochRobertsPoints

/-! # The cone residuals of Bloch's translation operator

Stage A3.3. In Bloch's construction, the members of `[Y] - ∂_s Θ₁ ((π × id)_*[Y])` dominating
`ℙ¹_t` are of two kinds: the members of the general translate, which meet the faces of `β`
properly, and the other components of `(π × id)⁻¹ (π × id)(Y)`, the *cone residuals* of `Y`,
whose cone in `ℂ[x, t]` has the same image as that of `Y` under `ℓ × id`. Roberts' main lemma
over the line (`a3h_roberts_points`) bounds the excess of the residuals for a generic `ℓ`; this
file therefore weakens the excess clause of the translation operator to a clause on the members
other than the residuals (`a3h_BlochTranslationR`) and recovers the operators
(`a3h_generalTranslation_of_residual`).

Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994), §2;
J. Roberts, *Chow's moving lemma* (1972), Main Lemma. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Order
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] MvPolynomial.gradedAlgebra in
omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Points of `X × ℙ¹` dominating `ℙ¹` lie over `𝔸¹`. -/
theorem a3h_mem_U_of_dom (y : (a3n_T X).left) (hy : a3n_h X y = genericPoint (g3c_P 1)) :
    y ∈ a3h_U X := by
  rw [a3h_mem_U_iff', hy]
  have h := a3k_generic_mem_basicOpen
  rw [← Proj.opensRange_awayι _ _ (isHomogeneous_X _ (0 : Fin 2)) zero_lt_one] at h
  exact h

/-- The cone residuals of `y` for the projection `ℓ_a × id`: the other points of `X × 𝔸¹` whose
cone has the same image as that of `y`. -/
def a3h_Residual {n : ℕ} (a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ) (y y' : (a3n_T X).left) :
    Prop :=
  ∃ hy : y ∈ a3h_U X, ∃ hy' : y' ∈ a3h_U X,
    (a3h_P X y' hy').comap (a3r_lin (a3h_block a)) = (a3h_P X y hy).comap (a3r_lin (a3h_block a)) ∧
      y' ≠ y

variable {n : ℕ}

open Classical in
/-- **Bloch's translation operator for the projection `π_ℓ`, up to cone residuals**: as
`a3h_BlochTranslation`, except that the members of `[Y] - ∂_s (Θ₁ c)` dominating `ℙ¹_t` are
required to have excess at most `k` only when they are not cone residuals of `Y` for `ℓ × id`.
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994),
537–568, §2. -/
structure a3h_BlochTranslationR (a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ)
    (hfin : ((Ideal.Quotient.mk (a3s_IX X)).comp (a3r_lin (a3r_mat a)).toRingHom).Finite)
    (β : AlgebraicCycle X.left ℚ) (k : ℕ) (S : Finset (a3n_T X).left) where
  /-- The two-parameter chains. -/
  Θ₁ : AlgebraicCycle (a3n_T (a3h_PnO n)).left ℚ → AlgebraicCycle (a3n_T (a3n_T X)).left ℚ
  /-- The chains over a point. -/
  Θ₀ : AlgebraicCycle (a3h_PnO n).left ℚ → AlgebraicCycle (a3n_T X).left ℚ
  Θ₀_add : ∀ c c', Θ₀ (c + c') = Θ₀ c + Θ₀ c'
  Θ₀_smul : ∀ (r : ℚ) c, Θ₀ (a3m_smul r c) = a3m_smul r (Θ₀ c)
  face : ∀ y ∈ S, a3k_dt X (Θ₁ (a1p_pushforward (a3h_G (a3h_πO X hfin)).left
      (Function.locallyFinsuppWithin.single y 1))) =
    Θ₀ (a3k_bd (a3h_PnO n) (a1p_pushforward (a3h_G (a3h_πO X hfin)).left
      (Function.locallyFinsuppWithin.single y 1)))
  square : ∀ y ∈ S, ∀ w, Θ₁ (a1p_pushforward (a3h_G (a3h_πO X hfin)).left
      (Function.locallyFinsuppWithin.single y 1)) w ≠ 0 → a3k_SquarePos X w
  excess : ∀ y ∈ S, ∀ y', ((Function.locallyFinsuppWithin.single y 1 :
      AlgebraicCycle (a3n_T X).left ℚ) - a3k_bd (a3n_T X) (Θ₁ (a1p_pushforward
        (a3h_G (a3h_πO X hfin)).left (Function.locallyFinsuppWithin.single y 1)))) y' ≠ 0 →
      a3n_h X y' = genericPoint (g3c_P 1) → ¬ a3h_Residual X a y y' → a3k_ExcessLE X β y' k
  good : ∀ D : X.left, (∃ y ∈ S, a3k_piece X y D ≠ 0) →
      (∀ v, β v ≠ 0 → a3i_MeetProperly X.left D v) →
      ∀ y', Θ₀ (a1p_pushforward (a3h_πO X hfin).left (Function.locallyFinsuppWithin.single D 1))
        y' ≠ 0 → ∀ hy' : a3n_h X y' = genericPoint (g3c_P 1), a3o_Good X β y' hy'

variable {X}

/-- A translation operator up to cone residuals is a translation operator once the residuals of
the members have excess at most `k`. -/
def a3h_BlochTranslationR.toTranslation {a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ}
    {hfin : ((Ideal.Quotient.mk (a3s_IX X)).comp (a3r_lin (a3r_mat a)).toRingHom).Finite}
    {β : AlgebraicCycle X.left ℚ} {k : ℕ} {S : Finset (a3n_T X).left}
    (Θ : a3h_BlochTranslationR X a hfin β k S)
    (hR : ∀ y ∈ S, ∀ y', a3h_Residual X a y y' → a3k_ExcessLE X β y' k) :
    a3h_BlochTranslation X (a3h_πO X hfin) β k S where
  Θ₁ := Θ.Θ₁
  Θ₀ := Θ.Θ₀
  Θ₀_add := Θ.Θ₀_add
  Θ₀_smul := Θ.Θ₀_smul
  face := Θ.face
  square := Θ.square
  excess y hy y' h1 h2 := by
    by_cases hres : a3h_Residual X a y y'
    · exact hR y hy y' hres
    · exact Θ.excess y hy y' h1 h2 hres
  good := Θ.good

variable (X)

/-- Translation operators up to cone residuals exist for a general projection: for the members
`S` of excess at most `k + 1` against `β`, dominating `ℙ¹`, for a generic linear projection `ℓ`
of `X ⊂ ℙᴺ` to `ℙⁿ`, `n = dim X`, finite on `X`, there is a translation operator for `π_ℓ` up to
the cone residuals of `ℓ × id`.
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994),
537–568, §2. -/
def a3h_GeneralTranslationR : Prop :=
  ∀ (β : AlgebraicCycle X.left ℚ) (k : ℕ) (S : Finset (a3n_T X).left),
    (∀ y ∈ S, a3n_h X y = genericPoint (g3c_P 1) ∧ a3k_ExcessLE X β y (k + 1)) →
    ∀ (n : ℕ), Order.height (genericPoint X.left) = n →
      a3r_Generic {a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ |
        ∀ hfin : ((Ideal.Quotient.mk (a3s_IX X)).comp (a3r_lin (a3r_mat a)).toRingHom).Finite,
          Nonempty (a3h_BlochTranslationR X a hfin β k S)}

/-- **Translation operators from translation operators up to cone residuals**: for a generic `ℓ`,
Roberts' main lemma over the line (`a3h_roberts_points`) bounds the excess of the cone residuals
of every member by `k`.
Source: J. Roberts, *Chow's moving lemma* (1972), Main Lemma; S. Bloch, *The moving lemma for
higher Chow groups*, J. Algebraic Geom. 3 (1994), §2. -/
theorem a3h_generalTranslation_of_residual (H : a3h_GeneralTranslationR X) :
    a3h_GeneralTranslation X := by
  intro β k S hS n hn
  have hRob := a3r_generic_biInter (S : Set (a3n_T X).left) S.finite_toSet
    (fun y => {a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ | ∀ hy : y ∈ a3h_U X,
      ∀ y' (hy' : y' ∈ a3h_U X), (a3h_P X y' hy').comap (a3r_lin (a3h_block a)) =
        (a3h_P X y hy).comap (a3r_lin (a3h_block a)) → y' ≠ y → a3k_ExcessLE X β y' k})
    (fun y hy => by
      obtain ⟨hdom, hexc⟩ := hS y hy
      refine (a3h_roberts_points X n hn β y (a3h_mem_U_of_dom X y hdom)
        (hdom ▸ a3k_generic_not_mem_Z0) (hdom ▸ a3k_generic_not_mem_Zinf) k hexc).mono ?_
      intro a ha hy' y' hy'' hc hne
      exact ha.2 y' hy'' hc hne)
  refine ((H β k S hS n hn).inter hRob).mono ?_
  rintro a ⟨hΘ, hR⟩ hfin
  refine ⟨(hΘ hfin).some.toTranslation fun y hy y' ⟨hyU, hy'U, hc, hne⟩ => ?_⟩
  exact hR y hy hyU y' hy'U hc hne

end HodgeLean.Adapters
