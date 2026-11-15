import HodgeLean.Adapters.IntersectionProductBlochPush
import HodgeLean.Adapters.IntersectionProductBlochProjection

/-! # Bloch's homotopy operators from a finite projection and a translation operator

Stage A3.3, the assembly of Bloch's homotopy operators (`a3k_BlochOperators`) as in Bloch (1994),
§2. A finite projection `π : X → ℙⁿ` (`a3h_π`, projective Noether normalization) pushes a member
`Y ⊆ X × ℙ¹_t` of the chain forward to `(π × id)_*[Y]` on `ℙⁿ × ℙ¹_t`; a translation operator
`Θ` turns cycles on `ℙⁿ × ℙ¹_t` into two-parameter chains on `(X × ℙ¹_t) × ℙ¹_s` (`Θ₁`, in
Bloch's construction the pull-back along `π × id × id` of the family of translates over `ℙ¹_s`)
and cycles on `ℙⁿ` into chains on `X × ℙ¹_s` (`Θ₀`, the same for a point), compatibly with the
faces `t = a`. The operators are
* `H y = Θ₁ ((π × id)_*[Y])`, `h D = Θ₀ (π_*[D])`,
and the relation `∂_t (H y) = h(∂ y)` (`a3k_BlochOperators`) is the face compatibility of `Θ`
followed by `π_* ∂ = ∂ (π × id)_*` (`a3h_push_bd`) and the linearity of `Θ₀`
(`a3h_blochOperators_of_translation`).

The translation operator for a general projection is `a3h_BlochTranslation`: its fields are
the face compatibility, the square position of the members of `H y`, the excess of
`[Y] - ∂_s H y` (Roberts' main lemma over the line, `a3h_roberts_rel`, for the residual of the
cone `(π × id)^*(π × id)_*[Y] = [Y] + R`, and Kleiman's transversality over the line,
`a3h_generic_line`, for the general translate) and the good position of `h D` for faces `D`
meeting `β` properly.

Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994),
537–568, §2; J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970* (1972),
89–96; Kleiman, *The transversality of a general translate*, Compositio Math. 28 (1974).
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
open scoped MonoidalCategory

namespace HodgeLean.Adapters

/-! ## Projective space over `ℂ` and the projection as a morphism over `ℂ` -/

section projective

/-- `ℙⁿ_ℂ` over `Spec ℂ`. -/
abbrev a3h_PnO (n : ℕ) : Over (Spec ↧ℂ) := Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))

instance a3h_PnO_proper (n : ℕ) : IsProper (a3h_PnO n).hom :=
  ProjectiveSpace.toBaseProper (Fin (n + 1)) (Spec ↧ℂ)

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom] {n : ℕ}
  {ℓ : Matrix (Fin (n + 1)) (Fin (a3s_N X + 1)) ℂ}
  (hfin : ((Ideal.Quotient.mk (a3s_IX X)).comp (a3r_lin ℓ).toRingHom).Finite)

/-- The projection `π_ℓ` as a morphism over `ℂ`. -/
def a3h_πO : X ⟶ a3h_PnO n := Over.homMk (a3h_π X hfin) (a3h_π_fst X hfin)

instance a3h_πO_finite : IsFinite (a3h_πO X hfin).left := a3h_π_isFinite X hfin

end projective

/-! ## The translation operator and the operators `H`, `h` -/

section operators

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {n : ℕ}
  (π : X ⟶ a3h_PnO n) [IsProper π.left]

open Classical in
/-- **Bloch's translation operator for a finite projection `π`**, for the members `S` of excess
at most `k + 1` against `β`: a two-parameter chain `Θ₁ c` on `(X × ℙ¹_t) × ℙ¹_s` for each cycle
`c` on `ℙⁿ × ℙ¹_t`, and a chain `Θ₀ c` on `X × ℙ¹_s` for each cycle `c` on `ℙⁿ`, `Θ₀` linear,
such that for `c = (π × id)_*[Y]`, `Y ∈ S`,
* `∂_t (Θ₁ c) = Θ₀ (∂ c)` (the faces `t = a`);
* the members of `Θ₁ c` are in square position;
* the members of `[Y] - ∂_s (Θ₁ c)` dominating `ℙ¹_t` have excess at most `k`;
and `Θ₀ (π_*[D])` is in good position with respect to `β` for every face component `D` of the
members of `S` meeting `β` properly.
In Bloch's construction `Θ₁ c` is the pull-back along `π × id × id` of the family over `ℙ¹_s`
of the translates `h_s⁻¹ c` by `h_s = (1 - s) + s M`, `M` general, and `Θ₀` the same over a
point: then `∂_s (Θ₁ (π × id)_*[Y]) = (π × id)^*(π × id)_*[Y] - (π × id)^* M⁻¹ (π × id)_*[Y]`, the
first term is `[Y]` plus components of smaller excess (Roberts' main lemma over the line,
`a3h_roberts_rel`) and the second meets everything properly (`a3h_generic_translate_rel`); the
family meets `V × ℙ¹_s` properly over all `s ≠ 0` (`a3h_generic_line`).
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994),
537–568, §2; J. Roberts, *Chow's moving lemma* (1972), Main Lemma; Kleiman, *The
transversality of a general translate*, Compositio Math. 28 (1974), Theorem 2. -/
structure a3h_BlochTranslation (β : AlgebraicCycle X.left ℚ) (k : ℕ)
    (S : Finset (a3n_T X).left) where
  /-- The two-parameter chains. -/
  Θ₁ : AlgebraicCycle (a3n_T (a3h_PnO n)).left ℚ → AlgebraicCycle (a3n_T (a3n_T X)).left ℚ
  /-- The chains over a point. -/
  Θ₀ : AlgebraicCycle (a3h_PnO n).left ℚ → AlgebraicCycle (a3n_T X).left ℚ
  Θ₀_add : ∀ c c', Θ₀ (c + c') = Θ₀ c + Θ₀ c'
  Θ₀_smul : ∀ (r : ℚ) c, Θ₀ (a3m_smul r c) = a3m_smul r (Θ₀ c)
  face : ∀ y ∈ S, a3k_dt X (Θ₁ (a1p_pushforward (a3h_G π).left
      (Function.locallyFinsuppWithin.single y 1))) =
    Θ₀ (a3k_bd (a3h_PnO n) (a1p_pushforward (a3h_G π).left
      (Function.locallyFinsuppWithin.single y 1)))
  square : ∀ y ∈ S, ∀ w, Θ₁ (a1p_pushforward (a3h_G π).left
      (Function.locallyFinsuppWithin.single y 1)) w ≠ 0 → a3k_SquarePos X w
  excess : ∀ y ∈ S, ∀ y', ((Function.locallyFinsuppWithin.single y 1 :
      AlgebraicCycle (a3n_T X).left ℚ) - a3k_bd (a3n_T X) (Θ₁ (a1p_pushforward (a3h_G π).left
        (Function.locallyFinsuppWithin.single y 1)))) y' ≠ 0 →
      a3n_h X y' = genericPoint (g3c_P 1) → a3k_ExcessLE X β y' k
  good : ∀ D : X.left, (∃ y ∈ S, a3k_piece X y D ≠ 0) →
      (∀ v, β v ≠ 0 → a3i_MeetProperly X.left D v) →
      ∀ y', Θ₀ (a1p_pushforward π.left (Function.locallyFinsuppWithin.single D 1)) y' ≠ 0 →
        ∀ hy' : a3n_h X y' = genericPoint (g3c_P 1), a3o_Good X β y' hy'

variable {X π}

theorem a3h_Θ₀_zero {β : AlgebraicCycle X.left ℚ} {k : ℕ} {S : Finset (a3n_T X).left}
    (Θ : a3h_BlochTranslation X π β k S) : Θ.Θ₀ 0 = 0 := by
  have h := Θ.Θ₀_add 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem a3h_Θ₀_sum {β : AlgebraicCycle X.left ℚ} {k : ℕ} {S : Finset (a3n_T X).left}
    (Θ : a3h_BlochTranslation X π β k S) {ι : Type*} (s : Finset ι)
    (F : ι → AlgebraicCycle (a3h_PnO n).left ℚ) :
    Θ.Θ₀ (∑ i ∈ s, F i) = ∑ i ∈ s, Θ.Θ₀ (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using a3h_Θ₀_zero Θ
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Θ.Θ₀_add, ih]

open Classical in
/-- `Θ₀ ∘ π_*` is the linear extension of its values on points. -/
theorem a3h_Θ₀_push {β : AlgebraicCycle X.left ℚ} {k : ℕ} {S : Finset (a3n_T X).left}
    (Θ : a3h_BlochTranslation X π β k S) (c : AlgebraicCycle X.left ℚ) :
    Θ.Θ₀ (a1p_pushforward π.left c) = a3k_lin (fun D => Θ.Θ₀ (a1p_pushforward π.left
      (Function.locallyFinsuppWithin.single D 1))) c := by
  set s := (a3m_support_finite c).toFinset
  have hs : ∀ y ∉ s, c y = 0 := fun y hy => by simpa [s] using hy
  conv_lhs => rw [a3m_eq_sum_single c s hs]
  rw [a3k_pushforward_sum, a3h_Θ₀_sum, a3k_lin_eq_sum _ c s hs]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [a3k_pushforward_smul, Θ.Θ₀_smul]

open Classical in
/-- **Bloch's homotopy operators from a translation operator**: `H y = Θ₁ ((π × id)_*[Y])` and
`h D = Θ₀ (π_*[D])`. The relation `∂_t (H y) = h(∂ y)` is the face compatibility of `Θ`, then
`∂ (π × id)_* = π_* ∂` (`a3h_push_bd`) and the linearity of `Θ₀ ∘ π_*`.
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994),
537–568, §2. -/
theorem a3h_blochOperators_of_translation {β : AlgebraicCycle X.left ℚ} {k : ℕ}
    {S : Finset (a3n_T X).left} (Θ : a3h_BlochTranslation X π β k S) :
    a3k_BlochOperators X β k S := by
  refine ⟨fun y => Θ.Θ₁ (a1p_pushforward (a3h_G π).left
      (Function.locallyFinsuppWithin.single y 1)),
    fun D => Θ.Θ₀ (a1p_pushforward π.left (Function.locallyFinsuppWithin.single D 1)),
    fun y hy w hw => Θ.square y hy w hw, fun y hy => ?_, fun y hy y' h1 h2 => Θ.excess y hy y' h1 h2,
    fun D hD hDp y' h1 h2 => Θ.good D hD hDp y' h1 h2⟩
  rw [Θ.face y hy, ← a3h_push_bd π, a3k_bd_single, a3h_Θ₀_push]

end operators

/-! ## The homotopy operators from translation operators for general projections -/

section general

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Translation operators exist for a general projection: for the members `S` of excess at most
`k + 1` against `β`, for a generic linear projection `ℓ` of `X ⊂ ℙᴺ` to `ℙⁿ`, `n = dim X`,
finite on `X`, there is a translation operator for `π_ℓ`.
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994),
537–568, §2. -/
def a3h_GeneralTranslation : Prop :=
  ∀ (β : AlgebraicCycle X.left ℚ) (k : ℕ) (S : Finset (a3n_T X).left),
    (∀ y ∈ S, a3n_h X y = genericPoint (g3c_P 1) ∧ a3k_ExcessLE X β y (k + 1)) →
    ∀ (n : ℕ), Order.height (genericPoint X.left) = n →
      a3r_Generic {a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ |
        ∀ hfin : ((Ideal.Quotient.mk (a3s_IX X)).comp (a3r_lin (a3r_mat a)).toRingHom).Finite,
          Nonempty (a3h_BlochTranslation X (a3h_πO X hfin) β k S)}

/-- **Bloch's homotopy operators**, from translation operators for a general projection: a
generic `ℓ` is finite on `X` (`a3r_generic_finite`) and has a translation operator, which gives
the operators (`a3h_blochOperators_of_translation`).
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994),
537–568, §2. -/
theorem a3h_homotopyOperators_of_translation (H : a3h_GeneralTranslation X) :
    a3k_HomotopyOperators X := by
  intro β k S hS
  obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg (X := X) (genericPoint X.left)
  obtain ⟨a, hfin, hΘ⟩ := ((a3r_generic_finite (a3s_IX X) (a3s_IX_isHomogeneous X)
    (a3h_dim_cone X n hn)).inter (H β k S hS n hn)).nonempty
  exact a3h_blochOperators_of_translation (hΘ hfin).some

end general

end HodgeLean.Adapters
