import HodgeLean.Foundations.Analytic.AnalytificationChowProjective

/-! # Chow's lemma, stage F4g-C1: finite products of projective spaces

`ℙⁿ_Y ⟶ Y` is projective, so is `𝟙 Y` (through `ℙ⁰_Y ≅ Y`), and for finitely many `nᵢ` the
fibre product `P = ∏_Y ℙ^{nᵢ}_Y` is projective over `Y`, with projections `pᵢ` and the universal
property of the product (`AnalytificationChow3_exists_product`), by induction from the fibre
product lemma `AnalytificationChow_isProjective_pullback` (the Segre embedding).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace

namespace HodgeLean.Foundations.Analytic

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `ℙⁿ_Y ⟶ Y` is projective: the identity is a presentation.
Source: Hartshorne, *Algebraic Geometry*, §II.4 (definition of projective morphism). -/
theorem AnalytificationChow3_isProjective_toBase (n : ℕ) (Y : Scheme.{0}) :
    IsProjective (toBase (Fin (n + 1)) Y) :=
  ⟨⟨{ ambientDimension := n, immersion := 𝟙 _, immersion_toBase := Category.id_comp _ }⟩⟩

example : IsProjective (toBase (Fin 1) (Spec (CommRingCat.of ℤ))) :=
  AnalytificationChow3_isProjective_toBase 0 _

/-- `𝟙 Y` is projective: `ℙ⁰_Y ⟶ Y` is an isomorphism (`ℙ⁰_ℤ` is terminal), and its inverse is a
presentation.
Source: Hartshorne, *Algebraic Geometry*, §II.7 (`ℙ⁰`); `spec_g3c_isIso_terminal_from_P_zero`. -/
theorem AnalytificationChow3_isProjective_id (Y : Scheme.{0}) : IsProjective (𝟙 Y) := by
  have : IsIso (terminal.from (Proj (MvPolynomial.homogeneousSubmodule (Fin (0 + 1))
      (ULift.{0} ℤ)))) :=
    HodgeLean.Foundations.spec_g3c_isIso_terminal_from_P_zero
  have : IsIso (toBase (Fin (0 + 1)) Y) :=
    inferInstanceAs (IsIso (pullback.fst (terminal.from Y) (terminal.from (Proj
      (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) (ULift.{0} ℤ))))))
  let P : Presentation (𝟙 Y) :=
    { ambientDimension := 0
      immersion := CategoryTheory.inv (toBase (Fin (0 + 1)) Y)
      immersion_toBase := IsIso.inv_hom_id _ }
  exact ⟨⟨P⟩⟩

example : IsProjective (𝟙 (Spec (CommRingCat.of ℤ))) := AnalytificationChow3_isProjective_id _

/-- **Finite fibre products of projective spaces.** For `n : Fin k → ℕ` there is a projective
`s : P ⟶ Y` with maps `pᵢ : P ⟶ ℙ^{nᵢ}_Y` over `Y` such that any family of `Y`-morphisms
`T ⟶ ℙ^{nᵢ}_Y` factors through `P`.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.4.9 and II.5.11 (products of projective
morphisms, the Segre embedding); `AnalytificationChow_isProjective_pullback`. -/
theorem AnalytificationChow3_exists_product (Y : Scheme.{0}) : ∀ (k : ℕ) (n : Fin k → ℕ),
    ∃ (P : Scheme.{0}) (s : P ⟶ Y) (p : ∀ i, P ⟶ ℙ(Fin (n i + 1); Y)),
      IsProjective s ∧ (∀ i, p i ≫ toBase (Fin (n i + 1)) Y = s) ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ Y) (φ : ∀ i, T ⟶ ℙ(Fin (n i + 1); Y)),
        (∀ i, φ i ≫ toBase (Fin (n i + 1)) Y = t) →
          ∃ ψ : T ⟶ P, ψ ≫ s = t ∧ ∀ i, ψ ≫ p i = φ i
  | 0, _ => ⟨Y, 𝟙 Y, fun i ↦ i.elim0, AnalytificationChow3_isProjective_id Y, fun i ↦ i.elim0,
      fun _ t _ _ ↦ ⟨t, Category.comp_id _, fun i ↦ i.elim0⟩⟩
  | k + 1, n => by
    obtain ⟨P, s, p, hs, hp, hP⟩ := AnalytificationChow3_exists_product Y k (fun i ↦ n i.succ)
    have := AnalytificationChow3_isProjective_toBase (n 0) Y
    let P' := pullback s (toBase (Fin (n 0 + 1)) Y)
    let p' : ∀ i, P' ⟶ ℙ(Fin (n i + 1); Y) := fun i ↦
      Fin.cases (motive := fun i ↦ P' ⟶ ℙ(Fin (n i + 1); Y)) (pullback.snd _ _)
        (fun i ↦ pullback.fst _ _ ≫ p i) i
    refine ⟨P', pullback.fst _ _ ≫ s, p', AnalytificationChow_isProjective_pullback s _, ?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simp [p', pullback.condition]
      | succ i => simp [p', hp]
    · intro T t φ hφ
      obtain ⟨ψ, hψs, hψp⟩ := hP T t (fun i ↦ φ i.succ) (fun i ↦ hφ i.succ)
      refine ⟨pullback.lift ψ (φ 0) (by rw [hψs, hφ 0]), by simp [hψs], fun i ↦ ?_⟩
      induction i using Fin.cases with
      | zero => simp [p']
      | succ i => simp [p', hψp]

end HodgeLean.Foundations.Analytic
