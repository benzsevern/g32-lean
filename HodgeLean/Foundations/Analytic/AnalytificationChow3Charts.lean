import HodgeLean.Foundations.Analytic.AnalytificationChow3Graph
import HodgeLean.Foundations.SegreProjectiveProofs
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Chow's lemma, stage F4g-C2: affine charts as immersions into projective space

An affine open `U` of a scheme of finite type over an affine `S` is a closed subscheme of some
`𝔸ⁿ_S` (`AnalytificationChow3_exists_isClosedImmersion_homOfVector`); the standard chart
`𝔸ⁿ_Y ⟶ ℙⁿ_Y`, `x_0 ↦ 1`, is an immersion (`AnalytificationChow3_isImmersion_affineToProj`);
so for `X ⟶ Y` over `S` there is an immersion `U ⟶ ℙⁿ_Y` over `Y`
(`AnalytificationChow3_exists_immersion`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial ProjectiveSpace

namespace HodgeLean.Foundations.Analytic

set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **An affine scheme of finite type over an affine `S` is closed in some `𝔸ⁿ_S`**: finitely many
generators `v` of `Γ(U)` over `Γ(S)` give a morphism `U ⟶ 𝔸ⁿ_S` surjective on global sections.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.3.11 (closed subschemes of `Spec`), §II.3
(finite type); Mathlib `AffineSpace.homOfVector`, `IsClosedImmersion.of_surjective_of_isAffine`. -/
theorem AnalytificationChow3_exists_isClosedImmersion_homOfVector {U S : Scheme.{0}} [IsAffine U]
    [IsAffine S] (σ : U ⟶ S) [LocallyOfFiniteType σ] :
    ∃ (n : ℕ) (v : Fin n → Γ(U, ⊤)), IsClosedImmersion (AffineSpace.homOfVector σ v) := by
  have hft : σ.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  let := σ.appTop.hom.toAlgebra
  obtain ⟨t, ht⟩ := hft.out
  let v : Fin t.card → Γ(U, ⊤) := fun i ↦ (t.equivFin.symm i : Γ(U, ⊤))
  refine ⟨t.card, v, ?_⟩
  apply IsClosedImmersion.of_surjective_of_isAffine
  intro a
  let g := AffineSpace.homOfVector σ v
  let B : Subalgebra Γ(S, ⊤) Γ(U, ⊤) :=
    { g.appTop.hom.range with
      algebraMap_mem' := fun r ↦ ⟨(𝔸(Fin t.card; S) ↘ S).appTop r, by
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over]
        rfl⟩ }
  have hB : Algebra.adjoin Γ(S, ⊤) (t : Set Γ(U, ⊤)) ≤ B := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    refine ⟨AffineSpace.coord S (t.equivFin ⟨x, hx⟩), ?_⟩
    simp [g, v]
  exact hB (ht ▸ Algebra.mem_top)

example {U : Scheme.{0}} [IsAffine U] :
    ∃ (n : ℕ) (v : Fin n → Γ(U, ⊤)), IsClosedImmersion (AffineSpace.homOfVector (𝟙 U) v) :=
  AnalytificationChow3_exists_isClosedImmersion_homOfVector (𝟙 U)

/-- The ring map `ℤ[x_0, …, x_n] ⟶ Γ(𝔸ⁿ_ℤ)`, `x_0 ↦ 1`, `x_{k+1} ↦ x_k` (dehomogenization).
Source: Hartshorne, *Algebraic Geometry*, Prop. II.2.5(b) (`D₊(x_0) ≅ 𝔸ⁿ`). -/
def AnalytificationChow3_dehomog (n : ℕ) :
    MvPolynomial (Fin (n + 1)) (ULift.{0} ℤ) →+*
      Γ(Spec (CommRingCat.of (MvPolynomial (Fin n) (ULift.{0} ℤ))), ⊤) :=
  (Scheme.ΓSpecIso _).inv.hom.comp
    (aeval (Fin.cons 1 X : Fin (n + 1) → MvPolynomial (Fin n) (ULift.{0} ℤ))).toRingHom

lemma AnalytificationChow3_dehomog_X_zero (n : ℕ) : AnalytificationChow3_dehomog n (X 0) = 1 := by
  simp [AnalytificationChow3_dehomog]

lemma AnalytificationChow3_dehomog_surjective (n : ℕ) :
    Function.Surjective (AnalytificationChow3_dehomog n) := by
  intro a
  obtain ⟨p, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso
    (CommRingCat.of (MvPolynomial (Fin n) (ULift.{0} ℤ)))).inv).2 a
  refine ⟨rename Fin.succ p, ?_⟩
  have hc : (Fin.cons 1 X : Fin (n + 1) → MvPolynomial (Fin n) (ULift.{0} ℤ)) ∘ Fin.succ = X :=
    funext fun i ↦ Fin.cons_succ _ _ _
  simp only [AnalytificationChow3_dehomog, RingHom.coe_comp, Function.comp_apply]
  congr 1
  change bind₁ _ (rename Fin.succ p) = p
  rw [bind₁_rename, hc, bind₁_X_left]
  rfl

lemma AnalytificationChow3_dehomog_irrelevant (n : ℕ) :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))).toIdeal.map
      (AnalytificationChow3_dehomog n) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ zero_lt_one
      (isHomogeneous_X _ 0)))
    (by rw [AnalytificationChow3_dehomog_X_zero]; exact isUnit_one)

/-- The standard chart `𝔸ⁿ_ℤ ⟶ ℙⁿ_ℤ`, `x_0 ↦ 1`, as a morphism to `Proj`.
Source: Hartshorne, *Algebraic Geometry*, Prop. II.2.5(b); Mathlib `Proj.fromOfGlobalSections`. -/
def AnalytificationChow3_chart (n : ℕ) :
    Spec (CommRingCat.of (MvPolynomial (Fin n) (ULift.{0} ℤ))) ⟶
      Proj (homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)) :=
  Proj.fromOfGlobalSections _ (AnalytificationChow3_dehomog n)
    (AnalytificationChow3_dehomog_irrelevant n)

/-- The standard chart is an immersion: over `D₊(x_0)` it is a closed immersion (its ring map is
surjective and sends `x_0` to `1`), and its preimage of `D₊(x_0)` is everything.
Source: Hartshorne, *Algebraic Geometry*, Prop. II.2.5(b); `g3c_isClosedImmersion_fromOfGlobalSections_restrict`. -/
theorem AnalytificationChow3_isImmersion_chart (n : ℕ) :
    IsImmersion (AnalytificationChow3_chart n) := by
  let D := Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)) (X 0)
  have hD : AnalytificationChow3_chart n ⁻¹ᵁ D = ⊤ := by
    rw [AnalytificationChow3_chart, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ zero_lt_one
      (isHomogeneous_X _ 0), AnalytificationChow3_dehomog_X_zero, Scheme.basicOpen_one]
  have hc : IsClosedImmersion (AnalytificationChow3_chart n ∣_ D) :=
    HodgeLean.Foundations.g3c_isClosedImmersion_fromOfGlobalSections_restrict _ _ _
      (AnalytificationChow3_dehomog_surjective n) (isHomogeneous_X _ 0)
      (AnalytificationChow3_dehomog_X_zero n)
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage _ fun x ↦ ⟨D, ?_, ?_⟩
  · change x ∈ AnalytificationChow3_chart n ⁻¹ᵁ D
    rw [hD]; trivial
  · rw [← morphismRestrict_ι]
    infer_instance

/-- The standard chart over `Y`, `𝔸ⁿ_Y ⟶ ℙⁿ_Y`: the base change of `AnalytificationChow3_chart`.
Source: Hartshorne, *Algebraic Geometry*, Prop. II.2.5(b) and §II.7 (`ℙⁿ_Y = ℙⁿ_ℤ ×_ℤ Y`). -/
def AnalytificationChow3_affineToProj (n : ℕ) (Y : Scheme.{0}) :
    𝔸(Fin n; Y) ⟶ ℙ(Fin (n + 1); Y) :=
  pullback.map _ _ _ _ (𝟙 Y) (AnalytificationChow3_chart n) (𝟙 _)
    (by simp) (terminal.hom_ext _ _)

theorem AnalytificationChow3_isImmersion_affineToProj (n : ℕ) (Y : Scheme.{0}) :
    IsImmersion (AnalytificationChow3_affineToProj n Y) := by
  have := AnalytificationChow3_isImmersion_chart n
  exact MorphismProperty.pullbackMap (P := @IsImmersion) (inferInstanceAs (IsImmersion (𝟙 Y)))
    (inferInstanceAs (IsImmersion (AnalytificationChow3_chart n))) (by simp)
    (terminal.hom_ext _ _)

@[reassoc (attr := simp)]
lemma AnalytificationChow3_affineToProj_toBase (n : ℕ) (Y : Scheme.{0}) :
    AnalytificationChow3_affineToProj n Y ≫ toBase (Fin (n + 1)) Y = 𝔸(Fin n; Y) ↘ Y := by
  simp [AnalytificationChow3_affineToProj, toBase]
  rfl

/-- **Affine opens are immersed in projective space over `Y`.** For `f : X ⟶ Y` over an affine `S`
with `X` locally of finite type over `S`, every affine open `U ⊆ X` has an immersion
`U ⟶ ℙⁿ_Y` over `Y`: `U` is closed in `𝔸ⁿ_S`, so `(f, v) : U ⟶ 𝔸ⁿ_Y` is an immersion, followed by
the standard chart.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.4.10 (first step); EGA II, 5.6.1. -/
theorem AnalytificationChow3_exists_immersion {X Y S : Scheme.{0}} [IsAffine S] (σX : X ⟶ S)
    [LocallyOfFiniteType σX] (σY : Y ⟶ S) (f : X ⟶ Y) (hf : f ≫ σY = σX) (U : X.Opens)
    (hU : IsAffineOpen U) :
    ∃ (n : ℕ) (φ : U.toScheme ⟶ ℙ(Fin (n + 1); Y)),
      IsImmersion φ ∧ φ ≫ toBase (Fin (n + 1)) Y = U.ι ≫ f := by
  have : IsAffine U := hU
  obtain ⟨n, v, hv⟩ := AnalytificationChow3_exists_isClosedImmersion_homOfVector (U.ι ≫ σX)
  have hcomp : AffineSpace.homOfVector (U.ι ≫ f) v ≫ AffineSpace.map (Fin n) σY =
      AffineSpace.homOfVector (U.ι ≫ σX) v := by
    ext1
    · simp [hf]
    · simp
  have : IsImmersion (AffineSpace.homOfVector (U.ι ≫ f) v) := by
    have : IsImmersion (AffineSpace.homOfVector (U.ι ≫ f) v ≫ AffineSpace.map (Fin n) σY) := by
      rw [hcomp]; infer_instance
    exact IsImmersion.of_comp _ (AffineSpace.map (Fin n) σY)
  have := AnalytificationChow3_isImmersion_affineToProj n Y
  refine ⟨n, AffineSpace.homOfVector (U.ι ≫ f) v ≫ AnalytificationChow3_affineToProj n Y,
    inferInstance, ?_⟩
  simp

end HodgeLean.Foundations.Analytic
