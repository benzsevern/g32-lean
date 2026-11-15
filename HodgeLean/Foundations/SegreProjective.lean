import HodgeLean.Foundations.SegreProjectiveProofs
import HodgeLean.Adapters.AbelianPowerHodge

/-! # The Powers flagship, stage G3 part 2b: projectivity of fibre products (FROZEN SPEC)

Stage G3 (optional), part 2b, of formalizing PW v0.3, Theorem 4.2 (`thm:gen`)
(doi:10.5281/zenodo.23570103). G3 part 1 (`AbelianPower.lean`) builds `A^r = g3_power A r` and
discharges `[IsProjective (g3_power A r).hom]` only for `r ≤ 1`; for `r ≥ 2`, G2, G4 and F1 at
`Y = A^r` carry it as a binder. This stage targets that binder, through the Segre embedding.
`IsProjective f` is HodgeConjecture's: a closed immersion `i : X ⟶ ℙ(Fin (d+1); T)` with
`i ≫ toBase = f`, where `ℙ(Fin (d+1); T) = T ×_ℤ Proj ℤ[x_0, …, x_d]`. Each theorem is the matching
`_aux` theorem of `SegreProjectiveProofs.lean`.

It claims:

* **Part A, the Segre morphism over `ℤ`.** Mathlib's `Proj.fromOfGlobalSections` is natural in
  the source and unchanged when all sections are twisted by a unit (A1, A2). The chart maps
  `g3c_chartMap n m i j : D₊(x_i) × D₊(y_j) ⟶ Proj ℤ[z_{kl}]`, `z_{kl} ↦ (x_k/x_i)(y_l/y_j)`,
  agree on overlaps (A3), so they glue to a unique `s : ℙⁿ_ℤ × ℙᵐ_ℤ ⟶ Proj ℤ[z_{kl}]` (A4).
  For that `s`: `s⁻¹ D₊(z_{ij}) = D₊(x_i) × D₊(y_j)` (A5); the chart ring map is surjective (A6);
  `s` is a closed immersion (A7).
* **Part B, base change.** Renaming homogeneous coordinates gives isomorphic `Proj` (B1, used for
  `Fin (n+1) × Fin (m+1) ≃ Fin (n*m+n+m+1)`); `ℙ(Fin (n+1); T) ×_T ℙ(Fin (m+1); T)` is the base
  change to `T` of `ℙⁿ_ℤ × ℙᵐ_ℤ`, over `T` (B2); so there is a closed immersion
  `ℙⁿ_T ×_T ℙᵐ_T ⟶ ℙ^{nm+n+m}_T` over `T` (B3); and **for schemes `X`, `Y`, `T` in universe `0`,
  `IsProjective f` and `IsProjective g` imply `IsProjective (pullback.fst f g ≫ f)`** (B4).
* **Part C.** `IsProjective (g3_power A r).hom` for every `r`, from `[IsProjective A.hom]`, with
  no other binder (C1, registered as an instance). So the G2 and G4 statements at `Y = A^r`,
  `P = g3_powerData A r` are implications from `[GeometricallyIntegral A.hom]` alone, besides the
  scope instances of `A` (section `Link`).
* **Degenerate checks.** `ℙ⁰_ℤ` is the terminal scheme (D1); the Segre morphism with `m = 0` is
  an isomorphism (D2); `Proj` of the polynomial ring in no variables is empty, which is why
  presentations use `Fin (d+1)` (D3); every morphism out of the empty scheme is projective (D4).
* **Falsification.** `𝔸¹_ℂ ⟶ Spec ℂ` is not projective (F1), and neither is
  `𝔸¹_ℂ ×_ℂ ℙ¹_ℂ ⟶ Spec ℂ` (F2): B4 fails when one factor is only quasi-projective.

It does not claim: B4 for schemes in a universe other than `0` (the repository's schemes are in
universe `0`); a description of the image of the Segre morphism (the quadrics
`z_{ij} z_{kl} = z_{il} z_{kj}`), or of the Segre ring `⊕_d A_d ⊗ B_d`; that a composite of
projective morphisms is projective; integrality of `A^r` (G3 part 2a, `[GeometricallyIntegral
A.hom]` remains a binder); any cohomological or Hodge statement. HC no distance; AV milestone no
distance.
-/

noncomputable section

namespace HodgeLean.Foundations

open CategoryTheory Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization MonoidalCategory
open AlgebraicGeometry.ComplexProjectiveSpace ProjectiveSpace
open HodgeLean.Adapters HodgeLean.RealDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Part A: the Segre morphism over `ℤ` -/

section General

universe u

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **A1. `Proj.fromOfGlobalSections` is natural in the source.** For `g : X' ⟶ X`, the morphism
`X ⟶ Proj A` given by `f : A → Γ(X)` precomposed with `g` is the one given by `g^* ∘ f`.
Source: Hartshorne, *Algebraic Geometry*, Thm. II.7.1 (morphisms to projective space from
generating global sections, compatibly with pullback); Mathlib `Proj.fromOfGlobalSections`,
`Proj.fromOfGlobalSections_morphismRestrict`. -/
theorem spec_g3c_comp_fromOfGlobalSections {X X' : Scheme.{u}} (g : X' ⟶ X)
    (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (g.appTop.hom.comp f) = ⊤) :
    g ≫ Proj.fromOfGlobalSections 𝒜 f hf =
      Proj.fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) hf' :=
  spec_g3c_comp_fromOfGlobalSections_aux 𝒜 g f hf hf'

/-- With `g = 𝟙`, A1 is the identity (`appTop (𝟙 X) = 𝟙`). -/
example {X : Scheme.{u}} (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map ((𝟙 X : X ⟶ X).appTop.hom.comp f) = ⊤) :
    𝟙 X ≫ Proj.fromOfGlobalSections 𝒜 f hf =
      Proj.fromOfGlobalSections 𝒜 ((𝟙 X : X ⟶ X).appTop.hom.comp f) hf' :=
  spec_g3c_comp_fromOfGlobalSections 𝒜 (𝟙 X) f hf hf'

/-- **A2. Twisting by a unit does not change the morphism.** If `f' r = v^d · f r` for every
`r` of degree `d`, with `v` a unit of `Γ(X)`, then `f` and `f'` give the same morphism to
`Proj A`: on `D(f t)`, `t` of degree `d`, `f' a / f' t^k = v^{dk} f a / (v^{dk} f t^k)`.
Source: Hartshorne, *Algebraic Geometry*, Thm. II.7.1 (the morphism depends on the line bundle
with its sections only up to isomorphism; here the automorphism `v · −` of `𝒪_X`); Mathlib
`Proj.toBasicOpenOfGlobalSections`. -/
theorem spec_g3c_fromOfGlobalSections_unit_twist {X : Scheme.{u}}
    (f f' : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f' = ⊤) (v : Γ(X, ⊤)ˣ)
    (hv : ∀ (d : ℕ) (r : A), r ∈ 𝒜 d → f' r = (v : Γ(X, ⊤)) ^ d * f r) :
    Proj.fromOfGlobalSections 𝒜 f hf = Proj.fromOfGlobalSections 𝒜 f' hf' :=
  spec_g3c_fromOfGlobalSections_unit_twist_aux 𝒜 f f' hf hf' v hv

/-- With `v = 1`, the hypothesis forces `f' = f` on homogeneous elements. -/
example {X : Scheme.{u}} (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    Proj.fromOfGlobalSections 𝒜 f hf = Proj.fromOfGlobalSections 𝒜 f hf :=
  spec_g3c_fromOfGlobalSections_unit_twist 𝒜 f f hf hf 1 (fun d r _ => by simp)

end General

/-- **A3. The chart maps agree on overlaps.** On `(D₊(x_a) × D₊(y_b)) ∩ (D₊(x_{a'}) × D₊(y_{b'}))`,
the two Segre chart maps coincide: pulled back to the overlap, the second ring map is the first
twisted by the unit `(x_a/x_{a'})(y_b/y_{b'})` (A1, A2).
Source: Hartshorne, *Algebraic Geometry*, Ex. II.5.11 (the Segre embedding) and Thm. II.7.1;
`spec_g3c_comp_fromOfGlobalSections`, `spec_g3c_fromOfGlobalSections_unit_twist`. -/
theorem spec_g3c_chartMap_compat (n m : ℕ) (a b : Fin (n + 1) × Fin (m + 1)) :
    pullback.fst (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2) ≫
        g3c_chartMap n m a.1 a.2 =
      pullback.snd (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2) ≫
        g3c_chartMap n m b.1 b.2 :=
  spec_g3c_chartMap_compat_aux n m a b

example (n m : ℕ) (a : Fin (n + 1) × Fin (m + 1)) :
    pullback.fst (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m a.1 a.2) ≫
        g3c_chartMap n m a.1 a.2 =
      pullback.snd (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m a.1 a.2) ≫
        g3c_chartMap n m a.1 a.2 :=
  spec_g3c_chartMap_compat n m a a

/-- **A4. The Segre morphism over `ℤ` exists and is unique.** There is exactly one
`s : ℙⁿ_ℤ × ℙᵐ_ℤ ⟶ Proj ℤ[z_{kl}]` restricting to `g3c_chartMap n m i j` on every chart: the
charts `D₊(x_i) × D₊(y_j)` cover the product (`Scheme.Pullback.openCoverOfLeftRight` of the
coordinate covers, `iSup_coordinateBasicOpen_eq_top`), and A3 is the glueing condition.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.2.12 (glueing morphisms) and Ex. II.5.11;
Mathlib `Scheme.Cover.glueMorphisms`, `Scheme.Cover.hom_ext`. -/
theorem spec_g3c_existsUnique_segre (n m : ℕ) :
    ∃! s : g3c_prod n m ⟶ g3c_segreTarget n m,
      ∀ i j, g3c_prodChartι n m i j ≫ s = g3c_chartMap n m i j :=
  spec_g3c_existsUnique_segre_aux n m

example (n m : ℕ) : Nonempty (g3c_prod n m ⟶ g3c_segreTarget n m) :=
  ⟨(spec_g3c_existsUnique_segre n m).exists.choose⟩

/-- **A5. The Segre morphism pulls `D₊(z_{ij})` back to the chart `D₊(x_i) × D₊(y_j)`.** On the
chart `(a, b)`, the preimage is `D((x_i/x_a)(y_j/y_b))`, which is the overlap with the chart
`(i, j)` (`Proj.fromOfGlobalSections_preimage_basicOpen`).
Source: Hartshorne, *Algebraic Geometry*, Ex. II.5.11; Mathlib
`Proj.fromOfGlobalSections_preimage_basicOpen`, `Scheme.basicOpen_mul`. -/
theorem spec_g3c_segre_preimage_basicOpen (n m : ℕ) (s : g3c_prod n m ⟶ g3c_segreTarget n m)
    (hs : ∀ i j, g3c_prodChartι n m i j ≫ s = g3c_chartMap n m i j)
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    s ⁻¹ᵁ Proj.basicOpen (g3c_segreGrading n m) (X (i, j)) =
      (g3c_prodChartι n m i j).opensRange :=
  spec_g3c_segre_preimage_basicOpen_aux n m s hs i j

example (n m : ℕ) (s : g3c_prod n m ⟶ g3c_segreTarget n m)
    (hs : ∀ i j, g3c_prodChartι n m i j ≫ s = g3c_chartMap n m i j) :
    s ⁻¹ᵁ Proj.basicOpen (g3c_segreGrading n m) (X (0, 0)) =
      (g3c_prodChartι n m 0 0).opensRange :=
  spec_g3c_segre_preimage_basicOpen n m s hs 0 0

/-- **A6. The Segre chart ring map is surjective.** `Γ(D₊(x_i) × D₊(y_j)) = ℤ[x_k/x_i] ⊗ ℤ[y_l/y_j]`
is generated by the `x_k/x_i ⊗ 1` and `1 ⊗ y_l/y_j`, which are the images of `z_{kj}` and `z_{il}`
(`x_i/x_i = y_j/y_j = 1`).
Source: Hartshorne, *Algebraic Geometry*, Ex. II.5.11; Mathlib
`HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top`, `pullbackSpecIso`;
`ComplexProjectiveSpace.chartGenerator_eq_prod`. -/
theorem spec_g3c_chartSections_surjective (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    Function.Surjective (g3c_chartSections n m i j) :=
  spec_g3c_chartSections_surjective_aux n m i j

example (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    ∃ p, g3c_chartSections n m i j p = g3c_fstCoord n m i j 0 :=
  spec_g3c_chartSections_surjective n m i j _

/-- **A7. The Segre morphism over `ℤ` is a closed immersion.** Closed immersions are local on the
target; over `D₊(z_{ij})` the restriction is the morphism of affine schemes
`D₊(x_i) × D₊(y_j) ⟶ D₊(z_{ij})` (A5), whose ring map is onto (A6).
Source: Hartshorne, *Algebraic Geometry*, Ex. II.5.11 and Ex. II.3.11(b); Mathlib
`IsClosedImmersion.isZariskiLocalAtTarget`, `IsClosedImmersion.of_surjective_of_isAffine`,
`Proj.fromOfGlobalSections_morphismRestrict`. -/
theorem spec_g3c_segre_isClosedImmersion (n m : ℕ)
    (s : g3c_prod n m ⟶ g3c_segreTarget n m)
    (hs : ∀ i j, g3c_prodChartι n m i j ≫ s = g3c_chartMap n m i j) :
    IsClosedImmersion s :=
  spec_g3c_segre_isClosedImmersion_aux n m s hs

example (n m : ℕ) : ∃ s : g3c_prod n m ⟶ g3c_segreTarget n m, IsClosedImmersion s :=
  let h := (spec_g3c_existsUnique_segre n m).exists
  ⟨h.choose, spec_g3c_segre_isClosedImmersion n m _ h.choose_spec⟩

/-! ### Part B: index bookkeeping and base change to `T` -/

/-- **B1. Renaming the homogeneous coordinates.** An equivalence `ι ≃ ι'` induces an isomorphism
of the `Proj` of the polynomial rings, through the graded isomorphism `rename e` and `Proj.map`.
Source: Hartshorne, *Algebraic Geometry*, §II.2 (functoriality of `Proj`); Mathlib `Proj.map`,
`Proj.map_comp`, `Proj.map_id`, `MvPolynomial.rename`. -/
theorem spec_g3c_nonempty_proj_iso_of_equiv {ι ι' : Type} (e : ι ≃ ι') :
    Nonempty (Proj (homogeneousSubmodule ι (ULift.{0} ℤ)) ≅
      Proj (homogeneousSubmodule ι' (ULift.{0} ℤ))) :=
  spec_g3c_nonempty_proj_iso_of_equiv_aux e

/-- The `(n+1)(m+1)` bookkeeping: the Segre target is isomorphic to `ℙ^{nm+n+m}_ℤ`. -/
example (n m : ℕ) : Nonempty (g3c_segreTarget n m ≅ g3c_P (n * m + n + m)) :=
  spec_g3c_nonempty_proj_iso_of_equiv
    (finProdFinEquiv.trans (finCongr (by ring)))

example (n m : ℕ) : Fintype.card (Fin (n + 1) × Fin (m + 1)) = n * m + n + m + 1 := by
  simp only [Fintype.card_prod, Fintype.card_fin]; ring

/-- `ℙ(Fin (n+1); T)` is the base change of `g3c_P n` to `T` (definitionally). -/
example (T : Scheme.{0}) (n : ℕ) :
    ℙ(Fin (n + 1); T) = pullback (terminal.from T) (terminal.from (g3c_P n)) := rfl

/-- **B2. `ℙⁿ_T ×_T ℙᵐ_T` is the base change of `ℙⁿ_ℤ × ℙᵐ_ℤ`, over `T`.** Both are limits of the
same diagram `T ⟶ ⊤ ⟵ ℙⁿ_ℤ, ℙᵐ_ℤ`; the isomorphism commutes with the projections to `T`.
Source: Mac Lane, *Categories for the Working Mathematician*, §V.2 (limits computed in stages);
Hartshorne, *Algebraic Geometry*, Thm. II.3.3; Mathlib `pullbackAssoc`,
`pullbackRightPullbackFstIso`, `IsPullback.paste_horiz`. -/
theorem spec_g3c_pullback_projectiveSpace_iso (T : Scheme.{0}) (n m : ℕ) :
    ∃ e : pullback (toBase (Fin (n + 1)) T) (toBase (Fin (m + 1)) T) ≅
        pullback (terminal.from T) (terminal.from (g3c_prod n m)),
      e.hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ toBase (Fin (n + 1)) T :=
  spec_g3c_pullback_projectiveSpace_iso_aux T n m

example (T : Scheme.{0}) (n m : ℕ) :
    Nonempty (pullback (toBase (Fin (n + 1)) T) (toBase (Fin (m + 1)) T) ≅
      pullback (terminal.from T) (terminal.from (g3c_prod n m))) :=
  ⟨(spec_g3c_pullback_projectiveSpace_iso T n m).choose⟩

/-- **B3. The Segre embedding over `T`.** There is a closed immersion
`ℙⁿ_T ×_T ℙᵐ_T ⟶ ℙ^{nm+n+m}_T` over `T`: B2, then the base change to `T` of the Segre morphism
over `ℤ` (A4, A7) followed by the renaming isomorphism (B1); closed immersions are stable under
base change and composition.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.5.11; Mathlib
`IsClosedImmersion.isStableUnderBaseChange`, `IsClosedImmersion.comp`,
`MorphismProperty.pullbackMap`. -/
theorem spec_g3c_segre_over (T : Scheme.{0}) (n m : ℕ) :
    ∃ s : pullback (toBase (Fin (n + 1)) T) (toBase (Fin (m + 1)) T) ⟶
        ℙ(Fin (n * m + n + m + 1); T),
      IsClosedImmersion s ∧
        s ≫ toBase (Fin (n * m + n + m + 1)) T =
          pullback.fst _ _ ≫ toBase (Fin (n + 1)) T :=
  spec_g3c_segre_over_aux T n m

/-- At `n = m = 0`, B3 embeds `T ×_T T` in `ℙ⁰_T` (ambient dimension `0 * 0 + 0 + 0 = 0`). -/
example (T : Scheme.{0}) :
    ∃ s : pullback (toBase (Fin 1) T) (toBase (Fin 1) T) ⟶ ℙ(Fin 1; T),
      IsClosedImmersion s ∧ s ≫ toBase (Fin 1) T = pullback.fst _ _ ≫ toBase (Fin 1) T :=
  spec_g3c_segre_over T 0 0

/-- **B4. A fibre product of projective morphisms is projective.** From presentations
`i : X ⟶ ℙⁿ_T`, `j : Y ⟶ ℙᵐ_T`, the map `i × j : X ×_T Y ⟶ ℙⁿ_T ×_T ℙᵐ_T` is a closed immersion
(`MorphismProperty.pullbackMap`), and composing with B3 gives a presentation of
`X ×_T Y ⟶ T` of ambient dimension `nm + n + m`.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.4.9 and Ex. II.5.11 (products of projective
morphisms via the Segre embedding); Mathlib `MorphismProperty.pullbackMap`; upstream
`ProjectiveSpace.Presentation` at `2ead713`. -/
theorem spec_g3c_isProjective_pullback {X Y T : Scheme.{0}} (f : X ⟶ T) (g : Y ⟶ T)
    [IsProjective f] [IsProjective g] : IsProjective (pullback.fst f g ≫ f) :=
  spec_g3c_isProjective_pullback_aux f g

/-- The same morphism through the second factor. -/
example {X Y T : Scheme.{0}} (f : X ⟶ T) (g : Y ⟶ T) [IsProjective f] [IsProjective g] :
    IsProjective (pullback.snd f g ≫ g) := by
  rw [← pullback.condition]; exact spec_g3c_isProjective_pullback f g

/-- So a product of projective schemes over `ℂ` is projective, in `Over (Spec ℂ)`. -/
example (X Y : Over (Spec ↧ℂ)) [IsProjective X.hom] [IsProjective Y.hom] :
    IsProjective (X ⊗ Y).hom :=
  spec_g3c_isProjective_pullback X.hom Y.hom

/-! ### Part C: the power `A^r` -/

/-- **C1. `A^r` is projective.** By induction on `r`: `A^0 = Spec ℂ` is projective (G3 part 1,
S13), and `(A ⊗ A^r).hom = pullback.fst A.hom (A^r).hom ≫ A.hom` (definitionally) is projective
by B4.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.4.9; `spec_g3c_isProjective_pullback`,
`spec_g3_isProjective_power_zero`. -/
theorem spec_g3c_isProjective_power (A : Over (Spec ↧ℂ)) [IsProjective A.hom] (r : ℕ) :
    IsProjective (g3_power A r).hom :=
  spec_g3c_isProjective_power_aux A r

attribute [instance] spec_g3c_isProjective_power

/-- `r = 2`, from the instance. -/
example (A : Over (Spec ↧ℂ)) [IsProjective A.hom] : IsProjective (g3_power A 2).hom :=
  inferInstance

/-! ### Degenerate checks and falsification -/

/-- **D1. `ℙ⁰_ℤ` is the terminal scheme.** `Proj ℤ[x_0] = D₊(x_0) = Spec ℤ[x_0]_{(x_0)} = Spec ℤ`.
Source: Hartshorne, *Algebraic Geometry*, Prop. II.2.5(b); Mathlib `Proj.basicOpenIsoSpec`;
upstream `ProjectiveSpace.degreeZeroEquiv` at `2ead713`. -/
theorem spec_g3c_isIso_terminal_from_P_zero : IsIso (terminal.from (g3c_P 0)) :=
  spec_g3c_isIso_terminal_from_P_zero_aux

attribute [local instance] spec_g3c_isIso_terminal_from_P_zero in
/-- So `ℙ(Fin 1; T) ⟶ T` is an isomorphism (`ℙ⁰_T = T`), for every `T`. -/
example (T : Scheme.{0}) : IsIso (toBase (Fin 1) T) := by
  change IsIso (pullback.fst (terminal.from T) (terminal.from (g3c_P 0)))
  infer_instance

/-- **D2. With `m = 0` the Segre morphism is an isomorphism** (`ℙⁿ × ℙ⁰ = ℙⁿ`, and
`z_{k0} ↦ x_k / x_i` on the chart `D₊(x_i) × ℙ⁰`).
Source: Hartshorne, *Algebraic Geometry*, Ex. II.5.11 (the case `s = 0`); Mathlib
`isIso_of_isClosedImmersion_of_surjective`, `IsZariskiLocalAtTarget`. -/
theorem spec_g3c_segre_isIso_right_zero (n : ℕ) (s : g3c_prod n 0 ⟶ g3c_segreTarget n 0)
    (hs : ∀ i j, g3c_prodChartι n 0 i j ≫ s = g3c_chartMap n 0 i j) : IsIso s :=
  spec_g3c_segre_isIso_right_zero_aux n s hs

example : ∃ s : g3c_prod 0 0 ⟶ g3c_segreTarget 0 0, IsIso s :=
  let h := (spec_g3c_existsUnique_segre 0 0).exists
  ⟨h.choose, spec_g3c_segre_isIso_right_zero 0 _ h.choose_spec⟩

/-- **D3. No homogeneous coordinates: `Proj` is empty.** `ℤ[∅] = ℤ` sits in degree `0`, so the
irrelevant ideal is `0`, and every homogeneous prime contains it. This is why presentations use
`Fin (d+1)`, never `Fin 0`.
Source: Hartshorne, *Algebraic Geometry*, §II.2 (definition of `Proj S`: homogeneous primes not
containing `S₊`); Mathlib `ProjectiveSpectrum.not_irrelevant_le`. -/
theorem spec_g3c_isEmpty_proj_fin_zero :
    IsEmpty (Proj (homogeneousSubmodule (Fin 0) (ULift.{0} ℤ))) :=
  spec_g3c_isEmpty_proj_fin_zero_aux

example : IsEmpty (Proj (homogeneousSubmodule (Fin 0) (ULift.{0} ℤ))) :=
  spec_g3c_isEmpty_proj_fin_zero

/-- **D4. The empty scheme is projective over anything.** A morphism from the empty scheme to
`ℙ⁰_T` is a closed immersion (Mathlib's instance for an empty source).
Source: Hartshorne, *Algebraic Geometry*, §II.3 (the empty closed subscheme); Mathlib
`IsClosedImmersion` of `[IsEmpty X]`. -/
theorem spec_g3c_isProjective_of_isEmpty {X T : Scheme.{0}} [IsEmpty X] (f : X ⟶ T) :
    IsProjective f :=
  spec_g3c_isProjective_of_isEmpty_aux f

/-- So B4 with an empty factor is consistent. -/
example {X Y T : Scheme.{0}} [IsEmpty X] (f : X ⟶ T) (g : Y ⟶ T) [IsProjective g] :
    IsProjective (pullback.fst f g ≫ f) :=
  have : IsProjective f := spec_g3c_isProjective_of_isEmpty f
  spec_g3c_isProjective_pullback f g

/-- **F1. The affine line is not projective over `ℂ`.** Projective implies proper; a proper
affine morphism is finite; `ℂ[t]` is not a finite `ℂ`-module.
Source: Hartshorne, *Algebraic Geometry*, Thm. II.4.9 and Ex. II.4.6; Mathlib
`IsFinite.iff_isProper_and_isAffineHom`; upstream `IsProjective.isProper` at `2ead713`. -/
theorem spec_g3c_not_isProjective_affineLine :
    ¬ IsProjective (𝔸(Fin 1; Spec ↧ℂ) ↘ Spec ↧ℂ) :=
  spec_g3c_not_isProjective_affineLine_aux

example : ¬ IsProjective (𝔸(Fin 1; Spec ↧ℂ) ↘ Spec ↧ℂ) := spec_g3c_not_isProjective_affineLine

/-- **F2. `𝔸¹ × ℙ¹` is not projective over `ℂ`.** Otherwise it is proper over `ℂ`; its projection
to `𝔸¹` is surjective (base change of the surjection `ℙ¹ ⟶ Spec ℂ`), so `𝔸¹ ⟶ Spec ℂ` would be
universally closed, hence proper, contradicting F1. So B4 needs both factors projective:
quasi-projective is not enough.
Source: Hartshorne, *Algebraic Geometry*, Thm. II.4.9, Ex. II.4.6 and Cor. II.4.8(e); Mathlib
`UniversallyClosed.of_comp_surjective`. -/
theorem spec_g3c_not_isProjective_affineLine_prod :
    ¬ IsProjective (pullback.fst (𝔸(Fin 1; Spec ↧ℂ) ↘ Spec ↧ℂ) (toBase (Fin 2) (Spec ↧ℂ)) ≫
      (𝔸(Fin 1; Spec ↧ℂ) ↘ Spec ↧ℂ)) :=
  spec_g3c_not_isProjective_affineLine_prod_aux

/-- The hypothesis `[IsProjective f]` of B4 cannot be dropped: with `f` the affine line and `g`
the projective line, the conclusion fails. -/
example : ¬ ∀ f : 𝔸(Fin 1; Spec ↧ℂ) ⟶ Spec ↧ℂ,
    IsProjective (pullback.fst f (toBase (Fin 2) (Spec ↧ℂ)) ≫ f) :=
  fun h => spec_g3c_not_isProjective_affineLine_prod (h _)

/-! ### The non-vacuity link with G2 and G4 -/

section Link

open TopologicalSpace AlgebraicGeometry.ComplexPoint

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom]
  [IsProjective A.hom]

/-- G2's `dim Y = r · dim A` at `Y = A^r`: the projectivity binder is discharged by C1, and
integrality comes from `[GeometricallyIntegral A.hom]` (G3 part 1, S11). -/
example [GeometricallyIntegral A.hom] (r : ℕ) :
    dim (g3_power A r).left = r * dim A.left :=
  spec_g2_dim_eq (g3_powerData A r)

/-- G4's pullback formula for `f_a` on `A^r`, with the same single extra binder. -/
example [GeometricallyIntegral A.hom] (r : ℕ) (a : Fin r → AbelianEnd A) :
    homPullback ((g3_powerData A r).sumMap a) 1 =
      ∑ i, homPullback ((g3_powerData A r).proj i) 1 ∘ₗ abelianEndAction A (a i) :=
  spec_g4_homPullback_sumMap (g3_powerData A r) a

/-- Integrality of `A^r` given directly, instead of geometric integrality of `A`. -/
example (r : ℕ) [IsIntegral (g3_power A r).left] :
    dim (g3_power A r).left = r * dim A.left :=
  spec_g2_dim_eq (g3_powerData A r)

end Link

end HodgeLean.Foundations
