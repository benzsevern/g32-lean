import HodgeLean.RealDefs.Operations

/-! # The Hodge filtration and complex conjugation on the real definitions

Hypothesis-free theorems about upstream's de Rham hypercohomology `H_dR^n(X)`, its Hodge
filtration `F^p H_dR^n(X)` and its conjugation `deRhamConj` (roadmap `docs/roadmap/layer3.md`,
§3 C3/U2 and U4).

* `deRhamConj_bettiDeRham` (C3/U2): conjugation fixes the image of rational classes and
  conjugates the complex scalar. It is stated on upstream's `H^n(X; ℚ)`, the domain of
  `bettiDeRham`, rather than on `HQ X n`: the two tensor products `ℂ ⊗[ℚ] -` carry different
  instance terms, so `z ⊗ₜ v` with `v : HQ X n` does not typecheck as an argument of `bettiDeRham`.
* `hodgeFiltration_antitone`, `hodgeFiltration_eq_top_of_nonpos`, `hodgeFiltration_eq_bot_of_lt`
  (U4), with the indices `p n : ℤ` of upstream's `hodgeFiltrationComplexSubmodule`.
* `hodgePiece_eq_bot_of_lt`: `F^p ⊓ conj F^q` vanishes when `p > n` or `q > n`.

The vanishing above degree `n` is the canonical t-structure: `F^p Ω•(X)` is strictly `≥ p`, so
`ℍ^n(X; F^p Ω•(X)) = Hom_D(ℤ[0], F^p Ω•(X)[n])` is zero for `n < p`. -/

open CategoryTheory Limits AlgebraicGeometry ComplexPoint
open scoped TensorProduct

namespace HodgeLean.RealDefs

attribute [local instance] analyticHasDerivedCategory

set_option linter.auxLemma false in
/- Upstream's spelling of the sheaf category; needed for its category instance to unify with the
one on `AnalyticAdditiveSheaf X`. -/
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable (X : Over (Spec ↧ℂ))

/-! ### Conjugation -/

/-- Conjugating `ℂ`-valued constants after including `ℚ`-valued ones changes nothing. -/
theorem fieldToComplexConstantSheaf_comp_conj :
    fieldToComplexConstantSheaf ℚ X ≫ conjConstantComplexSheaf X =
      fieldToComplexConstantSheaf ℚ X := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  change (presheafToSheaf J AddCommGrpCat).map ((Functor.const _).map
      (AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom)) ≫
      (presheafToSheaf J AddCommGrpCat).map (conjConstantComplexPresheaf X) =
    (presheafToSheaf J AddCommGrpCat).map ((Functor.const _).map
      (AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom))
  rw [← Functor.map_comp]
  congr 1
  ext U x
  change (starRingEnd ℂ) (algebraMap ℚ ℂ x) = algebraMap ℚ ℂ x
  simp

/-- The complex-level form of `fieldToComplexConstantSheaf_comp_conj`. -/
theorem fieldToComplexConstantSheafComplexInt_comp_conj :
    fieldToComplexConstantSheafComplexInt ℚ X ≫ conjConstantComplexSheafComplexInt X =
      fieldToComplexConstantSheafComplexInt ℚ X := by
  unfold fieldToComplexConstantSheafComplexInt conjConstantComplexSheafComplexInt
    conjConstantComplexComplex
  rw [← HomologicalComplex.extendMap_comp, ← Functor.map_comp,
    fieldToComplexConstantSheaf_comp_conj]

/-- Conjugation of constant `ℂ`-valued functions is an involution of the complex `ℂ[0]`. -/
theorem conjConstantComplexSheafComplexInt_comp_self :
    conjConstantComplexSheafComplexInt X ≫ conjConstantComplexSheafComplexInt X = 𝟙 _ := by
  have hs : conjConstantComplexSheaf X ≫ conjConstantComplexSheaf X = 𝟙 _ := by
    let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
    change (presheafToSheaf J AddCommGrpCat).map (conjConstantComplexPresheaf X) ≫
        (presheafToSheaf J AddCommGrpCat).map (conjConstantComplexPresheaf X) = _
    rw [← Functor.map_comp]
    have : conjConstantComplexPresheaf X ≫ conjConstantComplexPresheaf X = 𝟙 _ := by
      ext U : 2
      exact AddMonoidHom.ext fun x : ℂ => Complex.conj_conj x
    rw [this]
    exact (presheafToSheaf J AddCommGrpCat).map_id _
  unfold conjConstantComplexSheafComplexInt conjConstantComplexComplex
  rw [← HomologicalComplex.extendMap_comp, ← Functor.map_comp, hs, CategoryTheory.Functor.map_id,
    HomologicalComplex.extendMap_id]
  rfl

variable [IsIntegral X.left] [Smooth X.hom]

/-- Conjugation fixes the de Rham image of every rational class.

Checks: F-1665 -/
theorem deRhamConj_fieldToDeRhamCohomology (n : ℕ) (v : H^n(X; ℚ)) :
    deRhamConj X n (fieldToDeRhamCohomology ℚ X n v) = fieldToDeRhamCohomology ℚ X n v := by
  have h : fieldToDeRhamCohomology ℚ X n v = complexConstantCohomologyDeRhamAddEquiv X n
      (hypercohomologyMap X (fieldToComplexConstantSheafComplexInt ℚ X) n
        ((hypercohomologyAddEquivConstantCohomology ℚ X n).symm v)) := by
    unfold fieldToDeRhamCohomology fieldToHolomorphicDeRhamComplexInt
    simp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
    rw [hypercohomologyMap_comp_apply]
    rfl
  rw [h, deRhamConj_apply, AddEquiv.symm_apply_apply, ← hypercohomologyMap_comp_apply,
    fieldToComplexConstantSheafComplexInt_comp_conj]

/-- Conjugation on `H_dR^n(X)` sends `z ⊗ v`, for a rational class `v`, to `conj z ⊗ v` (C3/U2).

Stated on `H^n(X; ℚ)`, the domain of `bettiDeRham`, rather than on `HQ X n`.

Checks: F-1665 -/
theorem deRhamConj_bettiDeRham (n : ℕ) (z : ℂ) (v : H^n(X; ℚ)) :
    deRhamConj X n (bettiDeRham X n (z ⊗ₜ v)) = bettiDeRham X n (starRingEnd ℂ z ⊗ₜ v) := by
  rw [bettiDeRham, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, deRhamConj_smul]
  congr 1
  exact deRhamConj_fieldToDeRhamCohomology X n v

/-- Conjugation on `H_dR^n(X)` is an involution.

Checks: F-1665 -/
theorem deRhamConj_deRhamConj (n : ℤ) (α : H_dR^n(X)) :
    deRhamConj X n (deRhamConj X n α) = α := by
  rw [deRhamConj_apply, deRhamConj_apply, AddEquiv.symm_apply_apply,
    ← hypercohomologyMap_comp_apply, conjConstantComplexSheafComplexInt_comp_self,
    hypercohomologyMap_id]
  exact AddEquiv.apply_symm_apply _ α

/-! ### The Hodge filtration -/

/-- The truncated complex `F^p Ω•(X)` is strictly `≥ p`. -/
instance hodgeFilteredDeRhamComplex_isStrictlyGE (p : ℤ) :
    (F^p Ω•(X)).IsStrictlyGE p := by
  unfold hodgeFilteredDeRhamComplex
  infer_instance

/-- `F^p' H_dR^n(X) ≤ F^p H_dR^n(X)` whenever `p ≤ p'`.

Checks: F-1665 -/
theorem hodgeFiltration_le_of_le {p p' : ℤ} (h : p ≤ p') (n : ℤ) :
    F^p' H_dR^n(X) ≤ F^p H_dR^n(X) := by
  have : (F^p' Ω•(X)).IsStrictlyGE p := (F^p' Ω•(X)).isStrictlyGE_of_ge p p' h
  let e := ComplexShape.embeddingUpIntGE p
  -- `F^p' Ω•(X)` is its own truncation at `p`, so it maps to `F^p Ω•(X)` over `Ω•(X)`.
  let g : F^p' Ω•(X) ⟶ F^p Ω•(X) :=
    inv (HomologicalComplex.stupidTruncInclusion (F^p' Ω•(X)) e) ≫
      HomologicalComplex.stupidTruncMap (hodgeFilteredDeRhamInclusion X p') e
  have hc : HomologicalComplex.stupidTruncMap (hodgeFilteredDeRhamInclusion X p') e ≫
      hodgeFilteredDeRhamInclusion X p =
    HomologicalComplex.stupidTruncInclusion (F^p' Ω•(X)) e ≫ hodgeFilteredDeRhamInclusion X p' :=
    HomologicalComplex.stupidTruncMap_comp_stupidTruncInclusion e _
  have hg : g ≫ hodgeFilteredDeRhamInclusion X p = hodgeFilteredDeRhamInclusion X p' :=
    (Category.assoc _ _ _).trans
      ((congrArg (inv (HomologicalComplex.stupidTruncInclusion (F^p' Ω•(X)) e) ≫ ·) hc).trans
        (IsIso.inv_hom_id_assoc _ _))
  rintro _ ⟨β, rfl⟩
  refine ⟨hypercohomologyMap X g n β, ?_⟩
  change hypercohomologyMap X _ n (hypercohomologyMap X g n β) = hypercohomologyMap X _ n β
  rw [← hypercohomologyMap_comp_apply, hg]

/-- The Hodge filtration is decreasing in `p`; in particular `F^(p+1) ≤ F^p` (U4).

Checks: F-1665 -/
theorem hodgeFiltration_antitone (n : ℤ) :
    Antitone fun p : ℤ => F^p H_dR^n(X) :=
  fun _ _ h => hodgeFiltration_le_of_le X h n

/-- `F^(p+1) H_dR^n(X) ≤ F^p H_dR^n(X)` (U4).

Checks: F-1665 -/
theorem hodgeFiltration_succ_le (p n : ℤ) : F^(p + 1) H_dR^n(X) ≤ F^p H_dR^n(X) :=
  hodgeFiltration_le_of_le X (Int.le_add_one le_rfl) n

/-- `F^p H_dR^n(X)` is everything for `p ≤ 0` (U4).

Checks: F-1665 -/
theorem hodgeFiltration_eq_top_of_nonpos {p : ℤ} (hp : p ≤ 0) (n : ℤ) :
    F^p H_dR^n(X) = ⊤ := by
  have : Ω•(X).IsStrictlyGE p := Ω•(X).isStrictlyGE_of_ge p 0 hp
  have : IsIso (hodgeFilteredDeRhamInclusion X p) :=
    HomologicalComplex.stupidTruncInclusion_isIso Ω•(X) (ComplexShape.embeddingUpIntGE p)
  refine eq_top_iff.mpr fun β _ =>
    ⟨hypercohomologyMap X (inv (hodgeFilteredDeRhamInclusion X p)) n β, ?_⟩
  change hypercohomologyMap X _ n (hypercohomologyMap X _ n β) = β
  rw [← hypercohomologyMap_comp_apply, IsIso.inv_hom_id, hypercohomologyMap_id]
  rfl

omit [IsIntegral X.left] [Smooth X.hom] in
/-- `ℍ^n(X; K)` is trivial for a complex `K` that is strictly `≥ p` with `n < p`.

Checks: F-1665 -/
theorem hypercohomology_subsingleton_of_isStrictlyGE
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) {p n : ℤ} [K.IsStrictlyGE p] (h : n < p) :
    Subsingleton ℍ^n(X; K) := by
  refine ⟨fun α β => (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective ?_⟩
  have h₁ : DerivedCategory.TStructure.t.IsLE
      (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X)) 0 :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (DerivedCategory.Q.mapIso (constantIntegerSheafComplexIntIsoSingleULift X).symm) 0
  have h₂ : DerivedCategory.TStructure.t.IsGE ((DerivedCategory.Q.obj K)⟦n⟧) (p - n) :=
    DerivedCategory.TStructure.t.isGE_shift _ p n (p - n)
  exact (DerivedCategory.TStructure.t.zero _ 0 (p - n) (by lia)).trans
    (DerivedCategory.TStructure.t.zero _ 0 (p - n) (by lia)).symm

/-- `F^p H_dR^n(X)` is zero for `p > n`, since `F^p Ω•(X)` starts in degree `p` (U4).

Checks: F-1665 -/
theorem hodgeFiltration_eq_bot_of_lt {p n : ℤ} (h : n < p) :
    F^p H_dR^n(X) = ⊥ := by
  have := hypercohomology_subsingleton_of_isStrictlyGE X (F^p Ω•(X)) h
  refine eq_bot_iff.mpr ?_
  rintro _ ⟨β, rfl⟩
  rw [Subsingleton.elim β 0, map_zero]
  exact Submodule.zero_mem _

/-- The conjugate filtration `conj F^q H_dR^n(X)` is zero for `q > n`.

Checks: F-1665 -/
theorem conjHodgeFiltration_eq_bot_of_lt {q n : ℤ} (h : n < q) :
    conjHodgeFiltrationComplexSubmodule X q n = ⊥ := by
  refine eq_bot_iff.mpr fun α hα => ?_
  have h0 : deRhamConj X n α = 0 := by
    have : deRhamConjSemilinear X n α ∈ F^q H_dR^n(X) := hα
    rw [hodgeFiltration_eq_bot_of_lt X h] at this
    exact this
  rw [Submodule.mem_bot, ← deRhamConj_deRhamConj X n α, h0, map_zero]

/-- `hodgePiece X p q n` is zero when `p > n` or `q > n`.

Checks: F-1665 -/
theorem hodgePiece_eq_bot_of_lt {p q n : ℤ} (h : n < p ∨ n < q) :
    hodgePiece X p q n = ⊥ := by
  rcases h with h | h
  · rw [hodgePiece, hodgeFiltration_eq_bot_of_lt X h, bot_inf_eq]
  · rw [hodgePiece, conjHodgeFiltration_eq_bot_of_lt X h, inf_bot_eq]

end HodgeLean.RealDefs
