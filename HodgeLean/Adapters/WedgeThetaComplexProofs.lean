import HodgeLean.Adapters.WedgeThetaComplexDefs

/-! # Open obligations of stage `WedgeThetaComplex`

One `_aux` obligation per statement of `WedgeThetaComplex.lean`, all open. The statements, their
sources and their falsification checks are in `docs/specs/WedgeThetaComplex.md`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.Foundations

namespace HodgeLean.Adapters

section WedgeLaneA

attribute [local instance] chartFieldModule chartFieldTower

/-- Near each point of `U`, a section of `Ω^p` on `U` is the sheafification of a Kähler form. -/
theorem wedgeA_exists_local_rep (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ℕ) (U : Opens (TopCat.of (ComplexPoint X)))
    (s : (holomorphicDeRhamSheaf X d p).presheaf.obj (op U)) (x : ComplexPoint X) (hx : x ∈ U) :
    ∃ (V : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ V) (hVU : V ≤ U)
      (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op V)) p),
      (holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE hVU).op s =
        (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d p)).app (op V) (Submodule.Quotient.mk ω) := by
  have hS := Presheaf.imageSieve_mem (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d p)) s
  obtain ⟨V, f, ⟨t, ht⟩, hxV⟩ := hS x hx
  obtain ⟨ω, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  exact ⟨V, hxV, f.le, ω, ht.symm⟩

open scoped Manifold in
/-- The value at `y ∈ V` of the sheafification of a Kähler form on `V` is its chart evaluation
at `y`. -/
theorem wedgeA_formStalkValue_mk (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ℕ) (V : Opens (TopCat.of (ComplexPoint X)))
    (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op V)) p)
    (y : ComplexPoint X) (hy : y ∈ V) :
    formStalkValue X d y p ((holomorphicDeRhamSheaf X d p).presheaf.germ V y hy
      ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app (op V) (Submodule.Quotient.mk ω))) =
      chartEvaluationHolo X d (op V) y p ω
        ⟨_, extChartAt_self_mem_chartSectionDomain X d (op V) hy⟩ := by
  rw [spec_formStalkValue_germ_toSheafify]
  change extendByZero X d (op V) y _ _ = _
  rw [extendByZero_apply_of_mem X d (op V) y _ (extChartAt_self_mem_chartSectionDomain X d (op V) hy),
    LinearMap.restrictScalars_apply]

open scoped Manifold in
/-- The covector of a global `1`-form represented on `V` by `ι m` is the derivative of `m`. -/
theorem wedgeA_covector_eq (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (V : Opens (TopCat.of (ComplexPoint X))) (m : Ω[OpenHolomorphicFunctions X d (op V)⁄ℂ])
    (hm : (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op θ =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d 1)).app (op V)
        (Submodule.Quotient.mk (exteriorPower.ιMulti _ 1 fun _ => m)))
    (y : ComplexPoint X) (hy : y ∈ V) :
    globalOneFormCovector X d θ y =
      (chartDerivation X d (op V) y).liftKaehlerDifferential m
        ⟨_, extChartAt_self_mem_chartSectionDomain X d (op V) hy⟩ := by
  have hmem := extChartAt_self_mem_chartSectionDomain X d (op V) hy
  rw [globalOneFormCovector, globalFormValue_eq_chartEvaluation_self X d 1 θ V _ hm y hy]
  change (ContinuousAlternatingMap.ofSubsingleton ℂ (Fin d → ℂ) ℂ (0 : Fin 1)).symm
    (extendByZero X d (op V) y _ _) = _
  rw [extendByZero_apply_of_mem X d (op V) y _ hmem, LinearMap.restrictScalars_apply,
    laneB_chartEvaluationHolo_ιMulti, laneB_ofSubsingleton_symm_wedgeCovectors]


/-- Near each point of `U`, both `θ` and a section `s` on `U` come from Kähler forms `ι m` and
`ω` on one open. -/
theorem wedgeA_exists_local (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (p : ℕ)
    (U : Opens (TopCat.of (ComplexPoint X)))
    (s : (holomorphicDeRhamSheaf X d p).presheaf.obj (op U)) (x : ComplexPoint X) (hx : x ∈ U) :
    ∃ (V : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ V) (hVU : V ≤ U)
      (m : Ω[OpenHolomorphicFunctions X d (op V)⁄ℂ])
      (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op V)) p),
      (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op θ =
        (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d 1)).app (op V)
          (Submodule.Quotient.mk (exteriorPower.ιMulti _ 1 fun _ => m)) ∧
      (holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE hVU).op s =
        (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d p)).app (op V) (Submodule.Quotient.mk ω) := by
  obtain ⟨V₁, hx₁, ω₁, h₁⟩ := spec_exists_local_representative X d 1 θ x
  obtain ⟨V, hxV, hVU', ω, hω⟩ := wedgeA_exists_local_rep X d p (U ⊓ V₁)
    ((holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE inf_le_left).op s) x ⟨hx, hx₁⟩
  have hVU : V ≤ U := hVU'.trans inf_le_left
  have hVV₁ : V ≤ V₁ := hVU'.trans inf_le_right
  refine ⟨V, hxV, hVU, exteriorPower.oneEquiv _ _ (formRestriction X d (homOfLE hVV₁).op 1 ω₁),
    ω, ?_, ?_⟩
  · rw [← exteriorPower.oneEquiv_symm_apply, LinearEquiv.symm_apply_apply,
      ← laneB_map_toSheafify_mk X d 1 hVV₁, ← h₁, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp]
    rfl
  · rw [← hω, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

/-- The local product `ι m * ω` has the values `θ(y) ∧ s(y)` when `θ = ι m` and `s = ω` on `V`. -/
theorem wedgeA_formStalkValue_ι_mul (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (n : ℕ)
    (U : Opens (TopCat.of (ComplexPoint X)))
    (s : (holomorphicDeRhamSheaf X d n).presheaf.obj (op U))
    (V : Opens (TopCat.of (ComplexPoint X))) (hVU : V ≤ U)
    (m : Ω[OpenHolomorphicFunctions X d (op V)⁄ℂ])
    (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op V)) n)
    (hm : (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op θ =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d 1)).app (op V)
        (Submodule.Quotient.mk (exteriorPower.ιMulti _ 1 fun _ => m)))
    (hω : (holomorphicDeRhamSheaf X d n).presheaf.map (homOfLE hVU).op s =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d n)).app (op V) (Submodule.Quotient.mk ω))
    (y : ComplexPoint X) (hy : y ∈ V) :
    formStalkValue X d y (n + 1) ((holomorphicDeRhamSheaf X d (n + 1)).presheaf.germ V y hy
      ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d (n + 1))).app (op V)
        (Submodule.Quotient.mk ⟨_, laneB_ι_mul_mem n m ω⟩))) =
      covectorWedgeForm (globalOneFormCovector X d θ y)
        (formStalkValue X d y n ((holomorphicDeRhamSheaf X d n).presheaf.germ U y (hVU hy) s)) := by
  rw [wedgeA_formStalkValue_mk, laneB_chartEvaluationHolo_ι_mul, covectorWedgeForm,
    wedgeA_covector_eq X d θ V m hm y hy,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE hVU) y hy, hω, wedgeA_formStalkValue_mk]


/-- Sections of `Ω^p` with prescribed values glue: if near each point of `U` there is a section
with the values `F`, there is one on `U`. -/
theorem wedgeA_exists_section_of_local (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (U : Opens (TopCat.of (ComplexPoint X)))
    (F : ∀ y : ComplexPoint X, y ∈ U → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (h : ∀ x, x ∈ U → ∃ (V : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ V) (hVU : V ≤ U)
      (t : (holomorphicDeRhamSheaf X d p).presheaf.obj (op V)), ∀ y (hy : y ∈ V),
        formStalkValue X d y p ((holomorphicDeRhamSheaf X d p).presheaf.germ V y hy t) =
          F y (hVU hy)) :
    ∃ t : (holomorphicDeRhamSheaf X d p).presheaf.obj (op U), ∀ y (hy : y ∈ U),
      formStalkValue X d y p ((holomorphicDeRhamSheaf X d p).presheaf.germ U y hy t) = F y hy := by
  choose V hxV hVU t ht using h
  have hcompat : TopCat.Presheaf.IsCompatible (holomorphicDeRhamSheaf X d p).presheaf
      (fun x : U => V x.1 x.2) (fun x => t x.1 x.2) := by
    intro a b
    apply laneB_section_eq X d p
    intro y hy
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ht, ht]
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' (holomorphicDeRhamSheaf X d p)
    (fun x : U => V x.1 x.2) U (fun x => homOfLE (hVU x.1 x.2))
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxV y hy⟩) _ hcompat
  refine ⟨g, fun y hy => ?_⟩
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (hVU y hy)) y (hxV y hy), hg ⟨y, hy⟩, ht]

/-- On every open, the wedge with `θ` of a section exists as a section with the pointwise
values `θ(y) ∧ s(y)`. -/
theorem wedgeA_exists_wedge_section (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (n : ℕ)
    (U : Opens (TopCat.of (ComplexPoint X)))
    (s : (holomorphicDeRhamSheaf X d n).presheaf.obj (op U)) :
    ∃ t : (holomorphicDeRhamSheaf X d (n + 1)).presheaf.obj (op U), ∀ y (hy : y ∈ U),
      formStalkValue X d y (n + 1) ((holomorphicDeRhamSheaf X d (n + 1)).presheaf.germ U y hy t) =
        covectorWedgeForm (globalOneFormCovector X d θ y)
          (formStalkValue X d y n ((holomorphicDeRhamSheaf X d n).presheaf.germ U y hy s)) := by
  refine wedgeA_exists_section_of_local X d (n + 1) U _ fun x hx => ?_
  obtain ⟨V, hxV, hVU, m, ω, hm, hω⟩ := wedgeA_exists_local X d θ n U s x hx
  exact ⟨V, hxV, hVU, _, fun y hy => wedgeA_formStalkValue_ι_mul X d θ n U s V hVU m ω hm hω y hy⟩

theorem wedgeA_covectorWedgeForm_add {d n : ℕ} (a : (Fin d → ℂ) →L[ℂ] ℂ)
    (α β : (Fin d → ℂ) [⋀^Fin n]→L[ℂ] ℂ) :
    covectorWedgeForm a (α + β) = covectorWedgeForm a α + covectorWedgeForm a β := by
  rw [covectorWedgeForm, covectorWedgeForm, covectorWedgeForm,
    ← ContinuousAlternatingMap.alternatizeUncurryFin_add]
  congr 1
  ext u
  simp [smul_add]

theorem wedgeA_covectorWedgeForm_zero {d n : ℕ} (a : (Fin d → ℂ) →L[ℂ] ℂ) :
    covectorWedgeForm a (0 : (Fin d → ℂ) [⋀^Fin n]→L[ℂ] ℂ) = 0 := by
  ext v
  simp [covectorWedgeForm, ContinuousAlternatingMap.alternatizeUncurryFin_apply]

end WedgeLaneA

theorem spec_exists_isWedgeBy_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (n : ℕ) :
    ∃ w : holomorphicDeRhamSheaf X d n ⟶ holomorphicDeRhamSheaf X d (n + 1),
      IsWedgeBy X d θ n w := by
  choose t ht using fun (U : Opens (TopCat.of (ComplexPoint X))) s =>
    wedgeA_exists_wedge_section X d θ n U s
  let f : (holomorphicDeRhamSheaf X d n).presheaf ⟶ (holomorphicDeRhamSheaf X d (n + 1)).presheaf :=
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := t U.unop
          map_zero' := by
            apply laneB_section_eq_zero X d (n + 1) U.unop
            intro y hy
            rw [ht, map_zero, map_zero, wedgeA_covectorWedgeForm_zero]
          map_add' := fun s₁ s₂ => by
            apply laneB_section_eq X d (n + 1) U.unop
            intro y hy
            rw [ht, map_add, map_add, map_add, map_add, ht, ht, wedgeA_covectorWedgeForm_add] }
      naturality := fun U V i => by
        apply AddCommGrpCat.hom_ext
        ext s
        apply laneB_section_eq X d (n + 1) V.unop
        intro y hy
        simp only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_mk,
          ZeroHom.coe_mk]
        rw [TopCat.Presheaf.germ_res_apply', ht, ht, TopCat.Presheaf.germ_res_apply'] }
  exact ⟨⟨f⟩, fun U x hx s => ht U s x hx⟩


theorem spec_isWedgeBy_unique_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (n : ℕ)
    (w w' : holomorphicDeRhamSheaf X d n ⟶ holomorphicDeRhamSheaf X d (n + 1))
    (hw : IsWedgeBy X d θ n w) (hw' : IsWedgeBy X d θ n w') : w = w' := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext s
  apply laneB_section_eq X d (n + 1) U.unop
  intro y hy
  rw [hw U.unop y hy s, hw' U.unop y hy s]


section WedgeLaneA3

attribute [local instance] chartFieldModule chartFieldTower

/-- On sections of `Ω^p` over `U`, the differential of the sheafification of `ω` on `V ≤ U` is
the sheafification of `dω`. -/
theorem wedgeA_map_differential (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ℕ) {U V : Opens (TopCat.of (ComplexPoint X))} (hVU : V ≤ U)
    (σ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op U))
    (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op V)) p)
    (hω : (holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE hVU).op σ =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app (op V) (Submodule.Quotient.mk ω)) :
    (holomorphicDeRhamSheaf X d (p + 1)).presheaf.map (homOfLE hVU).op
        ((holomorphicDeRhamSheafDifferential X d p).hom.app (op U) σ) =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d (p + 1))).app (op V)
        (Submodule.Quotient.mk (Algebra.DeRham.differential ℂ _ p ω)) := by
  have h1 := ConcreteCategory.congr_hom
    ((holomorphicDeRhamSheafDifferential X d p).hom.naturality (homOfLE hVU).op) σ
  simp only [ConcreteCategory.comp_apply] at h1
  rw [← h1, hω]
  have h2 := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamDifferential X d p)) (op V))
    (Submodule.Quotient.mk ω : HolomorphicForm X d (op V) p)
  simp only [NatTrans.comp_app] at h2
  exact h2.symm

open CliffordAlgebra (involute involute_ι) in
/-- The Leibniz rule for left multiplication by a `1`-form. -/
theorem wedgeA_extDeriv_ι_mul {A : Type} [CommRing A] [Algebra ℂ A] (m : Ω[A⁄ℂ])
    (x : Algebra.DeRham.ExtAlg ℂ A) :
    Algebra.DeRham.extDeriv ℂ A (ExteriorAlgebra.ι A m * x) =
      -(ExteriorAlgebra.ι A m * Algebra.DeRham.extDeriv ℂ A x) +
        Algebra.DeRham.extDeriv ℂ A (ExteriorAlgebra.ι A m) * x := by
  rw [Algebra.DeRham.extDeriv_mul, involute_ι, neg_mul]

/-- The Leibniz rule for `ι m * ω` on forms of degree `k`. -/
theorem wedgeA_differential_ι_mul {A : Type} [CommRing A] [Algebra ℂ A] (k : ℕ) (m : Ω[A⁄ℂ])
    (ω : Algebra.DeRham.Form ℂ A k)
    (h : Algebra.DeRham.extDeriv ℂ A (ExteriorAlgebra.ι A m) * (ω : Algebra.DeRham.ExtAlg ℂ A) ∈
      ⋀[A]^(k + 1 + 1) Ω[A⁄ℂ]) :
    Algebra.DeRham.differential ℂ A (k + 1) ⟨_, laneB_ι_mul_mem k m ω⟩ +
      ⟨_, laneB_ι_mul_mem (k + 1) m (Algebra.DeRham.differential ℂ A k ω)⟩ = ⟨_, h⟩ := by
  apply Subtype.ext
  rw [Submodule.coe_add, Algebra.DeRham.coe_differential, wedgeA_extDeriv_ι_mul]
  simp

open CliffordAlgebra (involute) in
/-- Multiplying an even element whose evaluation vanishes at a point by any form keeps the
vanishing. -/
theorem wedgeA_vanish_even_mul (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (y : ↥(chartSectionDomain X d U z))
    (e : Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U)) (he : involute e = e)
    (h2 : ∃ h : e ∈ ⋀[OpenHolomorphicFunctions X d U]^2 Ω[OpenHolomorphicFunctions X d U⁄ℂ],
      chartEvaluationHolo X d U z 2 ⟨e, h⟩ y = 0) (k : ℕ)
    (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) k) :
    ∃ h : e * (ω : Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U)) ∈
        ⋀[OpenHolomorphicFunctions X d U]^(k + 1 + 1) Ω[OpenHolomorphicFunctions X d U⁄ℂ],
      chartEvaluationHolo X d U z (k + 1 + 1) ⟨_, h⟩ y = 0 := by
  have hω : ω ∈ Submodule.span (OpenHolomorphicFunctions X d U)
      (Set.range (exteriorPower.ιMulti (OpenHolomorphicFunctions X d U) k)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨n, rfl⟩ := hw
      refine laneB_vanish_congr X d U z y (by omega) ?_
        (laneB_vanish_ιMulti_mul X d U z y 2 k n h2)
      rw [exteriorPower.ιMulti_apply_coe, laneB_ιMulti_mul_comm_of_even e he]
  | zero =>
      refine ⟨by simp, ?_⟩
      have h0 : (⟨e * ((0 : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) k) :
          Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U)), by simp⟩ :
          Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) (k + 1 + 1)) = 0 :=
        Subtype.ext (by simp)
      rw [h0, map_zero]
      rfl
  | add a b _ _ ha hb =>
      obtain ⟨ha, ea⟩ := ha
      obtain ⟨hb, eb⟩ := hb
      have hab : e * ((a + b : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) k) :
          Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U)) =
          e * (a : Algebra.DeRham.ExtAlg ℂ _) + e * (b : Algebra.DeRham.ExtAlg ℂ _) := by
        rw [Submodule.coe_add, mul_add]
      refine ⟨hab ▸ Submodule.add_mem _ ha hb, ?_⟩
      have hsplit : (⟨_, hab ▸ Submodule.add_mem _ ha hb⟩ :
          Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) (k + 1 + 1)) =
          ⟨_, ha⟩ + ⟨_, hb⟩ := Subtype.ext hab
      rw [hsplit, map_add, Pi.add_apply, ea, eb, add_zero]
  | smul a w _ hw =>
      obtain ⟨hw, ew⟩ := hw
      have haw : e * ((a • w : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) k) :
          Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U)) =
          a • (e * (w : Algebra.DeRham.ExtAlg ℂ _)) := by
        rw [Submodule.coe_smul, mul_smul_comm]
      refine ⟨haw ▸ Submodule.smul_mem _ a hw, ?_⟩
      have hsplit : (⟨_, haw ▸ Submodule.smul_mem _ a hw⟩ :
          Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) (k + 1 + 1)) =
          a • ⟨_, hw⟩ := Subtype.ext haw
      rw [hsplit, map_smul, chartFieldModule_smul_apply, ew, smul_zero]

end WedgeLaneA3

open CliffordAlgebra (involute) in
theorem spec_isWedgeBy_comp_differential_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (hθ : (holomorphicDeRhamSheafDifferential X d 1).hom.app (op ⊤) θ = 0) (n : ℕ)
    (w : holomorphicDeRhamSheaf X d n ⟶ holomorphicDeRhamSheaf X d (n + 1))
    (w' : holomorphicDeRhamSheaf X d (n + 1) ⟶ holomorphicDeRhamSheaf X d (n + 1 + 1))
    (hw : IsWedgeBy X d θ n w) (hw' : IsWedgeBy X d θ (n + 1) w') :
    w ≫ holomorphicDeRhamSheafDifferential X d (n + 1) =
      -(holomorphicDeRhamSheafDifferential X d n ≫ w') := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext s
  change (holomorphicDeRhamSheafDifferential X d (n + 1)).hom.app U (w.hom.app U s) =
    -(w'.hom.app U ((holomorphicDeRhamSheafDifferential X d n).hom.app U s))
  apply laneB_section_eq X d (n + 1 + 1) U.unop
  intro y hy
  rw [map_neg, map_neg]
  obtain ⟨V, hyV, hVU, m, ω, hm, hω⟩ := wedgeA_exists_local X d θ n U.unop s y hy
  have hmem := extChartAt_self_mem_chartSectionDomain X d (op V) hyV
  have hws : (holomorphicDeRhamSheaf X d (n + 1)).presheaf.map (homOfLE hVU).op (w.hom.app U s) =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d (n + 1))).app (op V)
        (Submodule.Quotient.mk ⟨_, laneB_ι_mul_mem n m ω⟩) := by
    apply laneB_section_eq X d (n + 1) V
    intro z hz
    rw [TopCat.Presheaf.germ_res_apply, hw U.unop z (hVU hz) s,
      wedgeA_formStalkValue_ι_mul X d θ n U.unop s V hVU m ω hm hω z hz]
  have hds := wedgeA_map_differential X d n hVU s ω hω
  have hdws := wedgeA_map_differential X d (n + 1) hVU _ _ hws
  rw [hw' U.unop y hy, ← TopCat.Presheaf.germ_res_apply _ (homOfLE hVU) y hyV, hdws,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE hVU) y hyV, hds, wedgeA_formStalkValue_mk,
    wedgeA_formStalkValue_mk, covectorWedgeForm, wedgeA_covector_eq X d θ V m hm y hyV,
    ← laneB_chartEvaluationHolo_ι_mul]
  -- the closedness of `θ` gives the vanishing of `d(ι m)` at `y`
  have h0 : chartEvaluationHolo X d (op V) y 2
      (Algebra.DeRham.differential ℂ _ 1 (exteriorPower.ιMulti _ 1 fun _ => m)) ⟨_, hmem⟩ = 0 := by
    have h := globalFormValue_eq_chartEvaluation_self X d (1 + 1) _ V _
      (laneB_map_differential X d 1 V θ _ hm) y hyV
    rw [hθ, map_zero] at h
    rw [h]
    change _ = extendByZero X d (op V) y _ _
    rw [extendByZero_apply_of_mem X d (op V) y _ hmem, LinearMap.restrictScalars_apply]
  have he : ∃ h : Algebra.DeRham.extDeriv ℂ _ (ExteriorAlgebra.ι _ m) ∈
      ⋀[OpenHolomorphicFunctions X d (op V)]^2 Ω[OpenHolomorphicFunctions X d (op V)⁄ℂ],
      chartEvaluationHolo X d (op V) y 2 ⟨_, h⟩ ⟨_, hmem⟩ = 0 := by
    refine laneB_vanish_congr X d (op V) y ⟨_, hmem⟩ rfl ?_ ⟨_, h0⟩
    rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  have heven : involute (Algebra.DeRham.extDeriv ℂ (OpenHolomorphicFunctions X d (op V))
      (ExteriorAlgebra.ι _ m)) = Algebra.DeRham.extDeriv ℂ _ (ExteriorAlgebra.ι _ m) := by
    rw [Algebra.DeRham.extDeriv_ι, Algebra.DeRham.involute_snd_phi]
  obtain ⟨hb, eb⟩ := wedgeA_vanish_even_mul X d (op V) y ⟨_, hmem⟩ _ heven he n ω
  have hsplit : Algebra.DeRham.differential ℂ _ (n + 1) ⟨_, laneB_ι_mul_mem n m ω⟩ +
      ⟨_, laneB_ι_mul_mem (n + 1) m (Algebra.DeRham.differential ℂ _ n ω)⟩ = ⟨_, hb⟩ := by
    exact wedgeA_differential_ι_mul n m ω hb
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← Pi.add_apply, ← map_add, hsplit, eb]

/-- The differential of `Ω•(X)[1]` in degree `n ≥ 0`, through `wedgeThetaShiftXIso`: it is
`-d_{n+1}` (`CochainComplex.shiftFunctor_obj_d'`). -/
theorem wedgeThetaHl1B_shift_d (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (n : ℕ) :
    (Ω•(X)⟦(1 : ℤ)⟧).d (n : ℤ) ((n + 1 : ℕ) : ℤ) =
      -((wedgeThetaShiftXIso X n).hom ≫
        holomorphicDeRhamSheafDifferential X (dim X.left) (n + 1) ≫
          (wedgeThetaShiftXIso X (n + 1)).inv) := by
  rw [CochainComplex.shiftFunctor_obj_d', Int.negOnePow_one, Units.neg_smul, one_smul,
    ← CochainComplex.of_d _ (holomorphicDeRhamSheafDifferential X (dim X.left))]
  congr 1
  simp only [wedgeThetaShiftXIso, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl]
  exact HomologicalComplex.extend_d_eq _ _ rfl rfl

theorem spec_exists_isWedgeThetaHom_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (θ : GlobalHolomorphicForm X 1) (hθ : θ ∈ closedGlobalHolomorphicForms X 1) :
    ∃ L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧, IsWedgeThetaHom X θ L := by
  have hθ' : (holomorphicDeRhamSheafDifferential X (dim X.left) 1).hom.app (op ⊤) θ = 0 := hθ
  choose w hw using fun n : ℕ => spec_exists_isWedgeBy_aux X (dim X.left) θ n
  let f : ∀ i : ℤ, Ω•(X).X i ⟶ (Ω•(X)⟦(1 : ℤ)⟧).X i := fun i =>
    match i with
    | Int.ofNat n => (wedgeThetaXIso X n).hom ≫ w n ≫ (wedgeThetaShiftXIso X n).inv
    | Int.negSucc _ => 0
  have hf : ∀ n : ℕ, f (n : ℤ) =
      (wedgeThetaXIso X n).hom ≫ w n ≫ (wedgeThetaShiftXIso X n).inv := fun _ => rfl
  refine ⟨{ f := f, comm' := ?_ }, fun n => ?_⟩
  · rintro i j (rfl : i + 1 = j)
    rcases i with n | k
    · change f (n : ℤ) ≫ (Ω•(X)⟦(1 : ℤ)⟧).d (n : ℤ) ((n + 1 : ℕ) : ℤ) =
        Ω•(X).d (n : ℤ) ((n + 1 : ℕ) : ℤ) ≫ f ((n + 1 : ℕ) : ℤ)
      have h4 : ∀ k : ℕ, (holomorphicDeRhamComplex X (dim X.left)).d k (k + 1) =
          holomorphicDeRhamSheafDifferential X (dim X.left) k := fun k =>
        CochainComplex.of_d _ _ _
      have h1 : Ω•(X).d (n : ℤ) ((n + 1 : ℕ) : ℤ) = (wedgeThetaXIso X n).hom ≫
          holomorphicDeRhamSheafDifferential X (dim X.left) n ≫
            (wedgeThetaXIso X (n + 1)).inv := by
        rw [← h4]
        exact HomologicalComplex.extend_d_eq _ _ rfl rfl
      have h2 := wedgeThetaHl1B_shift_d X n
      have h3 := spec_isWedgeBy_comp_differential_aux X (dim X.left) θ hθ' n (w n) (w (n + 1))
        (hw n) (hw (n + 1))
      rw [hf, hf, h1, h2]
      simp only [Category.assoc, Preadditive.comp_neg, Iso.inv_hom_id_assoc]
      rw [← Category.assoc (w n), h3]
      simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.assoc]
    · apply Limits.IsZero.eq_of_src
      apply HomologicalComplex.isZero_extend_X
      intro j hj
      simp only [ComplexShape.embeddingUpNat_f] at hj
      omega
  · simp [wedgeThetaComponent, hf, hw n]

theorem spec_isWedgeThetaHom_unique_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (θ : GlobalHolomorphicForm X 1) (L L' : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧)
    (hL : IsWedgeThetaHom X θ L) (hL' : IsWedgeThetaHom X θ L') : L = L' := by
  ext i
  rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
  · have h := spec_isWedgeBy_unique_aux X (dim X.left) θ n _ _ (hL n) (hL' n)
    simp only [wedgeThetaComponent] at h
    simpa using h
  · rcases n with _ | n
    · have h := spec_isWedgeBy_unique_aux X (dim X.left) θ 0 _ _ (hL 0) (hL' 0)
      simp only [wedgeThetaComponent] at h
      simpa using h
    · apply Limits.IsZero.eq_of_src
      apply HomologicalComplex.isZero_extend_X
      intro j hj
      simp only [ComplexShape.embeddingUpNat_f] at hj
      omega

/-- The covector of the zero global `1`-form is zero. -/
theorem wedgeThetaHl1B_globalOneFormCovector_zero (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (x : ComplexPoint X) :
    globalOneFormCovector X (dim X.left) (0 : GlobalHolomorphicForm X 1) x = 0 := by
  ext u
  change globalFormValue X (dim X.left) 1 x 0 (fun _ ↦ u) = 0
  simp [globalFormValue]

theorem spec_isWedgeThetaHom_zero_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] : IsWedgeThetaHom X 0 0 := by
  intro n U x hx s
  have h0 : covectorWedgeForm (0 : (Fin (dim X.left) → ℂ) →L[ℂ] ℂ)
      (formStalkValue X (dim X.left) x n
        ((holomorphicDeRhamSheaf X (dim X.left) n).presheaf.germ U x hx s)) = 0 := by
    ext v
    simp [covectorWedgeForm, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  rw [wedgeThetaHl1B_globalOneFormCovector_zero, h0]
  have hz : wedgeThetaComponent X 0 n = 0 := by simp [wedgeThetaComponent]
  have hz' : (0 : holomorphicDeRhamSheaf X (dim X.left) n ⟶
      holomorphicDeRhamSheaf X (dim X.left) (n + 1)).hom.app (op U) = 0 := rfl
  rw [hz, hz']
  simp

/-- The covector of a global `1`-form is additive in the form. -/
theorem wedgeThetaHl1B_globalOneFormCovector_add (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (x : ComplexPoint X) (θ θ' : GlobalHolomorphicForm X 1) :
    globalOneFormCovector X (dim X.left) (θ + θ') x =
      globalOneFormCovector X (dim X.left) θ x + globalOneFormCovector X (dim X.left) θ' x := by
  ext u
  change globalFormValue X (dim X.left) 1 x (θ + θ') (fun _ ↦ u) =
    globalFormValue X (dim X.left) 1 x θ (fun _ ↦ u) +
      globalFormValue X (dim X.left) 1 x θ' (fun _ ↦ u)
  unfold globalFormValue
  erw [map_add]
  rfl

/-- The wedge `a ∧ α` is additive in the covector `a`. -/
theorem wedgeThetaHl1B_covectorWedgeForm_add {d n : ℕ} (a b : (Fin d → ℂ) →L[ℂ] ℂ)
    (α : (Fin d → ℂ) [⋀^Fin n]→L[ℂ] ℂ) :
    covectorWedgeForm (a + b) α = covectorWedgeForm a α + covectorWedgeForm b α := by
  ext v
  simp [covectorWedgeForm, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Finset.sum_add_distrib, add_mul]

theorem spec_isWedgeThetaHom_add_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (θ θ' : GlobalHolomorphicForm X 1) (L L' : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧)
    (hL : IsWedgeThetaHom X θ L) (hL' : IsWedgeThetaHom X θ' L') :
    IsWedgeThetaHom X (θ + θ') (L + L') := by
  intro n U x hx s
  have hc : wedgeThetaComponent X (L + L') n =
      wedgeThetaComponent X L n + wedgeThetaComponent X L' n := by
    simp only [wedgeThetaComponent, Preadditive.add_comp, Preadditive.comp_add,
      HomologicalComplex.add_f_apply]
  rw [hc, wedgeThetaHl1B_globalOneFormCovector_add, wedgeThetaHl1B_covectorWedgeForm_add,
    ← hL n U x hx s, ← hL' n U x hx s]
  erw [Sheaf.Hom.add_app]
  simp only [AddCommGrpCat.hom_add, AddMonoidHom.add_apply, map_add]

/-- A morphism of cochain complexes `g : P ⟶ B` lifts along `ι : A ⟶ B` when `P` is zero below
`q` and `ι` is an isomorphism in degrees `≥ q`. -/
theorem wedgeTheta_exists_lift_of_isIso_ge {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
    {P A B : CochainComplex C ℤ} (ι : A ⟶ B) (g : P ⟶ B) (q : ℤ)
    (hP : ∀ n, n < q → Limits.IsZero (P.X n)) (hι : ∀ n, q ≤ n → IsIso (ι.f n)) :
    ∃ L' : P ⟶ A, L' ≫ ι = g := by
  classical
  let f : ∀ n, P.X n ⟶ A.X n := fun n =>
    if h : q ≤ n then have := hι n h; g.f n ≫ inv (ι.f n) else 0
  have hf : ∀ n (h : q ≤ n), f n ≫ ι.f n = g.f n := by
    intro n h
    have := hι n h
    simp [f, h]
  refine ⟨{ f := f, comm' := ?_ }, ?_⟩
  · intro n m hnm
    change n + 1 = m at hnm
    by_cases h : q ≤ n
    · have hm : q ≤ m := by omega
      have := hι m hm
      rw [← cancel_mono (ι.f m), Category.assoc, Category.assoc, ← ι.comm, hf m hm,
        ← Category.assoc, hf n h, g.comm]
    · exact (hP n (by omega)).eq_of_src _ _
  · ext n
    by_cases h : q ≤ n
    · exact hf n h
    · exact (hP n (by omega)).eq_of_src _ _

theorem spec_exists_hodgeFiltered_comp_inclusion_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (q : ℤ) :
    ∃ L' : F^q Ω•(X) ⟶ (F^(q + 1) Ω•(X))⟦(1 : ℤ)⟧,
      L' ≫ (hodgeFilteredDeRhamInclusion X (q + 1))⟦(1 : ℤ)⟧' =
        hodgeFilteredDeRhamInclusion X q ≫ L := by
  refine wedgeTheta_exists_lift_of_isIso_ge _ _ q (fun n hn => ?_) (fun n hn => ?_)
  · exact HomologicalComplex.isZero_stupidTrunc_X _ _ n
      ((ComplexShape.notMem_range_embeddingUpIntGE_iff q n).2 hn)
  · rw [CochainComplex.shiftFunctor_map_f']
    have h : (ComplexShape.embeddingUpIntGE (q + 1)).f (n - q).toNat = n + 1 := by
      simp only [ComplexShape.embeddingUpIntGE_f]
      omega
    rw [hodgeFilteredDeRhamInclusion, HomologicalComplex.stupidTruncInclusion_f _ _ h]
    exact Iso.isIso_hom _

local instance wedgeThetaProofsHasDerivedCategory (X : Over (Spec ↧ℂ)) :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- Under `SmallShiftedHom.equiv`, the shift map is composition with an isomorphism. -/
theorem wedgeTheta_equiv_hypercohomologyShift (X : Over (Spec ↧ℂ))
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (k : ℤ) (α : ℍ^k(X; K⟦(1 : ℤ)⟧)) :
    Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (hypercohomologyShift X K k α) =
      Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q α ≫
        ((shiftFunctor (DerivedCategory (AnalyticAdditiveSheaf X)) k).mapIso
            ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app K) ≪≫
          (shiftFunctorAdd' (DerivedCategory (AnalyticAdditiveSheaf X)) 1 k (k + 1)
            (add_comm 1 k)).symm.app _).hom := by
  simp only [hypercohomologyShift, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk]
  simp [ShiftedHom.comp, ShiftedHom.map]

theorem spec_hypercohomologyShift_bijective_aux (X : Over (Spec ↧ℂ))
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (k : ℤ) :
    Function.Bijective (hypercohomologyShift X K k) := by
  set e₁ := Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q (X := constantIntegerSheafComplexInt X) (Y := K⟦(1 : ℤ)⟧) (m := k)
  set e₂ := Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q (X := constantIntegerSheafComplexInt X) (Y := K) (m := k + 1)
  set φ := (shiftFunctor (DerivedCategory (AnalyticAdditiveSheaf X)) k).mapIso
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app K) ≪≫
    (shiftFunctorAdd' (DerivedCategory (AnalyticAdditiveSheaf X)) 1 k (k + 1)
      (add_comm 1 k)).symm.app _
  have h : ∀ α, e₂ (hypercohomologyShift X K k α) = e₁ α ≫ φ.hom :=
    wedgeTheta_equiv_hypercohomologyShift X K k
  refine ⟨fun α β hαβ => e₁.injective ?_, fun β => ⟨e₁.symm (e₂ β ≫ φ.inv), ?_⟩⟩
  · have := congrArg e₂ hαβ
    rw [h, h] at this
    exact (cancel_mono φ.hom).1 this
  · apply e₂.injective
    rw [h, Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem spec_hypercohomologyShift_hypercohomologyMap_aux (X : Over (Spec ↧ℂ))
    {K K' : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ K') (k : ℤ)
    (x : ℍ^k(X; K⟦(1 : ℤ)⟧)) :
    hypercohomologyShift X K' k (hypercohomologyMap X (f⟦(1 : ℤ)⟧') k x) =
      hypercohomologyMap X f (k + 1) (hypercohomologyShift X K k x) := by
  apply (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q).injective
  simp only [hypercohomologyShift, hypercohomologyMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk,
    Localization.SmallShiftedHom.equiv_mk₀]
  rw [ShiftedHom.comp_assoc _ _ _ (zero_add k) (add_zero 1) (by omega),
    ShiftedHom.comp_assoc _ _ _ (add_comm 1 k) (zero_add 1) (by omega),
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  congr 1
  simp only [ShiftedHom.map, CategoryTheory.Functor.map_id, Category.id_comp]
  exact ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.naturality f)

theorem spec_hypercohomologyShift_hypercohomologyMap_eq_comp_aux (X : Over (Spec ↧ℂ))
    {K K' : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (L : K ⟶ K'⟦(1 : ℤ)⟧) (k : ℤ)
    (α : ℍ^k(X; K)) :
    hypercohomologyShift X K' k (hypercohomologyMap X L k α) =
      α.comp (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom K K' (1 : ℤ) from L)) (add_comm 1 k) := by
  apply (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q).injective
  simp only [hypercohomologyShift, hypercohomologyMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk,
    Localization.SmallShiftedHom.equiv_mk₀]
  rw [ShiftedHom.comp_assoc _ _ _ (zero_add k) (add_zero 1) (by omega), ShiftedHom.mk₀_comp]
  congr 1
  simp only [ShiftedHom.map, CategoryTheory.Functor.map_id, Category.id_comp]

theorem spec_hypercohomologyShift_mem_hodgeFiltration_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (q k : ℤ)
    (α : H_dR^k(X)) (hα : α ∈ F^q H_dR^k(X)) :
    hypercohomologyShift X Ω•(X) k (hypercohomologyMap X L k α) ∈
      F^(q + 1) H_dR^(k + 1)(X) := by
  obtain ⟨β, rfl⟩ := AddMonoidHom.mem_range.1 hα
  obtain ⟨L', hL'⟩ := spec_exists_hodgeFiltered_comp_inclusion_aux X L q
  refine AddMonoidHom.mem_range.2
    ⟨hypercohomologyShift X (F^(q + 1) Ω•(X)) k (hypercohomologyMap X L' k β), ?_⟩
  rw [filteredToDeRhamCohomology, filteredToDeRhamCohomology,
    ← spec_hypercohomologyShift_hypercohomologyMap_aux]
  have h1 := hypercohomologyMap_comp_apply X L'
    ((hodgeFilteredDeRhamInclusion X (q + 1))⟦(1 : ℤ)⟧') k β
  have h2 := hypercohomologyMap_comp_apply X (hodgeFilteredDeRhamInclusion X q) L k β
  exact congrArg (hypercohomologyShift X Ω•(X) k)
    (h1.symm.trans ((congrArg (fun f => hypercohomologyMap X f k β) hL').trans h2))

end HodgeLean.Adapters
