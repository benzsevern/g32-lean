import HodgeLean.Adapters.CupFilteredDeRhamDefs

/-! # Open obligations of stage `CupFilteredDeRham`

One `_aux` obligation per statement of `CupFilteredDeRham.lean`, all open. The statements, their
sources and their falsification checks are in `docs/specs/CupFilteredDeRham.md`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.Foundations HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

set_option maxRecDepth 4000 in
theorem spec_cupProductOf_cup_eq_smul_transportedCup_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∃ c : ℚ, c ≠ 0 ∧ ∀ {i j k : ℕ} (h : i + j = k) (a : HQ X i) (b : HQ X j),
      (cupProductOf X).cup h a b =
        c • Foundations.Singular.transportedCup (TopCat.of (ComplexPoint X))
          (fun n => (HQ.linearEquiv X n).trans (rationalCohomologyLinearEquivSingular X n))
          h a b := by
  let := Foundations.pathConnectedSpace_complexPoint X
  let Y := TopCat.of (ComplexPoint X)
  let e : ∀ n, HQ X n ≃ₗ[ℚ] AlgebraicTopology.Singular.Cohomology ℚ Y n :=
    fun n => (HQ.linearEquiv X n).trans (rationalCohomologyLinearEquivSingular X n)
  let s : ℚ := Classical.choose (Foundations.Singular.exists_smul_unit Y (e 0 (cupUnit X)))
  have hs : s • Foundations.Singular.unit Y = e 0 (cupUnit X) :=
    Classical.choose_spec (Foundations.Singular.exists_smul_unit Y (e 0 (cupUnit X)))
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hs
    exact unitClass_ne_zero' X ((e 0).injective (hs.symm.trans (map_zero _).symm))
  have hcomp : ∀ n (a : HQ X n), cupComparison X n a = s⁻¹ • e n a := fun n a => rfl
  have hcomp' : ∀ n (a : HQ X n), e n a = s • cupComparison X n a := fun n a => by
    rw [hcomp, smul_smul, mul_inv_cancel₀ hs0, one_smul]
  refine ⟨s⁻¹, inv_ne_zero hs0, fun {i j k} h a b => ?_⟩
  show Foundations.Singular.transportedCup Y (cupComparison X) h a b =
    s⁻¹ • Foundations.Singular.transportedCup Y e h a b
  apply (e k).injective
  rw [map_smul, Foundations.Singular.map_transportedCup Y e, hcomp' k,
    Foundations.Singular.map_transportedCup, hcomp, hcomp, map_smul, LinearMap.map_smul₂,
    smul_smul, smul_smul, mul_inv_cancel₀ hs0, one_mul]

/-- Global sections preserve quasi-isomorphisms in degree `n` between complexes strictly `≥ n`:
there the degree-`n` homology is a kernel, and global sections preserve kernels. -/
lemma quasiIsoAt_globalSections_map_of_isStrictlyGE {Y : TopCat.{0}}
    {S T : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ} (n : ℤ) [S.IsStrictlyGE n]
    [T.IsStrictlyGE n] (f : S ⟶ T) [QuasiIsoAt f n] :
    QuasiIsoAt (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      Y).mapHomologicalComplex ℤᵘᵖ).map f) n := by
  let F := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  have hS : (S.sc n).f = 0 := (S.isZero_of_isStrictlyGE n _ (by simp)).eq_of_src _ _
  have hT : (T.sc n).f = 0 := (T.isZero_of_isStrictlyGE n _ (by simp)).eq_of_src _ _
  have := F.preservesLeftHomology_of_zero_f (S.sc n) hS
  have := F.preservesLeftHomology_of_zero_f (T.sc n) hT
  have h : QuasiIsoAt f n := inferInstance
  rw [quasiIsoAt_iff] at h ⊢
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology F
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f)

section

local instance cupf1HasDerivedCategory (X : Over (Spec ↧ℂ)) :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

theorem spec_globalSectionsToHypercohomology_bijective_of_isStrictlyGE_aux
    (X : Over (Spec ↧ℂ)) (S : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ)
    [S.IsStrictlyGE n] :
    Function.Bijective (globalSectionsToHypercohomology X S n) := by
  obtain ⟨I, i, _, _, _⟩ := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective S n
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I n
  have : QuasiIsoAt (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map i) n :=
    quasiIsoAt_globalSections_map_of_isStrictlyGE n i
  have hi : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X) ℤᵘᵖ i := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have hpost : Function.Bijective (hypercohomologyMap X i n) :=
    (Localization.SmallShiftedHom.postcompEquiv.{1} i hi (a := n)).bijective
  rw [← Function.Bijective.of_comp_iff' hpost]
  have hcomp : (hypercohomologyMap X i n) ∘ (globalSectionsToHypercohomology X S n) =
      (globalSectionsToHypercohomology X I n) ∘
        (HomologicalComplex.homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map i) n) := by
    funext x
    exact (globalSectionsToHypercohomology_naturality X i _ x).symm
  rw [hcomp]
  exact (globalSectionsToHypercohomology_bijective_of_isKInjective X I _).comp
    (ConcreteCategory.bijective_of_isIso _)

end

theorem spec_cycleForm_injective_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (p : ℕ) : Function.Injective (cycleForm X p) := by
  intro a b h
  have h1 := ((ConcreteCategory.bijective_of_isIso
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (filteredDeRhamXIso X p).hom))).1 h
  exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance h1

/-- The degree-`(p + 1)` term of `F^p Ω•` is the sheaf of holomorphic `(p + 1)`-forms.
Source: Mathlib's `HomologicalComplex.stupidTruncXIso` and `HomologicalComplex.extendXIso`. -/
def filteredDeRhamXSuccIso (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    (F^(p : ℤ) Ω•(X)).X ((p + 1 : ℕ) : ℤ) ≅ holomorphicDeRhamSheaf X (dim X.left) (p + 1) :=
  HomologicalComplex.stupidTruncXIso Ω•(X) (ComplexShape.embeddingUpIntGE (p : ℤ))
      (i := 1) (by simp) ≪≫
    (holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat
      (i := p + 1) rfl

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    (filteredDeRhamXSuccIso X p).hom ≫ (filteredDeRhamXSuccIso X p).inv = 𝟙 _ :=
  Iso.hom_inv_id _

set_option backward.isDefEq.respectTransparency false in
/-- Under `filteredDeRhamXIso` and `filteredDeRhamXSuccIso`, the differential of `F^p Ω•` from
degree `p` to degree `p + 1` is the exterior derivative. -/
lemma filteredDeRham_d_succ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    (F^(p : ℤ) Ω•(X)).d (p : ℤ) ((p + 1 : ℕ) : ℤ) =
      (filteredDeRhamXIso X p).hom ≫ holomorphicDeRhamSheafDifferential X (dim X.left) p ≫
        (filteredDeRhamXSuccIso X p).inv := by
  rw [← holomorphicDeRhamComplex_d]
  dsimp only [hodgeFilteredDeRhamComplex, HomologicalComplex.stupidTrunc,
    filteredDeRhamXIso, filteredDeRhamXSuccIso, HomologicalComplex.stupidTruncXIso]
  rw [HomologicalComplex.extend_d_eq _ _ (i := 0) (by simp) (j := 1) (by simp)]
  simp only [HomologicalComplex.restriction_d, Iso.trans_hom, Iso.trans_inv, Category.assoc]
  congr 1
  rw [show Ω•(X).d ((ComplexShape.embeddingUpIntGE (p : ℤ)).f 0)
      ((ComplexShape.embeddingUpIntGE (p : ℤ)).f 1) =
    ((holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat
      (i := p) rfl).hom ≫ (holomorphicDeRhamComplex X (dim X.left)).d p (p + 1) ≫
      ((holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat
      (i := p + 1) rfl).inv from HomologicalComplex.extend_d_eq _ _ rfl rfl]
  simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.assoc]
  rfl

theorem spec_range_cycleForm_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (p : ℕ) : (cycleForm X p).range = closedGlobalHolomorphicForms X p := by
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))
  let K := filteredGlobalSectionsOf X p
  have hd (y : K.X (p : ℤ)) : K.d (p : ℤ) ((p + 1 : ℕ) : ℤ) y =
      Γ.map (filteredDeRhamXSuccIso X p).inv
        (globalHolomorphicDifferential X p (Γ.map (filteredDeRhamXIso X p).hom y)) := by
    change Γ.map ((F^(p : ℤ) Ω•(X)).d (p : ℤ) ((p + 1 : ℕ) : ℤ)) y = _
    rw [filteredDeRham_d_succ, Γ.map_comp, Γ.map_comp]
    rfl
  have hinv (ω : GlobalHolomorphicForm X p) :
      Γ.map (filteredDeRhamXIso X p).hom (Γ.map (filteredDeRhamXIso X p).inv ω) = ω := by
    rw [← ConcreteCategory.comp_apply, ← Γ.map_comp, Iso.inv_hom_id, Γ.map_id,
      ConcreteCategory.id_apply]
  ext ω
  constructor
  · rintro ⟨z, rfl⟩
    change globalHolomorphicDifferential X p (cycleForm X p z) = 0
    have h0 := ConcreteCategory.congr_hom (K.iCycles_d (p : ℤ) ((p + 1 : ℕ) : ℤ)) z
    rw [ConcreteCategory.comp_apply, hd] at h0
    apply (ConcreteCategory.bijective_of_isIso (Γ.map (filteredDeRhamXSuccIso X p).inv)).1
    rw [map_zero]
    exact h0
  · intro hω
    let y : K.X (p : ℤ) := Γ.map (filteredDeRhamXIso X p).inv ω
    have hy : K.d (p : ℤ) ((p + 1 : ℕ) : ℤ) y = 0 := by
      rw [hd, hinv, show globalHolomorphicDifferential X p ω = 0 from hω, map_zero]
      rfl
    have hy' : y ∈ (K.sc (p : ℤ)).g.hom.ker := by
      change K.d _ ((ComplexShape.up ℤ).next (p : ℤ)) y = 0
      rw [show (ComplexShape.up ℤ).next (p : ℤ) = ((p + 1 : ℕ) : ℤ) by simp]
      exact hy
    refine ⟨(K.sc (p : ℤ)).abCyclesIso.inv ⟨y, hy'⟩, ?_⟩
    change Γ.map (filteredDeRhamXIso X p).hom
      ((K.sc (p : ℤ)).iCycles ((K.sc (p : ℤ)).abCyclesIso.inv ⟨y, hy'⟩)) = ω
    rw [ShortComplex.abCyclesIso_inv_apply_iCycles]
    exact hinv ω

/-- Homology equals cycles in degree `n` for `Γ(Y, S)` when `S` is strictly `≥ n`. -/
lemma isIso_globalSectionsComplexInt_homologyπ_of_isStrictlyGE {Y : TopCat.{0}}
    (S : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) (n : ℤ) [S.IsStrictlyGE n] :
    IsIso ((TopCat.Sheaf.globalSectionsComplexInt Y S).homologyπ n) :=
  HomologicalComplex.isIso_homologyπ _ (n - 1) n (by simp)
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).map_isZero
      (S.isZero_of_isStrictlyGE n (n - 1) (by lia))).eq_of_src _ _)

theorem spec_hodgeFiltration_eq_range_cycleFormDeRhamClass_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    (F^(p : ℤ) H_dR^(p : ℤ)(X)).toAddSubgroup = (cycleFormDeRhamClass X p).range := by
  have := isIso_globalSectionsComplexInt_homologyπ_of_isStrictlyGE
    (Y := TopCat.of (ComplexPoint X)) (F^(p : ℤ) Ω•(X)) (p : ℤ)
  have hs : Function.Surjective
      ((globalSectionsToHypercohomology X (F^(p : ℤ) Ω•(X)) (p : ℤ)).comp
        ((filteredGlobalSectionsOf X p).homologyπ (p : ℤ)).hom) :=
    (spec_globalSectionsToHypercohomology_bijective_of_isStrictlyGE_aux X
      (F^(p : ℤ) Ω•(X)) (p : ℤ)).2.comp (ConcreteCategory.bijective_of_isIso _).2
  ext α
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hs y
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, rfl⟩

section LaneB

attribute [local instance] chartFieldModule chartFieldTower

open CliffordAlgebra (involute involute_ι) in
theorem laneB_ι_mul_eq_involute_mul_ι {A : Type} [CommRing A] [Algebra ℂ A]
    (m : Ω[A⁄ℂ]) (y : Algebra.DeRham.ExtAlg ℂ A) :
    ExteriorAlgebra.ι A m * y = involute y * ExteriorAlgebra.ι A m := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap a => rw [AlgHom.commutes, Algebra.commutes]
  | ι n =>
      rw [involute_ι, neg_mul, eq_neg_iff_add_eq_zero]
      exact ExteriorAlgebra.ι_add_mul_swap m n
  | mul y z hy hz => rw [← mul_assoc, hy, mul_assoc, hz, ← mul_assoc, map_mul]
  | add y z hy hz => rw [mul_add, hy, hz, map_add, add_mul]

theorem laneB_ι_mul_mem {A : Type} [CommRing A] [Algebra ℂ A] (k : ℕ) (m : Ω[A⁄ℂ])
    (w : Algebra.DeRham.Form ℂ A k) :
    ExteriorAlgebra.ι A m * (w : Algebra.DeRham.ExtAlg ℂ A) ∈ ⋀[A]^(k + 1) Ω[A⁄ℂ] := by
  rw [ExteriorAlgebra.exteriorPower, pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ m) w.2

theorem laneB_chartEvaluationHolo_ιMulti (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ) (m : Fin p → Ω[OpenHolomorphicFunctions X d U⁄ℂ])
    (y : ↥(chartSectionDomain X d U z)) :
    chartEvaluationHolo X d U z p (exteriorPower.ιMulti _ p m) y =
      ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ)
        (fun i => (chartDerivation X d U z).liftKaehlerDifferential (m i) y) := by
  rw [chartEvaluationHolo, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem laneB_chartEvaluationHolo_ι_mul (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (k : ℕ) (m : Ω[OpenHolomorphicFunctions X d U⁄ℂ])
    (w : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) k)
    (y : ↥(chartSectionDomain X d U z)) :
    chartEvaluationHolo X d U z (k + 1) ⟨_, laneB_ι_mul_mem k m w⟩ y =
      ContinuousAlternatingMap.alternatizeUncurryFin
        (((chartDerivation X d U z).liftKaehlerDifferential m y).smulRight
          (chartEvaluationHolo X d U z k w y)) := by
  have hw : w ∈ Submodule.span (OpenHolomorphicFunctions X d U)
      (Set.range (exteriorPower.ιMulti (OpenHolomorphicFunctions X d U) k)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨n, rfl⟩ := hw
      have he : (⟨_, laneB_ι_mul_mem k m (exteriorPower.ιMulti _ k n)⟩ :
          Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) (k + 1)) =
          exteriorPower.ιMulti _ (k + 1) (Fin.cons m n) := by
        apply Subtype.ext
        simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
        rfl
      rw [he, laneB_chartEvaluationHolo_ιMulti, laneB_chartEvaluationHolo_ιMulti,
        ContinuousAlternatingMap.wedgeCovectors_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
  | zero =>
      have he : (⟨_, laneB_ι_mul_mem k m 0⟩ :
          Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) (k + 1)) = 0 :=
        Subtype.ext (by simp)
      rw [he, map_zero, map_zero]
      ext v
      simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  | add a b _ _ ha hb =>
      have he : (⟨_, laneB_ι_mul_mem k m (a + b)⟩ :
          Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) (k + 1)) =
          ⟨_, laneB_ι_mul_mem k m a⟩ + ⟨_, laneB_ι_mul_mem k m b⟩ :=
        Subtype.ext (by simp [mul_add])
      rw [he, map_add, map_add, Pi.add_apply, Pi.add_apply, ha, hb,
        ← ContinuousAlternatingMap.alternatizeUncurryFin_add]
      congr 1
      ext u
      simp [smul_add]
  | smul a w _ hw =>
      have he : (⟨_, laneB_ι_mul_mem k m (a • w)⟩ :
          Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) (k + 1)) =
          a • ⟨_, laneB_ι_mul_mem k m w⟩ :=
        Subtype.ext (by simp)
      rw [he, map_smul, map_smul, chartFieldModule_smul_apply, chartFieldModule_smul_apply, hw,
        ← ContinuousAlternatingMap.alternatizeUncurryFin_smul]
      congr 1
      ext1 u
      rw [ContinuousLinearMap.smulRight_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, smul_comm]


theorem laneB_vanish_congr (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (y : ↥(chartSectionDomain X d U z)) {k k' : ℕ}
    {w w' : Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U)} (hk : k = k')
    (hww : w = w')
    (hw : ∃ hw : w ∈ ⋀[OpenHolomorphicFunctions X d U]^k Ω[OpenHolomorphicFunctions X d U⁄ℂ],
      chartEvaluationHolo X d U z k ⟨w, hw⟩ y = 0) :
    ∃ hw : w' ∈ ⋀[OpenHolomorphicFunctions X d U]^k' Ω[OpenHolomorphicFunctions X d U⁄ℂ],
      chartEvaluationHolo X d U z k' ⟨w', hw⟩ y = 0 := by
  subst hk hww
  exact hw

/-- Left multiplication by a `1`-form keeps the vanishing of the evaluation at a point. -/
theorem laneB_vanish_ι_mul (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (y : ↥(chartSectionDomain X d U z)) (k : ℕ)
    (m : Ω[OpenHolomorphicFunctions X d U⁄ℂ])
    {w : Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U)}
    (hw : ∃ hw : w ∈ ⋀[OpenHolomorphicFunctions X d U]^k Ω[OpenHolomorphicFunctions X d U⁄ℂ],
      chartEvaluationHolo X d U z k ⟨w, hw⟩ y = 0) :
    ∃ h : ExteriorAlgebra.ι _ m * w ∈
        ⋀[OpenHolomorphicFunctions X d U]^(k + 1) Ω[OpenHolomorphicFunctions X d U⁄ℂ],
      chartEvaluationHolo X d U z (k + 1) ⟨_, h⟩ y = 0 := by
  obtain ⟨hw, h0⟩ := hw
  refine ⟨laneB_ι_mul_mem k m ⟨w, hw⟩, ?_⟩
  rw [laneB_chartEvaluationHolo_ι_mul X d U z k m ⟨w, hw⟩ y, h0]
  ext v
  simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply]

theorem laneB_vanish_ιMulti_mul (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (y : ↥(chartSectionDomain X d U z)) (k : ℕ) :
    ∀ (j : ℕ) (n : Fin j → Ω[OpenHolomorphicFunctions X d U⁄ℂ])
      {w : Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U)},
      (∃ hw : w ∈ ⋀[OpenHolomorphicFunctions X d U]^k Ω[OpenHolomorphicFunctions X d U⁄ℂ],
        chartEvaluationHolo X d U z k ⟨w, hw⟩ y = 0) →
      ∃ h : ExteriorAlgebra.ιMulti _ j n * w ∈
          ⋀[OpenHolomorphicFunctions X d U]^(j + k) Ω[OpenHolomorphicFunctions X d U⁄ℂ],
        chartEvaluationHolo X d U z (j + k) ⟨_, h⟩ y = 0
  | 0, n, w, hw =>
      laneB_vanish_congr X d U z y (zero_add k).symm
        (by rw [ExteriorAlgebra.ιMulti_zero_apply, one_mul]) hw
  | j + 1, n, w, hw => by
      have ih := laneB_vanish_ιMulti_mul X d U z y k j (Matrix.vecTail n) hw
      have h2 := laneB_vanish_ι_mul X d U z y (j + k) (n 0) ih
      exact laneB_vanish_congr X d U z y (by omega)
        (by rw [ExteriorAlgebra.ιMulti_succ_apply, mul_assoc]) h2

open CliffordAlgebra (involute involute_ι) in
theorem laneB_ιMulti_mul_comm_of_even {A : Type} [CommRing A] [Algebra ℂ A]
    (e : Algebra.DeRham.ExtAlg ℂ A) (he : involute e = e) :
    ∀ (j : ℕ) (n : Fin j → Ω[A⁄ℂ]),
      ExteriorAlgebra.ιMulti A j n * e = e * ExteriorAlgebra.ιMulti A j n
  | 0, n => by simp [ExteriorAlgebra.ιMulti_zero_apply]
  | j + 1, n => by
      rw [ExteriorAlgebra.ιMulti_succ_apply, mul_assoc,
        laneB_ιMulti_mul_comm_of_even e he j, ← mul_assoc,
        laneB_ι_mul_eq_involute_mul_ι, he, mul_assoc]

open CliffordAlgebra (involute involute_ι) in
/-- The exterior derivative of a wedge of `1`-forms vanishes at a point if the derivatives of the
factors do (the Leibniz rule). -/
theorem laneB_vanish_extDeriv_ιMulti (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (y : ↥(chartSectionDomain X d U z)) :
    ∀ (p : ℕ) (m : Fin p → Ω[OpenHolomorphicFunctions X d U⁄ℂ]),
      (∀ i, ∃ h : Algebra.DeRham.extDeriv ℂ _ (ExteriorAlgebra.ι _ (m i)) ∈
          ⋀[OpenHolomorphicFunctions X d U]^2 Ω[OpenHolomorphicFunctions X d U⁄ℂ],
        chartEvaluationHolo X d U z 2 ⟨_, h⟩ y = 0) →
      ∃ h : Algebra.DeRham.extDeriv ℂ _ (ExteriorAlgebra.ιMulti _ p m) ∈
          ⋀[OpenHolomorphicFunctions X d U]^(p + 1) Ω[OpenHolomorphicFunctions X d U⁄ℂ],
        chartEvaluationHolo X d U z (p + 1) ⟨_, h⟩ y = 0
  | 0, m, _ => by
      have h1 : Algebra.DeRham.extDeriv ℂ (OpenHolomorphicFunctions X d U)
          (ExteriorAlgebra.ιMulti _ 0 m) = 0 := by
        rw [ExteriorAlgebra.ιMulti_zero_apply, ← map_one (algebraMap (OpenHolomorphicFunctions X d U)
          (Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U))),
          Algebra.DeRham.extDeriv_algebraMap, Derivation.map_one_eq_zero, map_zero]
      rw [h1]
      refine ⟨Submodule.zero_mem _, ?_⟩
      have h0 : (⟨0, Submodule.zero_mem _⟩ : Algebra.DeRham.Form ℂ
          (OpenHolomorphicFunctions X d U) (0 + 1)) = 0 := rfl
      rw [h0, map_zero]
      rfl
  | p + 1, m, hm => by
      obtain ⟨h1, e1⟩ := laneB_vanish_extDeriv_ιMulti X d U z y p (Matrix.vecTail m)
        (fun i => hm i.succ)
      obtain ⟨ha, ea⟩ := laneB_vanish_ι_mul X d U z y (p + 1) (m 0) ⟨h1, e1⟩
      have heven : involute (Algebra.DeRham.extDeriv ℂ (OpenHolomorphicFunctions X d U)
          (ExteriorAlgebra.ι _ (m 0))) =
          Algebra.DeRham.extDeriv ℂ _ (ExteriorAlgebra.ι _ (m 0)) := by
        rw [Algebra.DeRham.extDeriv_ι, Algebra.DeRham.involute_snd_phi]
      have hb := laneB_vanish_congr X d U z y (show p + 2 = p + 1 + 1 by omega)
        (laneB_ιMulti_mul_comm_of_even _ heven p (Matrix.vecTail m))
        (laneB_vanish_ιMulti_mul X d U z y 2 p (Matrix.vecTail m) (hm 0))
      obtain ⟨hb, eb⟩ := hb
      have hsum : Algebra.DeRham.extDeriv ℂ (OpenHolomorphicFunctions X d U)
          (ExteriorAlgebra.ιMulti _ (p + 1) m) =
          -(ExteriorAlgebra.ι _ (m 0) * Algebra.DeRham.extDeriv ℂ _
              (ExteriorAlgebra.ιMulti _ p (Matrix.vecTail m))) +
            Algebra.DeRham.extDeriv ℂ _ (ExteriorAlgebra.ι _ (m 0)) *
              ExteriorAlgebra.ιMulti _ p (Matrix.vecTail m) := by
        rw [ExteriorAlgebra.ιMulti_succ_apply, Algebra.DeRham.extDeriv_mul, involute_ι, neg_mul]
      rw [hsum]
      refine ⟨Submodule.add_mem _ (Submodule.neg_mem _ ha) hb, ?_⟩
      have hsplit : (⟨_, Submodule.add_mem _ (Submodule.neg_mem _ ha) hb⟩ :
          Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) (p + 1 + 1)) =
          -⟨_, ha⟩ + ⟨_, hb⟩ := rfl
      rw [hsplit, map_add, map_neg, Pi.add_apply, Pi.neg_apply, ea, eb, neg_zero, zero_add]

open scoped Manifold in
/-- A section of `Ω^p` on an open `V` whose values vanish at every point of `V` is zero. -/
theorem laneB_section_eq_zero (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ℕ) (V : Opens (TopCat.of (ComplexPoint X)))
    (s : (holomorphicDeRhamSheaf X d p).presheaf.obj (op V))
    (hs : ∀ y (hy : y ∈ V),
      formStalkValue X d y p ((holomorphicDeRhamSheaf X d p).presheaf.germ V y hy s) = 0) :
    s = 0 := by
  apply TopCat.Presheaf.section_ext (holomorphicDeRhamSheaf X d p) V s 0
  intro x hxV
  have hS := Presheaf.imageSieve_mem (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d p)) s
  obtain ⟨W, f, ⟨t, ht⟩, hxW⟩ := hS x hxV
  obtain ⟨ω, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  have ht' : (holomorphicDeRhamSheaf X d p).presheaf.map f.op s =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app (op W) (Submodule.Quotient.mk ω) := ht.symm
  have hmk : (Submodule.Quotient.mk ω : HolomorphicForm X d (op W) p) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero, mem_chartEvaluationKernel_iff]
    intro z y hy
    have hx'W : (extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y ∈ W := hy.2
    rw [chartEvaluation_fixedChartTransition X d (op W)
      ((extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y) z p ω hy (mem_extChartAt_source _)]
    have h0 := hs ((extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y) (f.le hx'W)
    rw [← TopCat.Presheaf.germ_res_apply _ f _ hx'W, ht',
      spec_formStalkValue_germ_toSheafify] at h0
    change (chartEvaluation X d (op W) _ p ω (extChartAt 𝓘(ℂ, Fin d → ℂ)
      ((extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y) ((extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y))).compContinuousLinearMap
        _ = 0
    rw [h0]
    exact ContinuousAlternatingMap.ext fun v ↦ by
      simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hgerm : (holomorphicDeRhamSheaf X d p).presheaf.germ V x hxV s =
      (holomorphicDeRhamSheaf X d p).presheaf.germ W x hxW
        ((holomorphicDeRhamSheaf X d p).presheaf.map f.op s) :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  rw [hgerm, ht', hmk, map_zero]
  erw [map_zero, map_zero]

/-- Two sections of `Ω^p` on `V` with the same values at every point of `V` are equal. -/
theorem laneB_section_eq (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ℕ) (V : Opens (TopCat.of (ComplexPoint X)))
    (s t : (holomorphicDeRhamSheaf X d p).presheaf.obj (op V))
    (hst : ∀ y (hy : y ∈ V),
      formStalkValue X d y p ((holomorphicDeRhamSheaf X d p).presheaf.germ V y hy s) =
        formStalkValue X d y p ((holomorphicDeRhamSheaf X d p).presheaf.germ V y hy t)) :
    s = t := by
  rw [← sub_eq_zero]
  refine laneB_section_eq_zero X d p V _ fun y hy => ?_
  rw [map_sub, map_sub, hst y hy, sub_self]

/-- Restricting the sheafification of a presheaf form restricts the form. -/
theorem laneB_map_toSheafify_mk (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ℕ) {U W : Opens (TopCat.of (ComplexPoint X))} (hWU : W ≤ U)
    (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) p) :
    (holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE hWU).op
        ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d p)).app (op U) (Submodule.Quotient.mk ω)) =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d p)).app (op W)
        (Submodule.Quotient.mk (formRestriction X d (homOfLE hWU).op p ω)) := by
  have h := ConcreteCategory.congr_hom
    ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d p)).naturality (homOfLE hWU).op)
    (Submodule.Quotient.mk ω : HolomorphicForm X d (op U) p)
  exact h.symm

/-- The differential of a global form represented on `W` by `ω` is represented by `dω`. -/
theorem laneB_map_differential (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ℕ) (W : Opens (TopCat.of (ComplexPoint X)))
    (σ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤))
    (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op W)) p)
    (hω : (holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE le_top).op σ =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app (op W) (Submodule.Quotient.mk ω)) :
    (holomorphicDeRhamSheaf X d (p + 1)).presheaf.map (homOfLE le_top).op
        ((holomorphicDeRhamSheafDifferential X d p).hom.app (op ⊤) σ) =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d (p + 1))).app (op W)
        (Submodule.Quotient.mk (Algebra.DeRham.differential ℂ _ p ω)) := by
  have h1 := ConcreteCategory.congr_hom
    ((holomorphicDeRhamSheafDifferential X d p).hom.naturality (homOfLE (le_top (a := W))).op) σ
  simp only [ConcreteCategory.comp_apply] at h1
  rw [← h1, hω]
  have h2 := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamDifferential X d p)) (op W))
    (Submodule.Quotient.mk ω : HolomorphicForm X d (op W) p)
  simp only [NatTrans.comp_app] at h2
  exact h2.symm

/-- Near each point, `p` global `1`-forms are represented on one open by Kähler `1`-forms
`ι mᵢ`. -/
theorem laneB_exists_local_oneForms (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : Fin p → (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (x : ComplexPoint X) :
    ∃ (W : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ W)
      (m : Fin p → Ω[OpenHolomorphicFunctions X d (op W)⁄ℂ]), ∀ i,
      (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op (θ i) =
        (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d 1)).app (op W)
          (Submodule.Quotient.mk (exteriorPower.ιMulti _ 1 fun _ => m i)) := by
  choose U hxU ω hω using fun i => spec_exists_local_representative X d 1 (θ i) x
  let W : Opens (TopCat.of (ComplexPoint X)) :=
    ⟨⋂ i, (U i : Set (ComplexPoint X)), isOpen_iInter_of_finite fun i => (U i).isOpen⟩
  have hWU : ∀ i, W ≤ U i := fun i => Set.iInter_subset _ i
  have hxW : x ∈ W := Set.mem_iInter.2 hxU
  have hm : ∀ i, ∃ m : Ω[OpenHolomorphicFunctions X d (op W)⁄ℂ],
      formRestriction X d (homOfLE (hWU i)).op 1 (ω i) =
        exteriorPower.ιMulti _ 1 fun _ => m := by
    intro i
    refine ⟨exteriorPower.oneEquiv _ _ (formRestriction X d (homOfLE (hWU i)).op 1 (ω i)), ?_⟩
    rw [← exteriorPower.oneEquiv_symm_apply, LinearEquiv.symm_apply_apply]
  choose m hm using hm
  refine ⟨W, hxW, m, fun i => ?_⟩
  rw [← hm i, ← laneB_map_toSheafify_mk X d 1 (hWU i), ← hω i]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem laneB_ofSubsingleton_symm_wedgeCovectors {d : ℕ} (L : Fin 1 → (Fin d → ℂ) →L[ℂ] ℂ) :
    (ContinuousAlternatingMap.ofSubsingleton ℂ (Fin d → ℂ) ℂ (0 : Fin 1)).symm
      (ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) L) = L 0 := by
  ext u
  change ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) L (fun _ => u) = L 0 u
  rw [ContinuousAlternatingMap.wedgeCovectors_apply_eq_det, Matrix.det_unique]
  rfl

open scoped Manifold in
/-- The value at a point of `W` of the sheafified wedge of local representatives is the wedge of
the covectors of the global `1`-forms. -/
theorem laneB_formStalkValue_wedge (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : Fin p → (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (W : Opens (TopCat.of (ComplexPoint X)))
    (m : Fin p → Ω[OpenHolomorphicFunctions X d (op W)⁄ℂ])
    (hm : ∀ i, (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op (θ i) =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d 1)).app (op W)
        (Submodule.Quotient.mk (exteriorPower.ιMulti _ 1 fun _ => m i)))
    (y : ComplexPoint X) (hy : y ∈ W) :
    formStalkValue X d y p ((holomorphicDeRhamSheaf X d p).presheaf.germ W y hy
      ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app (op W)
        (Submodule.Quotient.mk (exteriorPower.ιMulti _ p m)))) =
      ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ)
        (fun i => globalOneFormCovector X d (θ i) y) := by
  have hmem := extChartAt_self_mem_chartSectionDomain X d (op W) hy
  rw [spec_formStalkValue_germ_toSheafify]
  change extendByZero X d (op W) y _ _ = _
  rw [extendByZero_apply_of_mem X d (op W) y _ hmem, LinearMap.restrictScalars_apply,
    laneB_chartEvaluationHolo_ιMulti]
  congr 1
  funext i
  rw [globalOneFormCovector, globalFormValue_eq_chartEvaluation_self X d 1 (θ i) W _ (hm i) y hy]
  symm
  change (ContinuousAlternatingMap.ofSubsingleton ℂ (Fin d → ℂ) ℂ (0 : Fin 1)).symm
    (extendByZero X d (op W) y _ _) = _
  rw [extendByZero_apply_of_mem X d (op W) y _ hmem, LinearMap.restrictScalars_apply,
    laneB_chartEvaluationHolo_ιMulti, laneB_ofSubsingleton_symm_wedgeCovectors]

theorem spec_exists_globalFormValue_eq_wedgeCovectors_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : Fin p → (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) :
    ∃ ζ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤), ∀ x : ComplexPoint X,
      globalFormValue X d p x ζ =
        ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ)
          (fun i => globalOneFormCovector X d (θ i) x) := by
  choose W hxW m hm using laneB_exists_local_oneForms X d p θ
  let sf : ∀ x : ComplexPoint X, (holomorphicDeRhamSheaf X d p).presheaf.obj (op (W x)) :=
    fun x => (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d p)).app (op (W x))
      (Submodule.Quotient.mk (exteriorPower.ιMulti _ p (m x)))
  have hcompat : TopCat.Presheaf.IsCompatible (holomorphicDeRhamSheaf X d p).presheaf W sf := by
    intro a b
    apply laneB_section_eq X d p
    intro y hy
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      laneB_formStalkValue_wedge X d p θ (W a) (m a) (hm a),
      laneB_formStalkValue_wedge X d p θ (W b) (m b) (hm b)]
  obtain ⟨ζ, hζ, -⟩ := TopCat.Sheaf.existsUnique_gluing' (holomorphicDeRhamSheaf X d p) W ⊤
    (fun x => homOfLE le_top) (fun y _ => Opens.mem_iSup.2 ⟨y, hxW y⟩) sf hcompat
  refine ⟨ζ, fun x => ?_⟩
  have hgerm : (holomorphicDeRhamSheaf X d p).presheaf.germ ⊤ x trivial ζ =
      (holomorphicDeRhamSheaf X d p).presheaf.germ (W x) x (hxW x)
        ((holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE le_top).op ζ) :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  have hζx : (holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE le_top).op ζ = sf x := hζ x
  change formStalkValue X d x p ((holomorphicDeRhamSheaf X d p).presheaf.germ ⊤ x trivial ζ) = _
  rw [hgerm, hζx]
  exact laneB_formStalkValue_wedge X d p θ (W x) (m x) (hm x) x (hxW x)

open scoped Manifold in
theorem spec_differential_eq_zero_of_globalFormValue_eq_wedgeCovectors_aux (X : Over (Spec ↧ℂ))
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : Fin p → (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (hθ : ∀ i, (holomorphicDeRhamSheafDifferential X d 1).hom.app (op ⊤) (θ i) = 0)
    (ζ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤))
    (hζ : ∀ x : ComplexPoint X, globalFormValue X d p x ζ =
      ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ)
        (fun i => globalOneFormCovector X d (θ i) x)) :
    (holomorphicDeRhamSheafDifferential X d p).hom.app (op ⊤) ζ = 0 := by
  apply spec_eq_zero_of_globalFormValue_eq_zero X d (p + 1)
  intro x
  obtain ⟨W, hxW, m, hm⟩ := laneB_exists_local_oneForms X d p θ x
  have hloc : (holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE le_top).op ζ =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app (op W)
        (Submodule.Quotient.mk (exteriorPower.ιMulti _ p m)) := by
    apply laneB_section_eq X d p
    intro y hy
    rw [TopCat.Presheaf.germ_res_apply, laneB_formStalkValue_wedge X d p θ W m hm y hy]
    exact hζ y
  have hmem := extChartAt_self_mem_chartSectionDomain X d (op W) hxW
  have hval : ∀ (q : ℕ) (σ : (holomorphicDeRhamSheaf X d q).presheaf.obj (op ⊤))
      (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op W)) q),
      (holomorphicDeRhamSheaf X d q).presheaf.map (homOfLE le_top).op σ =
        (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d q)).app (op W) (Submodule.Quotient.mk ω) →
      globalFormValue X d (q + 1) x ((holomorphicDeRhamSheafDifferential X d q).hom.app (op ⊤) σ) =
        chartEvaluationHolo X d (op W) x (q + 1) (Algebra.DeRham.differential ℂ _ q ω)
          ⟨_, hmem⟩ := by
    intro q σ ω hσ
    rw [globalFormValue_eq_chartEvaluation_self X d (q + 1) _ W _
      (laneB_map_differential X d q W σ ω hσ) x hxW]
    change extendByZero X d (op W) x _ _ = _
    rw [extendByZero_apply_of_mem X d (op W) x _ hmem, LinearMap.restrictScalars_apply]
  rw [hval p ζ _ hloc]
  have hfac : ∀ i, ∃ h : Algebra.DeRham.extDeriv ℂ _ (ExteriorAlgebra.ι _ (m i)) ∈
      ⋀[OpenHolomorphicFunctions X d (op W)]^2 Ω[OpenHolomorphicFunctions X d (op W)⁄ℂ],
      chartEvaluationHolo X d (op W) x 2 ⟨_, h⟩ ⟨_, hmem⟩ = 0 := by
    intro i
    have h0 := hval 1 (θ i) _ (hm i)
    rw [hθ i, map_zero] at h0
    refine laneB_vanish_congr X d (op W) x ⟨_, hmem⟩ rfl ?_ ⟨_, h0.symm⟩
    rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  exact (laneB_vanish_extDeriv_ιMulti X d (op W) x ⟨_, hmem⟩ p m hfac).choose_spec

theorem spec_exists_cycleForm_eq_wedge_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (p : ℕ) (θ : Fin p → GlobalHolomorphicForm X 1)
    (hθ : ∀ i, θ i ∈ closedGlobalHolomorphicOneForms X) :
    ∃ z : (filteredGlobalSectionsOf X p).cycles (p : ℤ), ∀ x : ComplexPoint X,
      globalFormValue X (dim X.left) p x (cycleForm X p z) =
        ContinuousAlternatingMap.wedgeCovectors ℂ (Fin (dim X.left) → ℂ)
          (fun i => globalOneFormCovector X (dim X.left) (θ i) x) := by
  obtain ⟨ζ, hζ⟩ := spec_exists_globalFormValue_eq_wedgeCovectors_aux X (dim X.left) p θ
  have hd := spec_differential_eq_zero_of_globalFormValue_eq_wedgeCovectors_aux X (dim X.left) p
    θ (fun i => hθ i) ζ hζ
  have hmem : ζ ∈ closedGlobalHolomorphicForms X p := hd
  rw [← spec_range_cycleForm_aux X p] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, fun x => by rw [hz]; exact hζ x⟩

end LaneB

theorem spec_cupMultiC_comp_perm_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X} (hT : TorusCohomology μ) (n : ℕ)
    (v : Fin n → ℂ ⊗[ℚ] HQ X 1) (σ : Equiv.Perm (Fin n)) :
    μ.cupMultiC n (v ∘ σ) = Equiv.Perm.sign σ • μ.cupMultiC n v := by
  have h₁ := hT.complexificationCongr_symm_ιMulti n (v ∘ σ)
  have h₂ := hT.complexificationCongr_symm_ιMulti n v
  rw [← h₁, ← h₂, AlternatingMap.map_perm, Units.smul_def, Units.smul_def, map_zsmul, map_zsmul]

/-- With `hL`, a cup of degree-one classes lies in `F^c`, where `c` counts the factors `v i` with
`p i = 1`, each of which lies in `F^1`. -/
theorem bettiDeRhamHQ_cupMultiC_mem_count_of_cupLeft {X : Over (Spec ↧ℂ)} [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X)) :
    ∀ (n : ℕ) (v : Fin n → ℂ ⊗[ℚ] HQ X 1) (p : Fin n → ℤ),
      (∀ i, p i = 1 → bettiDeRhamHQ X 1 (v i) ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X)) →
      bettiDeRhamHQ X n (μ.cupMultiC n v) ∈
        F^(∑ i, if p i = 1 then (1 : ℤ) else 0) H_dR^(n : ℤ)(X)
  | 0, v, p, _ => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rw [hodgeFiltration_eq_top_of_nonpos X le_rfl]
    exact Submodule.mem_top
  | n + 1, v, p, hv => by
    have hfront : ∀ (v : Fin (n + 1) → ℂ ⊗[ℚ] HQ X 1) (p : Fin (n + 1) → ℤ),
        (∀ i, p i = 1 → bettiDeRhamHQ X 1 (v i) ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X)) → p 0 = 1 →
        bettiDeRhamHQ X (n + 1) (μ.cupMultiC (n + 1) v) ∈
          F^(∑ i, if p i = 1 then (1 : ℤ) else 0) H_dR^((n + 1 : ℕ) : ℤ)(X) := by
      intro v p hv h0
      rw [CupProduct.cupMultiC_succ, Fin.sum_univ_succ, ite_eq_left_of_eq_true _ _ (eq_true h0)]
      exact hL (Nat.add_comm 1 n) _ (v 0) _ (hv 0 h0)
        (bettiDeRhamHQ_cupMultiC_mem_count_of_cupLeft hT hL n (Fin.tail v) (Fin.tail p)
          fun i hi => hv i.succ hi)
    by_cases h0 : p 0 = 1
    · exact hfront v p hv h0
    by_cases hex : ∃ j, p j = 1
    · obtain ⟨j, hj⟩ := hex
      have hj0 : (0 : Fin (n + 1)) ≠ j := by rintro rfl; exact h0 hj
      have hsum : (∑ i, if (p ∘ Equiv.swap 0 j) i = 1 then (1 : ℤ) else 0) =
          ∑ i, if p i = 1 then (1 : ℤ) else 0 :=
        Equiv.sum_comp (Equiv.swap 0 j) (fun i => if p i = 1 then (1 : ℤ) else 0)
      have h := hfront (v ∘ Equiv.swap 0 j) (p ∘ Equiv.swap 0 j) (fun i hi => hv _ hi)
        (by simpa using hj)
      rw [hsum, spec_cupMultiC_comp_perm_aux X hT, Equiv.Perm.sign_swap hj0, Units.neg_smul,
        one_smul, map_neg] at h
      simpa using neg_mem h
    · simp only [not_exists] at hex
      simp only [hex, ↓reduceIte, Finset.sum_const_zero]
      rw [hodgeFiltration_eq_top_of_nonpos X le_rfl]
      exact Submodule.mem_top

theorem spec_bettiDeRhamHQ_cupMultiC_mem_of_cupLeft_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (n : ℕ) (v : Fin n → ℂ ⊗[ℚ] HQ X 1) (p : Fin n → ℤ)
    (hv : ∀ i, bettiDeRhamHQ X 1 (v i) ∈ F^(p i) H_dR^((1 : ℕ) : ℤ)(X)) :
    bettiDeRhamHQ X n (μ.cupMultiC n v) ∈ F^(∑ i, p i) H_dR^(n : ℤ)(X) := by
  by_cases hbig : ∃ i, 2 ≤ p i
  · obtain ⟨i, hi⟩ := hbig
    have h0 : v i = 0 := by
      have := hv i
      rw [hodgeFiltration_eq_bot_of_lt X (by lia : ((1 : ℕ) : ℤ) < p i)] at this
      exact ((HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X).bijective 1).1
        (by rw [(Submodule.mem_bot ℂ).mp this, map_zero])
    rw [(μ.cupMultiC n).map_coord_zero i h0, map_zero]
    exact Submodule.zero_mem _
  · simp only [not_exists, not_le] at hbig
    refine hodgeFiltration_antitone X n (Finset.sum_le_sum fun i _ => ?_)
      (bettiDeRhamHQ_cupMultiC_mem_count_of_cupLeft hT hL n v p fun i hi => by
        rw [← hi]; exact hv i)
    have := hbig i
    split_ifs with h <;> lia

theorem spec_cupWedgePiece_le_deRhamHodgePiece_of_cupLeft_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (n : ℕ) (pq : ℤ × ℤ) :
    cupWedgePiece X μ n pq ≤ deRhamHodgePiece X n pq := by
  by_cases hpq : pq.1 + pq.2 = n
  · rw [cupWedgePiece, Submodule.span_le]
    rintro _ ⟨d, v, rfl, hv, rfl⟩
    by_cases hall : ∀ i, (d i).1 + (d i).2 = ((1 : ℕ) : ℤ)
    · simp only [SetLike.mem_coe, deRhamHodgePiece, hpq, ↓reduceIte]
      have hv' : ∀ i, bettiDeRhamHQ X 1 (v i) ∈ hodgePiece X (d i).1 (d i).2 1 := fun i => by
        have := hv i
        simp only [cohomologyHodgePiece, hall i, ↓reduceIte, Submodule.mem_comap] at this
        exact this
      refine ⟨spec_bettiDeRhamHQ_cupMultiC_mem_of_cupLeft_aux X hT hL n v (fun i => (d i).1)
        fun i => (hv' i).1, ?_⟩
      rw [SetLike.mem_coe, CupFiltered.mem_conj_iff, sigmaQ_cupMultiC]
      exact spec_bettiDeRhamHQ_cupMultiC_mem_of_cupLeft_aux X hT hL n _ (fun i => (d i).2)
        fun i => (CupFiltered.mem_conj_iff 1 _ _).mp (hv' i).2
    · obtain ⟨i, hi⟩ := not_forall.mp hall
      have := hv i
      simp only [cohomologyHodgePiece, hi, ↓reduceIte] at this
      rw [SetLike.mem_coe, (μ.cupMultiC n).map_coord_zero i ((Submodule.mem_bot ℂ).mp this),
        map_zero]
      exact Submodule.zero_mem _
  · rw [spec_cupWedgePiece_eq_bot X μ n pq hpq]
    exact bot_le

/-- Linear algebra behind the filtration from opposedness: if an internal family `W` on the line
`p + q = n` has `W (p, q) ≤ F p ⊓ G q` for antitone `F`, `G` with `F p ⊓ G (n + 1 - p) = ⊥`, then
`F p` is the sum of the pieces `W (p', n - p')` with `p ≤ p'`. -/
theorem eq_iSup_of_opposed {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (n : ℤ) {W : ℤ × ℤ → Submodule R M} (hW : DirectSum.IsInternal W)
    (hW0 : ∀ pq : ℤ × ℤ, pq.1 + pq.2 ≠ n → W pq = ⊥) {F G : ℤ → Submodule R M}
    (hF : Antitone F) (hG : Antitone G) (hle : ∀ pq : ℤ × ℤ, W pq ≤ F pq.1 ⊓ G pq.2)
    (hopp : ∀ p : ℤ, F p ⊓ G (n + 1 - p) = ⊥) (p : ℤ) :
    F p = ⨆ (p' : ℤ) (_ : p ≤ p'), W (p', n - p') := by
  have hBF : (⨆ (p' : ℤ) (_ : p ≤ p'), W (p', n - p')) ≤ F p :=
    iSup₂_le fun p' hp' => (hle _).trans (inf_le_left.trans (hF hp'))
  refine le_antisymm ?_ hBF
  set A : Submodule R M := ⨆ (p' : ℤ) (_ : p' < p), W (p', n - p') with hA
  set B : Submodule R M := ⨆ (p' : ℤ) (_ : p ≤ p'), W (p', n - p') with hB
  have hAG : A ≤ G (n + 1 - p) := iSup₂_le fun p' hp' =>
    (hle (p', n - p')).trans (inf_le_right.trans (hG (by omega)))
  have htop : (⊤ : Submodule R M) ≤ A ⊔ B := by
    rw [← hW.submodule_iSup_eq_top]
    refine iSup_le fun i => ?_
    by_cases hi : i.1 + i.2 = n
    · have hi' : i = (i.1, n - i.1) := Prod.ext rfl (by simp only; omega)
      rw [hi']
      rcases lt_or_ge i.1 p with h | h
      · exact le_sup_of_le_left (le_iSup₂_of_le i.1 h le_rfl)
      · exact le_sup_of_le_right (le_iSup₂_of_le i.1 h le_rfl)
    · rw [hW0 i hi]; exact bot_le
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (htop (Submodule.mem_top (x := x)))
  have haF : a ∈ F p := by
    have := sub_mem hx (hBF hb)
    rwa [add_sub_cancel_right] at this
  have ha0 : a = 0 := by
    have : a ∈ F p ⊓ G (n + 1 - p) := Submodule.mem_inf.mpr ⟨haF, hAG ha⟩
    rwa [hopp p, Submodule.mem_bot] at this
  rw [ha0, zero_add]
  exact hb

theorem spec_hodgeFiltration_eq_iSup_cupWedgePiece_of_cupLeft_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (n : ℕ) (hopp : ∀ p : ℤ, 1 ≤ p → p ≤ n → hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥)
    (p : ℤ) :
    F^p H_dR^(n : ℤ)(X) = ⨆ (p' : ℤ) (_ : p ≤ p'), cupWedgePiece X μ n (p', (n : ℤ) - p') := by
  have hG : Antitone fun q : ℤ => conjHodgeFiltrationComplexSubmodule X q n :=
    fun _ _ h => Submodule.comap_mono (hodgeFiltration_antitone X n h)
  have hle : ∀ pq : ℤ × ℤ, cupWedgePiece X μ n pq ≤
      F^pq.1 H_dR^(n : ℤ)(X) ⊓ conjHodgeFiltrationComplexSubmodule X pq.2 n := by
    intro pq
    by_cases hpq : pq.1 + pq.2 = n
    · have := spec_cupWedgePiece_le_deRhamHodgePiece_of_cupLeft_aux X hT hL n pq
      simp only [deRhamHodgePiece, hpq, ↓reduceIte] at this
      exact this
    · rw [spec_cupWedgePiece_eq_bot X μ n pq hpq]
      exact bot_le
  have hopp' : ∀ p : ℤ, F^p H_dR^(n : ℤ)(X) ⊓
      conjHodgeFiltrationComplexSubmodule X ((n : ℤ) + 1 - p) n = ⊥ := by
    intro p
    by_cases hp1 : 1 ≤ p
    · by_cases hpn : p ≤ n
      · exact hopp p hp1 hpn
      · exact hodgePiece_eq_bot_of_lt X (Or.inl (by lia))
    · exact hodgePiece_eq_bot_of_lt X (Or.inr (by lia))
  exact eq_iSup_of_opposed (n : ℤ) (spec_cupWedgePiece_isInternal X hT n)
    (spec_cupWedgePiece_eq_bot X μ n) (hodgeFiltration_antitone X n) hG hle hopp' p

/-- The unit is a left unit for the complexified cup product. -/
theorem cupC_unit_left {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (μ : CupProduct X) (a : Fin 0 → ℂ ⊗[ℚ] HQ X 1) {j : ℕ}
    (y : ℂ ⊗[ℚ] HQ X j) :
    μ.cupC (zero_add j) (μ.cupMultiC 0 a) y = y := by
  induction y using TensorProduct.inductionOn with
  | tmul w b =>
    exact (CupProduct.cupC_tmul μ (zero_add j) 1 w (unitClass X) b).trans
      (by rw [one_mul, μ.one_cup])
  | add y y' hy hy' => rw [map_add, hy, hy']

/-- The complexified cup product is associative. -/
theorem cupf1_cupC_assoc {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (μ : CupProduct X) {i j l ij jl k : ℕ} (hij : i + j = ij)
    (hjl : j + l = jl) (h₁ : ij + l = k) (h₂ : i + jl = k) (a : ℂ ⊗[ℚ] HQ X i)
    (b : ℂ ⊗[ℚ] HQ X j) (c : ℂ ⊗[ℚ] HQ X l) :
    μ.cupC h₁ (μ.cupC hij a b) c = μ.cupC h₂ a (μ.cupC hjl b c) := by
  induction a using TensorProduct.inductionOn with
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | tmul z a =>
    induction b using TensorProduct.inductionOn with
    | add b b' hb hb' => simp only [map_add, LinearMap.add_apply, hb, hb']
    | tmul w b =>
      induction c using TensorProduct.inductionOn with
      | add c c' hc hc' => simp only [map_add, hc, hc']
      | tmul u c =>
        rw [CupProduct.cupC_tmul, CupProduct.cupC_tmul, CupProduct.cupC_tmul,
          CupProduct.cupC_tmul, mul_assoc, μ.assoc hij hjl h₁ h₂]

/-- `cupMultiC` turns concatenation into the complexified cup product, with the target degree
given by an equation. -/
theorem cupMultiC_append {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (μ : CupProduct X) (n : ℕ) (b : Fin n → ℂ ⊗[ℚ] HQ X 1) :
    ∀ (m : ℕ) (a : Fin m → ℂ ⊗[ℚ] HQ X 1) (k : ℕ) (h : m + n = k)
      (c : Fin k → ℂ ⊗[ℚ] HQ X 1),
      (∀ i : Fin m, c (Fin.cast h (Fin.castAdd n i)) = a i) →
      (∀ j : Fin n, c (Fin.cast h (Fin.natAdd m j)) = b j) →
      μ.cupMultiC k c = μ.cupC h (μ.cupMultiC m a) (μ.cupMultiC n b)
  | 0, a, k, h, c, _, hc2 => by
    obtain rfl : k = n := by omega
    rw [cupC_unit_left]
    congr 1
    funext j
    rw [← hc2 j]
    congr 1
    ext
    simp
  | m + 1, a, k, h, c, hc1, hc2 => by
    obtain rfl : k = m + n + 1 := by omega
    rw [CupProduct.cupMultiC_succ μ (m + n), CupProduct.cupMultiC_succ μ m,
      cupf1_cupC_assoc μ (Nat.add_comm 1 m) rfl h (Nat.add_comm 1 _)]
    have h0 : c 0 = a 0 := by
      rw [← hc1 0]
      congr 1
    rw [h0, cupMultiC_append μ n b m (Fin.tail a) (m + n) rfl (Fin.tail c)
      (fun i => by
        change c _ = a i.succ
        rw [← hc1 i.succ]
        congr 1)
      (fun j => by
        change c _ = b j
        rw [← hc2 j]
        congr 1
        ext
        simp
        omega)]

/-- A degree-one class in the candidate piece of type `d` maps into `F^{d.1}`. -/
theorem bettiDeRhamHQ_mem_of_mem_cohomologyHodgePiece_one {X : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] {v : ℂ ⊗[ℚ] HQ X 1} {d : ℤ × ℤ}
    (h : v ∈ cohomologyHodgePiece X 1 d) :
    bettiDeRhamHQ X 1 v ∈ F^d.1 H_dR^((1 : ℕ) : ℤ)(X) := by
  unfold cohomologyHodgePiece at h
  split_ifs at h with hd
  · exact (Submodule.mem_inf.mp (Submodule.mem_comap.mp h)).1
  · rw [(Submodule.mem_bot ℂ).mp h, map_zero]
    exact Submodule.zero_mem _

theorem spec_cupFiltered_of_cupLeft_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X} (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (hopp : ∀ n : ℕ, 2 ≤ n → n ≤ 2 * dim X.left → ∀ p : ℤ, 1 ≤ p → p ≤ n →
      hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) :
    CupFiltered X μ := by
  have hβ : ∀ i, Function.Bijective (bettiDeRhamHQ X i) :=
    (HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X).bijective
  have hoppAll : ∀ n : ℕ, ∀ p : ℤ, 1 ≤ p → p ≤ n →
      hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥ := by
    intro n p hp1 hpn
    rcases Nat.lt_or_ge n 2 with hn | hn
    · obtain rfl : n = 1 := by lia
      obtain rfl : p = 1 := by lia
      have h := (spec_disjoint_hodgeFiltration_one_of_le X
        (spec_comap_hodgeFiltration_one_eq X).le).eq_bot
      rw [hodgePiece]
      convert h using 3
      norm_num
    · by_cases hn' : n ≤ 2 * dim X.left
      · exact hopp n hn hn' p hp1 hpn
      · have := spec_subsingleton_deRhamCohomology_of_lt X n (by lia)
        exact eq_bot_iff.mpr fun x _ => (Submodule.mem_bot ℂ).mpr (Subsingleton.elim x 0)
  have hspan : ∀ (i : ℕ) (p : ℤ), F^p H_dR^(i : ℤ)(X) ≤ Submodule.span ℂ
      {α | ∃ (d : Fin i → ℤ × ℤ) (v : Fin i → ℂ ⊗[ℚ] HQ X 1),
        p ≤ (HodgeBlocks.totalBidegree i d).1 ∧ (∀ l, v l ∈ cohomologyHodgePiece X 1 (d l)) ∧
          bettiDeRhamHQ X i (μ.cupMultiC i v) = α} := by
    intro i p
    rw [spec_hodgeFiltration_eq_iSup_cupWedgePiece_of_cupLeft_aux X hT hL i (hoppAll i) p]
    refine iSup₂_le fun p' hp' => Submodule.span_mono ?_
    rintro _ ⟨d, v, hd, hv, rfl⟩
    exact ⟨d, v, by rw [hd]; exact hp', hv, rfl⟩
  refine ⟨fun {i j k} h p q x y hx hy => ?_⟩
  subst h
  let e := LinearEquiv.ofBijective (bettiDeRhamHQ X i) (hβ i)
  let e' := LinearEquiv.ofBijective (bettiDeRhamHQ X j) (hβ j)
  let Φ : H_dR^(i : ℤ)(X) →ₗ[ℂ] H_dR^(j : ℤ)(X) →ₗ[ℂ] H_dR^((i + j : ℕ) : ℤ)(X) :=
    ((μ.cupC rfl).compl₁₂ e.symm.toLinearMap e'.symm.toLinearMap).compr₂
      (bettiDeRhamHQ X (i + j))
  have hΦ : ∀ (a : ℂ ⊗[ℚ] HQ X i) (b : ℂ ⊗[ℚ] HQ X j),
      Φ (bettiDeRhamHQ X i a) (bettiDeRhamHQ X j b) = bettiDeRhamHQ X (i + j) (μ.cupC rfl a b) := by
    intro a b
    simp only [Φ, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, e, e',
      LinearEquiv.ofBijective_symm_apply_apply]
  have hle : Submodule.map₂ Φ (F^p H_dR^(i : ℤ)(X)) (F^q H_dR^(j : ℤ)(X)) ≤
      F^(p + q) H_dR^((i + j : ℕ) : ℤ)(X) := by
    refine (Submodule.map₂_le_map₂ (hspan i p) (hspan j q)).trans ?_
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨_, ⟨d, v, hp, hv, rfl⟩, _, ⟨d', w, hq, hw, rfl⟩, rfl⟩
    rw [SetLike.mem_coe]
    beta_reduce
    rw [hΦ, ← cupMultiC_append μ j w i v (i + j) rfl (Fin.append v w)
      (fun l => by simp) (fun l => by simp)]
    refine hodgeFiltration_antitone X _ ?_
      (spec_bettiDeRhamHQ_cupMultiC_mem_of_cupLeft_aux X hT hL (i + j) (Fin.append v w)
        (fun l => (Fin.append d d' l).1) fun l => ?_)
    · simp only [HodgeBlocks.totalBidegree] at hp hq
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      lia
    · induction l using Fin.addCases with
      | left l =>
        simp only [Fin.append_left]
        exact bettiDeRhamHQ_mem_of_mem_cohomologyHodgePiece_one (hv l)
      | right l =>
        simp only [Fin.append_right]
        exact bettiDeRhamHQ_mem_of_mem_cohomologyHodgePiece_one (hw l)
  have := Submodule.map₂_le.mp hle _ hx _ hy
  rwa [hΦ] at this

theorem spec_hodgeDecomposition_of_cupLeft_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (hopp : ∀ n : ℕ, 2 ≤ n → n ≤ 2 * dim X.left → ∀ p : ℤ, 1 ≤ p → p ≤ n →
      hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) :
    HodgeDecomposition X :=
  spec_hodgeDecomposition_of_opposed X hT (spec_cupFiltered_of_cupLeft_aux X hT hL hopp) hopp

end HodgeLean.Adapters
