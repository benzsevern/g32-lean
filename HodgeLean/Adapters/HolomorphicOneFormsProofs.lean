import HodgeLean.Adapters.HolomorphicOneFormsDefs
import HodgeLean.Adapters.HodgeFilterLattice

/-! # Proof obligations for global holomorphic `1`-forms

One obligation per statement of `HodgeLean.Adapters.HolomorphicOneForms`. All ten are proved, by two parallel provers. -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped TensorProduct

namespace HodgeLean.Adapters

theorem spec_structureSheaf_globalSections_bijective_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [IsProper X.hom] :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appTop).hom := by
  let F := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed X.hom
  let _ := (isField_of_universallyClosed ℂ X.hom).toField
  exact IsAlgClosed.ringHom_bijective_of_isIntegral F.hom hF

theorem spec_cycleOneForm_injective_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] :
    Function.Injective (cycleOneForm X) := by
  intro a b h
  have h1 := ((ConcreteCategory.bijective_of_isIso
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (filteredDeRhamXOneIso X).hom))).1 h
  exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance h1

/-- The degree-two term of `F^1 Ω•` is the sheaf of holomorphic `2`-forms.
Source: Mathlib's `HomologicalComplex.stupidTruncXIso` and `HomologicalComplex.extendXIso`. -/
def filteredDeRhamXTwoIso (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    (F^1 Ω•(X)).X ((2 : ℕ) : ℤ) ≅ holomorphicDeRhamSheaf X (dim X.left) 2 :=
  HomologicalComplex.stupidTruncXIso Ω•(X) (ComplexShape.embeddingUpIntGE 1)
      (i := 1) (by simp) ≪≫
    (holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat
      (i := 2) rfl

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    (filteredDeRhamXTwoIso X).hom ≫ (filteredDeRhamXTwoIso X).inv = 𝟙 _ :=
  Iso.hom_inv_id _

set_option backward.isDefEq.respectTransparency false in
/-- Under `filteredDeRhamXOneIso` and `filteredDeRhamXTwoIso`, the differential of `F^1 Ω•` from
degree `1` to degree `2` is the exterior derivative. -/
lemma filteredDeRham_d_one_two (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    (F^1 Ω•(X)).d ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) =
      (filteredDeRhamXOneIso X).hom ≫ holomorphicDeRhamSheafDifferential X (dim X.left) 1 ≫
        (filteredDeRhamXTwoIso X).inv := by
  rw [← holomorphicDeRhamComplex_d]
  dsimp only [hodgeFilteredDeRhamComplex, HomologicalComplex.stupidTrunc,
    filteredDeRhamXOneIso, filteredDeRhamXTwoIso, HomologicalComplex.stupidTruncXIso]
  rw [HomologicalComplex.extend_d_eq _ _ (i := 0) (by simp) (j := 1) (by simp)]
  simp only [HomologicalComplex.restriction_d, Iso.trans_hom, Iso.trans_inv, Category.assoc]
  congr 1
  rw [show Ω•(X).d ((ComplexShape.embeddingUpIntGE 1).f 0) ((ComplexShape.embeddingUpIntGE 1).f 1) =
    ((holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat
      (i := 1) rfl).hom ≫ (holomorphicDeRhamComplex X (dim X.left)).d 1 2 ≫
      ((holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat
      (i := 2) rfl).inv from HomologicalComplex.extend_d_eq _ _ rfl rfl]
  simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.assoc]
  rfl

theorem spec_range_cycleOneForm_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] :
    (cycleOneForm X).range = closedGlobalHolomorphicOneForms X := by
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))
  let K := filteredGlobalSections X
  have hd (y : K.X ((1 : ℕ) : ℤ)) : K.d ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) y =
      Γ.map (filteredDeRhamXTwoIso X).inv
        (globalHolomorphicDifferential X 1 (Γ.map (filteredDeRhamXOneIso X).hom y)) := by
    change Γ.map ((F^1 Ω•(X)).d ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ)) y = _
    rw [filteredDeRham_d_one_two, Γ.map_comp, Γ.map_comp]
    rfl
  have hinv (ω : GlobalHolomorphicForm X 1) :
      Γ.map (filteredDeRhamXOneIso X).hom (Γ.map (filteredDeRhamXOneIso X).inv ω) = ω := by
    rw [← ConcreteCategory.comp_apply, ← Γ.map_comp, Iso.inv_hom_id, Γ.map_id,
      ConcreteCategory.id_apply]
  ext ω
  constructor
  · rintro ⟨z, rfl⟩
    change globalHolomorphicDifferential X 1 (cycleOneForm X z) = 0
    have h0 := ConcreteCategory.congr_hom (K.iCycles_d ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ)) z
    rw [ConcreteCategory.comp_apply, hd] at h0
    apply (ConcreteCategory.bijective_of_isIso (Γ.map (filteredDeRhamXTwoIso X).inv)).1
    rw [map_zero]
    exact h0
  · intro hω
    let y : K.X ((1 : ℕ) : ℤ) := Γ.map (filteredDeRhamXOneIso X).inv ω
    have hy : K.d ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) y = 0 := by
      rw [hd, hinv, show globalHolomorphicDifferential X 1 ω = 0 from hω, map_zero]
      rfl
    have hy' : y ∈ (K.sc ((1 : ℕ) : ℤ)).g.hom.ker := by
      change K.d _ ((ComplexShape.up ℤ).next ((1 : ℕ) : ℤ)) y = 0
      rw [show (ComplexShape.up ℤ).next ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by simp]
      exact hy
    refine ⟨(K.sc ((1 : ℕ) : ℤ)).abCyclesIso.inv ⟨y, hy'⟩, ?_⟩
    change Γ.map (filteredDeRhamXOneIso X).hom
      ((K.sc ((1 : ℕ) : ℤ)).iCycles ((K.sc ((1 : ℕ) : ℤ)).abCyclesIso.inv ⟨y, hy'⟩)) = ω
    rw [ShortComplex.abCyclesIso_inv_apply_iCycles]
    exact hinv ω

/-- The differential into degree `1` of `Γ(Y, S)` vanishes when `S` is strictly `≥ 1`. -/
lemma globalSectionsComplexInt_d_zero_one {Y : TopCat.{0}}
    (S : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) [S.IsStrictlyGE 1] :
    (TopCat.Sheaf.globalSectionsComplexInt Y S).d 0 1 = 0 :=
  (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).map_isZero
    (S.isZero_of_isStrictlyGE 1 0 (by norm_num)))).eq_of_src _ _

/-- Homology equals cycles in degree `1` for `Γ(Y, S)` when `S` is strictly `≥ 1`. -/
lemma isIso_globalSectionsComplexInt_homologyπ_one {Y : TopCat.{0}}
    (S : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) [S.IsStrictlyGE 1] :
    IsIso ((TopCat.Sheaf.globalSectionsComplexInt Y S).homologyπ 1) :=
  HomologicalComplex.isIso_homologyπ _ 0 1 (by simp) (globalSectionsComplexInt_d_zero_one S)

theorem spec_filteredGlobalSections_homologyπ_one_bijective_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    Function.Bijective ((filteredGlobalSections X).homologyπ ((1 : ℕ) : ℤ)).hom := by
  have := isIso_globalSectionsComplexInt_homologyπ_one (Y := TopCat.of (ComplexPoint X))
    (F^1 Ω•(X))
  exact ConcreteCategory.bijective_of_isIso _

/-- Global sections preserve quasi-isomorphisms in degree `1` between complexes strictly `≥ 1`:
there the degree-one homology is a kernel, and global sections preserve kernels. -/
lemma quasiIsoAt_globalSections_map_one {Y : TopCat.{0}}
    {S T : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ} [S.IsStrictlyGE 1] [T.IsStrictlyGE 1]
    (f : S ⟶ T) [QuasiIsoAt f 1] :
    QuasiIsoAt (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      Y).mapHomologicalComplex ℤᵘᵖ).map f) 1 := by
  let F := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  have hS : (S.sc 1).f = 0 := (S.isZero_of_isStrictlyGE 1 _ (by simp)).eq_of_src _ _
  have hT : (T.sc 1).f = 0 := (T.isZero_of_isStrictlyGE 1 _ (by simp)).eq_of_src _ _
  have := F.preservesLeftHomology_of_zero_f (S.sc 1) hS
  have := F.preservesLeftHomology_of_zero_f (T.sc 1) hT
  have h : QuasiIsoAt f 1 := inferInstance
  rw [quasiIsoAt_iff] at h ⊢
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology F
    ((HomologicalComplex.shortComplexFunctor _ _ 1).map f)

section

local instance s4cHasDerivedCategory (X : Over (Spec ↧ℂ)) :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

theorem spec_globalSectionsToHypercohomology_one_bijective_aux (X : Over (Spec ↧ℂ))
    (S : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [S.IsStrictlyGE 1] :
    Function.Bijective (globalSectionsToHypercohomology X S ((1 : ℕ) : ℤ)) := by
  obtain ⟨I, i, _, _, _⟩ := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective S 1
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I 1
  have : QuasiIsoAt (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map i) 1 :=
    quasiIsoAt_globalSections_map_one i
  have hi : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X) ℤᵘᵖ i := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have hpost : Function.Bijective (hypercohomologyMap X i ((1 : ℕ) : ℤ)) :=
    (Localization.SmallShiftedHom.postcompEquiv.{1} i hi (a := ((1 : ℕ) : ℤ))).bijective
  rw [← Function.Bijective.of_comp_iff' hpost]
  have hcomp : (hypercohomologyMap X i ((1 : ℕ) : ℤ)) ∘
      (globalSectionsToHypercohomology X S ((1 : ℕ) : ℤ)) =
      (globalSectionsToHypercohomology X I ((1 : ℕ) : ℤ)) ∘
        (HomologicalComplex.homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map i) ((1 : ℕ) : ℤ)) := by
    funext x
    exact (globalSectionsToHypercohomology_naturality X i _ x).symm
  rw [hcomp]
  exact (globalSectionsToHypercohomology_bijective_of_isKInjective X I _).comp
    (ConcreteCategory.bijective_of_isIso _)

end

theorem spec_hodgeFiltration_one_eq_range_cycleDeRhamClass_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).toAddSubgroup = (cycleDeRhamClass X).range := by
  have hs : Function.Surjective
      ((globalSectionsToHypercohomology X (F^1 Ω•(X)) ((1 : ℕ) : ℤ)).comp
        ((filteredGlobalSections X).homologyπ ((1 : ℕ) : ℤ)).hom) :=
    (spec_globalSectionsToHypercohomology_one_bijective_aux X (F^1 Ω•(X))).2.comp
      (spec_filteredGlobalSections_homologyπ_one_bijective_aux X).2
  ext α
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hs y
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, rfl⟩

namespace CycleDeRhamClassInjective
open CategoryTheory.Limits

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

local instance : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- `Ω•(X)` in degree `0`. -/
private abbrev deRhamXZeroIso :
    Ω•(X).X 0 ≅ holomorphicDeRhamSheaf X (dim X.left) 0 :=
  (holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl

/-- `Ω•(X)` in degree `1`. -/
private abbrev deRhamXOneIso :
    Ω•(X).X 1 ≅ holomorphicDeRhamSheaf X (dim X.left) 1 :=
  (holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl

lemma deRham_d_zero_one :
    (deRhamXZeroIso X).inv ≫ Ω•(X).d 0 1 =
      holomorphicDeRhamSheafDifferential X (dim X.left) 0 ≫ (deRhamXOneIso X).inv := by
  rw [Iso.inv_comp_eq]
  have h : (holomorphicDeRhamComplex X (dim X.left)).d 0 1 =
      holomorphicDeRhamSheafDifferential X (dim X.left) 0 :=
    holomorphicDeRhamComplex_d X (dim X.left) 0
  exact (HomologicalComplex.extend_d_eq (holomorphicDeRhamComplex X (dim X.left))
    ComplexShape.embeddingUpNat (i := 0) (j := 1) (i' := 0) (j' := 1) rfl rfl).trans
    (congrArg (fun φ => (deRhamXZeroIso X).hom ≫ φ ≫ (deRhamXOneIso X).inv) h)

/-- The projection `Ω• → Ω^0[0]`. -/
private def proj : Ω•(X) ⟶ (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
    (holomorphicDeRhamSheaf X (dim X.left) 0) :=
  HomologicalComplex.mkHomToSingle (deRhamXZeroIso X).hom (fun i hi => by
    apply (Ω•(X).isZero_of_isStrictlyGE 0 i (by simp at hi; omega)).eq_of_src)

/-- The inclusion `ℂ_X[0] → Ω•`. -/
private def incl : (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
    𝓒(↧(ComplexPoint X); ℂ) ⟶ Ω•(X) :=
  HomologicalComplex.mkHomFromSingle
    (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫ (deRhamXZeroIso X).inv)
    (fun k hk => by
      obtain rfl : k = 1 := by simp at hk; omega
      rw [Category.assoc, deRham_d_zero_one, ← Category.assoc,
        constantsToHolomorphicDeRhamZeroSheaf_comp_differential, zero_comp])

lemma incl_proj : incl X ≫ proj X =
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
      (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)) := by
  apply HomologicalComplex.from_single_hom_ext
  erw [HomologicalComplex.single_map_f_self]
  simp [incl, proj]

lemma inclusion_proj : hodgeFilteredDeRhamInclusion X 1 ≫ proj X = 0 := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  by_cases hn : n = 0
  · subst hn
    apply (Ω•(X).isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE 1) 0 (fun i => by
      simp; omega)).eq_of_src
  · apply (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn).eq_of_tgt

/-- The short exact sequence `F^1 Ω• → Ω• → Ω^0[0]`. -/
private def ses : ShortComplex (CochainComplex (AnalyticAdditiveSheaf X) ℤ) :=
  ShortComplex.mk _ _ (inclusion_proj X)

lemma ses_shortExact : (ses X).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  by_cases hn : n = 0
  · subst hn
    have h1 : IsZero ((F^1 Ω•(X)).X 0) :=
      Ω•(X).isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE 1) 0 (fun i => by simp; omega)
    have hg : IsIso ((proj X).f 0) := by
      rw [proj, HomologicalComplex.mkHomToSingle_f]
      infer_instance
    have hf : ((ses X).map (HomologicalComplex.eval _ _ 0)).f = 0 := h1.eq_of_src _ _
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.exact_iff_mono _ hf]
      exact @IsIso.mono_of_iso _ _ _ _ ((proj X).f 0) hg
    · exact h1.mono _
    · exact @IsIso.epi_of_iso _ _ _ _ ((proj X).f 0) hg
  · have h3 : IsZero (((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        (holomorphicDeRhamSheaf X (dim X.left) 0)).X n) :=
      HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
    have hf : IsIso ((hodgeFilteredDeRhamInclusion X 1).f n) := by
      by_cases hpos : 1 ≤ n
      · obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = 1 + i := ⟨(n - 1).toNat, by omega⟩
        have h := HomologicalComplex.stupidTruncInclusion_f Ω•(X) (ComplexShape.embeddingUpIntGE 1)
          (i := i) (j := 1 + (i : ℤ)) (by simp)
        unfold hodgeFilteredDeRhamInclusion
        erw [h]
        exact Iso.isIso_hom _
      · refine IsZero.isIso
          (Ω•(X).isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE 1) n (fun i => by
            simp; omega))
          (Ω•(X).isZero_of_isStrictlyGE 0 n (by omega)) _
    have hg : ((ses X).map (HomologicalComplex.eval _ _ n)).g = 0 := h3.eq_of_tgt _ _
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.exact_iff_epi _ hg]
      exact @IsIso.epi_of_iso _ _ _ _ ((hodgeFilteredDeRhamInclusion X 1).f n) hf
    · exact @IsIso.mono_of_iso _ _ _ _ ((hodgeFilteredDeRhamInclusion X 1).f n) hf
    · exact h3.epi _

lemma integerConstantHom_bijective {Y : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat Y) :
    Function.Bijective (fun g => TopCat.Sheaf.integerConstantHomAddEquivGlobalSections F g) := by
  let _ : AddCommGroup ((TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℤ) ⟶ F) :=
    (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat Y)).homGroup _ _
  exact (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections F).bijective

lemma hom_factor
    (hconst : ∀ f : GlobalHolomorphicForm X 0, f ∈ Set.range
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
          (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left))).hom)
    (ψ : (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℤ) ⟶
      holomorphicDeRhamSheaf X (dim X.left) 0) :
    ∃ τ, ψ = τ ≫ constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) := by
  obtain ⟨t, ht⟩ := hconst (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections _ ψ)
  obtain ⟨τ, rfl⟩ := (integerConstantHom_bijective _).2 t
  refine ⟨τ, (integerConstantHom_bijective _).1 ?_⟩
  exact ht.symm

lemma key
    (hconst : ∀ f : GlobalHolomorphicForm X 0, f ∈ Set.range
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
          (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left))).hom)
    (y : ℍ^(1 : ℤ)(X; F^1 Ω•(X)))
    (hy : hypercohomologyMap X (hodgeFilteredDeRhamInclusion X 1) 1 y = 0) : y = 0 := by
  apply (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  rw [hypercohomologyEquiv_zero]
  have h1 := congrArg
    (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q) hy
  rw [hypercohomologyEquiv_zero] at h1
  change Localization.SmallShiftedHom.equiv _ _ (y.comp _ _) = 0 at h1
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀,
    ShiftedHom.comp_mk₀] at h1
  let T := DerivedCategory.triangleOfSES (ses_shortExact X)
  have hT : T ∈ distTriang _ := DerivedCategory.triangleOfSES_distinguished (ses_shortExact X)
  obtain ⟨g, hg⟩ := Pretriangulated.Triangle.coyoneda_exact₁ T hT _ h1
  rw [hg]
  have h23 : T.mor₂ ≫ T.mor₃ = 0 := Pretriangulated.comp_distTriang_mor_zero₂₃ _ hT
  let eZ : DerivedCategory.Q.obj (constantIntegerSheafComplexInt X) ≅
      (DerivedCategory.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℤ)) :=
    DerivedCategory.Q.mapIso (constantIntegerSheafComplexIntIsoSingle X) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (AnalyticAdditiveSheaf X) 0).app _).symm
  let e3 : T.obj₃ ≅ (DerivedCategory.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
      (holomorphicDeRhamSheaf X (dim X.left) 0) :=
    ((DerivedCategory.singleFunctorIsoCompQ (AnalyticAdditiveSheaf X) 0).app _).symm
  have hfac : (DerivedCategory.singleFunctor (AnalyticAdditiveSheaf X) 0).map
      (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)) ≫ e3.inv =
      ((DerivedCategory.singleFunctorIsoCompQ (AnalyticAdditiveSheaf X) 0).app _).hom ≫
        DerivedCategory.Q.map (incl X) ≫ T.mor₂ := by
    have hnat := (DerivedCategory.singleFunctorIsoCompQ (AnalyticAdditiveSheaf X) 0).hom.naturality
      (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left))
    rw [Functor.comp_map, ← incl_proj, Functor.map_comp] at hnat
    exact hnat
  obtain ⟨ψ, hψ⟩ := (DerivedCategory.singleFunctor (AnalyticAdditiveSheaf X) 0).map_surjective
    (eZ.inv ≫ g ≫ e3.hom)
  obtain ⟨τ, rfl⟩ := hom_factor X hconst ψ
  have hg' : g = eZ.hom ≫ (DerivedCategory.singleFunctor (AnalyticAdditiveSheaf X) 0).map
      (τ ≫ constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)) ≫ e3.inv := by
    rw [hψ]
    simp only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.comp_id]
  rw [hg']
  erw [Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hfac]
  have h0 : (DerivedCategory.Q.map (incl X) ≫ T.mor₂) ≫ T.mor₃ = 0 :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun φ => DerivedCategory.Q.map (incl X) ≫ φ) h23).trans comp_zero)
  erw [h0]
  simp only [comp_zero]
  rfl

end CycleDeRhamClassInjective

theorem spec_cycleDeRhamClass_injective_of_constant_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom]
    (hconst : ∀ f : GlobalHolomorphicForm X 0, f ∈ Set.range
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
          (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left))).hom) :
    Function.Injective (cycleDeRhamClass X) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hinj : Function.Injective
      ((globalSectionsToHypercohomology X (F^1 Ω•(X)) ((1 : ℕ) : ℤ)).comp
        ((filteredGlobalSections X).homologyπ ((1 : ℕ) : ℤ)).hom) :=
    (spec_globalSectionsToHypercohomology_one_bijective_aux X (F^1 Ω•(X))).1.comp
      (spec_filteredGlobalSections_homologyπ_one_bijective_aux X).1
  apply hinj
  rw [map_zero]
  exact CycleDeRhamClassInjective.key X hconst _ hz

theorem spec_comap_hodgeFiltration_one_le_iff_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X ↔
      ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
        bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ω ∈ complexHolomorphicH1 X := by
  constructor
  · intro hle z ω hω
    apply hle
    show bettiDeRhamHQ X 1 ω ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X)
    rw [hω]
    exact ⟨_, rfl⟩
  · intro h ω hω
    have hm : bettiDeRhamHQ X 1 ω ∈ (cycleDeRhamClass X).range := by
      rw [← spec_hodgeFiltration_one_eq_range_cycleDeRhamClass_aux X]
      exact hω
    obtain ⟨z, hz⟩ := hm
    exact h z ω hz.symm

theorem spec_cycleDeRhamClass_not_surjective_of_le_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (hg : 1 ≤ dim X.left)
    (hle : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X) :
    ¬ Function.Surjective (cycleDeRhamClass X) := by
  intro hsurj
  have htop : ∀ ω : ℂ ⊗[ℚ] HQ X 1, ω ∈ complexHolomorphicH1 X := by
    intro ω
    apply hle
    obtain ⟨z, hz⟩ := hsurj (bettiDeRhamHQ X 1 ω)
    show bettiDeRhamHQ X 1 ω ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X)
    rw [← hz]
    exact ⟨_, rfl⟩
  have hbot : complexAntiholomorphicH1 X = ⊥ := by
    rw [eq_bot_iff]
    intro ω hω
    exact Submodule.disjoint_def.mp (spec_complexH1_split X).2 ω (htop ω) hω
  have hdim := (spec_complexH1_dimension X).2
  rw [hbot, finrank_bot] at hdim
  omega

theorem spec_exists_cycle_not_antiholomorphic_of_eq_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (hg : 1 ≤ dim X.left)
    (heq : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X) :
    ∃ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z ∧ ω ∉ complexAntiholomorphicH1 X := by
  have hne : complexHolomorphicH1 X ≠ ⊥ := by
    intro h
    have hdim := (spec_complexH1_dimension X).1
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨ω, hωH, hω0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hF : ω ∈ (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) := by
    rw [heq]
    exact hωH
  have hm : bettiDeRhamHQ X 1 ω ∈ (cycleDeRhamClass X).range := by
    rw [← spec_hodgeFiltration_one_eq_range_cycleDeRhamClass_aux X]
    exact hF
  obtain ⟨z, hz⟩ := hm
  exact ⟨z, ω, hz.symm, fun hA =>
    hω0 (Submodule.disjoint_def.mp (spec_complexH1_split X).2 ω hωH hA)⟩

end HodgeLean.Adapters
