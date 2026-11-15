import HodgeLean.RealDefs.FundamentalClass.Cone
import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularSectionCohomology

/-! # `[X] = 1`: the singular-section comparison on the constant cochain

Follows a degree-`0` supported section through
`supportedRationalSingularSectionCohomologyEquivSupportComplement`, step by step. -/

open CategoryTheory Limits TopologicalSpace CochainComplex AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

section StepA

variable (X : TopCat.{0}) (U V : Opens X)
  (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ) (hK : ∀ n, (K.X n).IsFlasque)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Step A: the supported-section cone comparison sends the class of a supported section to the
class of its `inl` image in the cone of restriction. -/
lemma supportedSectionHomologyIsoRestrictionCone_homologyπ (n : ℤ)
    (c : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V K).X₁.cycles n)
    (c' : (mappingCone (TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ K
      (Opens.infLELeft V U))).cycles (n - 1))
    (hc' : (mappingCone (TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ K
      (Opens.infLELeft V U))).iCycles (n - 1) c' =
      (mappingCone.inl (TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ K
        (Opens.infLELeft V U))).v n (n - 1) (by omega)
        ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V K).f.f n
          ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V K).X₁.iCycles n c))) :
    (TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone X U V K hK n).hom
        ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V K).X₁.homologyπ n c) =
      (mappingCone (TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ K
        (Opens.infLELeft V U))).homologyπ (n - 1) c' := by
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V K
  have hS := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque
    X U V K hK
  have hdef : (TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone X U V K hK n).hom =
      (mappingCocone.shortExactHomologyIsoCone S hS (n - 1) n (by omega)).hom ≫
        HomologicalComplex.homologyMap
          (TopCat.Sheaf.supportRestrictionSectionsConeIso X U V K).hom (n - 1) := rfl
  let e := TopCat.Sheaf.supportRestrictionSectionsConeIso X U V K
  rw [hdef, ConcreteCategory.comp_apply,
    ab_shortExactHomologyIsoCone_homologyπ S hS (n - 1) n (by omega) c
      (HomologicalComplex.cyclesMap e.inv (n - 1) c') ?_,
    ab_homologyMap_homologyπ e.hom (n - 1) _ c' ?_]
  · have h1 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i e.inv (n - 1)) c'
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
    rw [h1, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, e.inv_hom_id]
    rfl
  · have h1 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i e.inv (n - 1)) c'
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
    rw [h1, hc', ← ConcreteCategory.comp_apply]
    erw [inl_v_mapArrowHom]
    rfl

end StepA


section Extend

variable {C D I J : Type*} [Category* C] [Category* D] [Preadditive C]
  [Preadditive D] [HasZeroObject C] [HasZeroObject D] {c : ComplexShape I}
  {c' : ComplexShape J}

/-- The inverse of the extension comparison, in a degree coming from the original complex. -/
lemma mapExtendCanonicalIso_inv_f (F : C ⥤ D) [F.Additive]
    (K : HomologicalComplex C c) (e : c.Embedding c') {i : I} {j : J} (h : e.f i = j) :
    (HomologicalComplex.mapExtendCanonicalIso F K e).inv.f j =
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom ≫ F.map (K.extendXIso e h).inv := by
  rw [← cancel_epi ((HomologicalComplex.mapExtendCanonicalIso F K e).hom.f j),
    ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.mapExtendCanonicalIso_hom_f F K e h]
  simp [← F.map_comp]

end Extend

section StepC4

variable (P : TopPair.{0})

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Step C4: the canonical relative cone comparison sends the `inl` class of the inclusion of a
relative cocycle back to that cocycle's class. -/
lemma relativeCochainConeCohomologyEquivCanonical_homologyπ
    (c : (RelativeCochainComplex ℚ P).cycles 0)
    (cM : (mappingCone (relativeCochainRestrictionInt ℚ P)).cycles ((0 : ℕ) - 1 : ℤ))
    (hcM : (mappingCone (relativeCochainRestrictionInt ℚ P)).iCycles _ cM =
      (mappingCone.inl (relativeCochainRestrictionInt ℚ P)).v ((0 : ℕ) : ℤ) ((0 : ℕ) - 1 : ℤ)
        (by omega)
        ((relativeDualCochainShortComplexInt ℚ P).f.f ((0 : ℕ) : ℤ)
          (((RelativeCochainComplex ℚ P).extendXIso ComplexShape.embeddingUpNat rfl).inv
            ((RelativeCochainComplex ℚ P).iCycles 0 c)))) :
    relativeCochainConeCohomologyEquivCanonical ℚ P 0
        ((mappingCone (relativeCochainRestrictionInt ℚ P)).homologyπ _ cM) =
      (RelativeCochainComplex ℚ P).homologyπ 0 c := by
  let K := RelativeCochainComplex ℚ P
  let cE := (K.extendCyclesIso ComplexShape.embeddingUpNat (rfl :
    ComplexShape.embeddingUpNat.f 0 = ((0 : ℕ) : ℤ))).inv c
  have hcE : (K.extend ComplexShape.embeddingUpNat).iCycles _ cE =
      (K.extendXIso ComplexShape.embeddingUpNat rfl).inv (K.iCycles 0 c) := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.extendCyclesIso_inv_iCycles,
      ConcreteCategory.comp_apply]
  have hS := relativeDualCochainShortComplexInt_shortExact ℚ P
  have h1 := mod_shortExactHomologyIsoCone_homologyπ (relativeDualCochainShortComplexInt ℚ P) hS
    ((0 : ℕ) - 1 : ℤ) ((0 : ℕ) : ℤ) (by omega) cE cM (hcM.trans (by rw [← hcE]; rfl))
  dsimp only [relativeCochainConeCohomologyEquivCanonical, relativeDualCochainHomologyIsoCone]
  rw [LinearEquiv.trans_apply]
  change (relativeDualCochainCohomologyEquiv ℚ P 0)
    ((mappingCocone.shortExactHomologyIsoCone (relativeDualCochainShortComplexInt ℚ P) hS
      ((0 : ℕ) - 1 : ℤ) ((0 : ℕ) : ℤ) (by omega)).inv
      ((mappingCone (relativeCochainRestrictionInt ℚ P)).homologyπ _ cM)) = _
  erw [← h1, Iso.hom_inv_id_apply]
  change (K.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom
    ((K.extend ComplexShape.embeddingUpNat).homologyπ _ cE) = _
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_extendHomologyIso_hom,
    ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]

end StepC4

section StepC123

variable (X : TopCat.{0})

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Steps C1–C4: the raw-cochain cone comparison sends the `inl` class of a raw cochain to the
relative class of any relative cocycle that it pulls back. -/
lemma openRawSingularRestrictionConeCohomologyEquivRelative_homologyπ {V W : Opens X}
    (i : W ⟶ V) (r₀ : (openRawSingularCochainComplex ℚ X V).X 0)
    (c : (openRawSingularRestrictionCone ℚ X i).cycles ((0 : ℕ) - 1 : ℤ))
    (hc : (openRawSingularRestrictionCone ℚ X i).iCycles _ c =
      (mappingCone.inl (HomologicalComplex.extendMap (openRawSingularRestriction ℚ X i)
        ComplexShape.embeddingUpNat)).v ((0 : ℕ) : ℤ) ((0 : ℕ) - 1 : ℤ) (by omega)
        (((openRawSingularCochainComplex ℚ X V).extendXIso ComplexShape.embeddingUpNat rfl).inv r₀))
    (cr : (RelativeCochainComplex ℚ (openInclusionPair X i)).cycles 0)
    (hcr : (HomologicalComplex.linearDualMap (relativeChainProjection ℚ (openInclusionPair X i))).f 0
      ((RelativeCochainComplex ℚ (openInclusionPair X i)).iCycles 0 cr) = r₀) :
    openRawSingularRestrictionConeCohomologyEquivRelative ℚ X i 0
        ((openRawSingularRestrictionCone ℚ X i).homologyπ _ c) =
      (RelativeCochainComplex ℚ (openInclusionPair X i)).homologyπ 0 cr := by
  let P := openInclusionPair X i
  let φ := relativeCochainRestrictionInt ℚ P
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let e1 := openRawSingularRestrictionConeIsoRelative ℚ X i
  let c1 := HomologicalComplex.cyclesMap e1.hom _ c
  let e2 := mappingCone.mapHomologicalComplexIso φ F
  let c2 := HomologicalComplex.cyclesMap e2.inv _ c1
  let S := (mappingCone φ).sc ((0 : ℕ) - 1 : ℤ)
  let cM : (mappingCone φ).cycles ((0 : ℕ) - 1 : ℤ) := (S.mapCyclesIso F).hom c2
  have s1 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality e1.hom
    ((0 : ℕ) - 1 : ℤ)) c
  have s2 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality e2.inv
    ((0 : ℕ) - 1 : ℤ)) c1
  have s3 := ConcreteCategory.congr_hom (homologyπ_mapHomologyIso_hom S F) c2
  have hcM : (mappingCone φ).iCycles _ cM =
      (mappingCone.inl φ).v ((0 : ℕ) : ℤ) ((0 : ℕ) - 1 : ℤ) (by omega)
        ((relativeDualCochainShortComplexInt ℚ P).f.f ((0 : ℕ) : ℤ)
          (((RelativeCochainComplex ℚ P).extendXIso ComplexShape.embeddingUpNat rfl).inv
            ((RelativeCochainComplex ℚ P).iCycles 0 cr))) := by
    have h1 := ConcreteCategory.congr_hom (S.mapCyclesIso_hom_iCycles F) c2
    have h2 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i e2.inv _) c1
    have h3 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i e1.hom _) c
    rw [ConcreteCategory.comp_apply] at h1 h2 h3
    rw [ConcreteCategory.comp_apply] at h2 h3
    change F.map S.iCycles cM = _
    rw [h1]
    change (((F.mapHomologicalComplex _).obj (mappingCone φ)).iCycles _ c2) = _
    rw [h2, h3, hc]
    refine (congrArg (ConcreteCategory.hom (e2.inv.f _)) (ConcreteCategory.congr_hom
      (inl_v_mapArrowHom _ _ _ _ ((0 : ℕ) : ℤ) ((0 : ℕ) - 1 : ℤ) (by omega)) _)).trans ?_
    refine (ConcreteCategory.congr_hom
      (inl_v_mapHomologicalComplexIso_inv φ F ((0 : ℕ) : ℤ) ((0 : ℕ) - 1 : ℤ) (by omega)) _).trans ?_
    change (mappingCone.inl φ).v ((0 : ℕ) : ℤ) ((0 : ℕ) - 1 : ℤ) (by omega) _ = _
    congr 1
    have hR := ConcreteCategory.congr_hom (HomologicalComplex.extendMap_f
      (HomologicalComplex.linearDualMap (relativeChainProjection ℚ P)) ComplexShape.embeddingUpNat
      (rfl : ComplexShape.embeddingUpNat.f 0 = ((0 : ℕ) : ℤ)))
      (((RelativeCochainComplex ℚ P).extendXIso ComplexShape.embeddingUpNat rfl).inv
        ((RelativeCochainComplex ℚ P).iCycles 0 cr))
    simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hR
    refine Eq.trans ?_ hR.symm
    refine Eq.trans ?_ (congrArg _ hcr).symm
    have hm : (HomologicalComplex.extendMap (openRawSingularCochainComplexIsoDual ℚ X V).hom
          ComplexShape.embeddingUpNat).f 0 ≫
        (HomologicalComplex.mapExtendCanonicalIso (forget₂ (ModuleCat ℚ) AddCommGrpCat)
          (HomologicalComplex.linearDualCochainComplex (SingularChainComplex ℚ (TopCat.of V)))
          ComplexShape.embeddingUpNat).inv.f 0 =
        ((openRawSingularCochainComplex ℚ X V).extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
          (openRawSingularCochainComplexIsoDual ℚ X V).hom.f 0 ≫
          (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
            ((HomologicalComplex.linearDualCochainComplex (SingularChainComplex ℚ (TopCat.of V))).extendXIso
              ComplexShape.embeddingUpNat rfl).inv := by
      rw [HomologicalComplex.extendMap_f _ _ (i := 0) (i' := (0 : ℤ)) rfl,
        mapExtendCanonicalIso_inv_f _ _ _ (i := 0) (j := (0 : ℤ)) rfl]
      simp
    refine (ConcreteCategory.congr_hom hm _).trans ?_
    simp
    rfl
  have s4 := relativeCochainConeCohomologyEquivCanonical_homologyπ P cr cM hcM
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at s1 s2 s3
  dsimp only [openRawSingularRestrictionConeCohomologyEquivRelative, AddEquiv.trans_apply]
  change (relativeCochainConeCohomologyEquivCanonical ℚ P 0)
    ((S.mapHomologyIso F).hom (HomologicalComplex.homologyMap e2.inv _
      (HomologicalComplex.homologyMap e1.hom _
        ((openRawSingularRestrictionCone ℚ X i).homologyπ _ c)))) = _
  rw [s1, s2]
  erw [s3]
  exact s4

end StepC123


/-- An element killed by the differential underlies a cycle. -/
lemma ab_exists_cycles {K : CochainComplex AddCommGrpCat.{0} ℤ} {i : ℤ} (x : K.X i)
    (hx : K.d i (i + 1) x = 0) : ∃ c : K.cycles i, K.iCycles i c = x := by
  refine ⟨K.liftCycles (AddCommGrpCat.ofHom (zmultiplesHom _ x)) (i + 1) (by simp) (by
    ext
    simp [hx]) (1 : ℤ), ?_⟩
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
  simp

section Assembly

variable (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V] (U V : Opens X)

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Upstream's singular-section comparison sends the class of a supported section to the relative
class of a relative cocycle, as soon as the section comes from a raw cochain `r₀` that is a cocycle
vanishing on `V ⊓ U`, and `r₀` is the pullback of the relative cocycle. -/
theorem supportedRationalSingularSectionCohomologyEquivRelative_homologyπ
    (c : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
      (rationalSingularCochainComplex X)).X₁.cycles ((0 : ℕ) : ℤ))
    (r₀ : (openRawSingularCochainComplex ℚ X V).X 0)
    (hd : (openRawSingularCochainComplex ℚ X V).d 0 1 r₀ = 0)
    (hW : (openRawSingularRestriction ℚ X (Opens.infLELeft V U)).f 0 r₀ = 0)
    (hr : (openRawToSingularCochainSheafComplex ℚ X V).f 0 r₀ =
      ((singularCochainSheafComplex ℚ X).extendXIso ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f 0 = ((0 : ℕ) : ℤ))).hom.hom.app (Opposite.op V)
        ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
          (rationalSingularCochainComplex X)).f.f ((0 : ℕ) : ℤ)
          ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
            (rationalSingularCochainComplex X)).X₁.iCycles _ c)))
    (cr : (RelativeCochainComplex ℚ (openInclusionPair X (Opens.infLELeft V U))).cycles 0)
    (hcr : (HomologicalComplex.linearDualMap
      (relativeChainProjection ℚ (openInclusionPair X (Opens.infLELeft V U)))).f 0
      ((RelativeCochainComplex ℚ (openInclusionPair X (Opens.infLELeft V U))).iCycles 0 cr) = r₀) :
    supportedRationalSingularSectionCohomologyEquivRelative X U V 0
        ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
          (rationalSingularCochainComplex X)).X₁.homologyπ _ c) =
      (RelativeCochainComplex ℚ (openInclusionPair X (Opens.infLELeft V U))).homologyπ 0 cr := by
  let i := Opens.infLELeft V U
  let K' := singularCochainSheafComplex ℚ X
  let rE := ((openRawSingularCochainComplex ℚ X V).extendXIso ComplexShape.embeddingUpNat
    (rfl : ComplexShape.embeddingUpNat.f 0 = ((0 : ℕ) : ℤ))).inv r₀
  obtain ⟨cR, hcR⟩ := ab_exists_cycles (K := openRawSingularRestrictionCone ℚ X i)
    (i := ((0 : ℕ) - 1 : ℤ))
    ((mappingCone.inl (HomologicalComplex.extendMap (openRawSingularRestriction ℚ X i)
      ComplexShape.embeddingUpNat)).v ((0 : ℕ) : ℤ) ((0 : ℕ) - 1 : ℤ) (by omega) rE) (by
      have h01 : ((0 : ℕ) - 1 : ℤ) + 1 = ((0 : ℕ) : ℤ) := by omega
      rw [h01]
      refine (ConcreteCategory.congr_hom (mappingCone.inl_v_d (HomologicalComplex.extendMap
        (openRawSingularRestriction ℚ X i) ComplexShape.embeddingUpNat) ((0 : ℕ) : ℤ)
        ((0 : ℕ) - 1 : ℤ) (((1 : ℕ) : ℤ)) (by omega) (by omega)) rE).trans ?_
      have hφ : (HomologicalComplex.extendMap (openRawSingularRestriction ℚ X i)
          ComplexShape.embeddingUpNat).f ((0 : ℕ) : ℤ) rE = 0 := by
        rw [HomologicalComplex.extendMap_f _ _ (i := 0) (i' := ((0 : ℕ) : ℤ)) rfl]
        simp only [rE, ConcreteCategory.comp_apply]
        erw [Iso.inv_hom_id_apply, hW]
        exact map_zero _
      have hdE : ((openRawSingularCochainComplex ℚ X V).extend ComplexShape.embeddingUpNat).d
          ((0 : ℕ) : ℤ) ((1 : ℕ) : ℤ) rE = 0 := by
        rw [HomologicalComplex.extend_d_eq _ _ (i := 0) (j := 1) (i' := ((0 : ℕ) : ℤ))
          (j' := ((1 : ℕ) : ℤ)) rfl rfl]
        simp only [rE, ConcreteCategory.comp_apply]
        erw [Iso.inv_hom_id_apply, hd]
        exact map_zero _
      simp only [ConcreteCategory.comp_apply,
        AddCommGrpCat.hom_sub, AddMonoidHom.sub_apply, hφ, hdE, map_zero, sub_zero])
  let mR := openRawToSingularSheafRestrictionCone ℚ X i
  let cB := HomologicalComplex.cyclesMap mR _ cR
  let eB := TopCat.Sheaf.sectionComplexRestrictionExtendConeIso X K' i
  let cA := HomologicalComplex.cyclesMap eB.inv _ cB
  have hA := supportedSectionHomologyIsoRestrictionCone_homologyπ X U V
    (rationalSingularCochainComplex X) (fun _ => inferInstance) ((0 : ℕ) : ℤ) c cA (by
      have h1 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i eB.inv _) cB
      have h2 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i mR _) cR
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1 h2
      change (HomologicalComplex.cyclesMap eB.inv _ ≫ HomologicalComplex.iCycles _ _) cB = _
      rw [ConcreteCategory.comp_apply, h1]
      change eB.inv.f _ ((HomologicalComplex.cyclesMap mR _ ≫ HomologicalComplex.iCycles _ _) cR) = _
      rw [ConcreteCategory.comp_apply, h2, hcR]
      refine (congrArg (ConcreteCategory.hom (eB.inv.f _)) (ConcreteCategory.congr_hom
        (inl_v_mappingCone_map _ _
          (HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex ℚ X V)
            ComplexShape.embeddingUpNat)
          (HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex ℚ X (V ⊓ U))
            ComplexShape.embeddingUpNat)
          (openSingularSheafRestrictionInt_naturality ℚ X i)
          ((0 : ℕ) : ℤ) ((0 : ℕ) - 1 : ℤ) (by omega)) rE)).trans ?_
      refine (ConcreteCategory.congr_hom
        (inl_v_mapArrowHom (C := AddCommGrpCat.{0})
          (HomologicalComplex.extendMap (TopCat.Sheaf.sectionComplexRestriction X (.up ℕ) K' i)
            ComplexShape.embeddingUpNat)
          (TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ
            (K'.extend ComplexShape.embeddingUpNat) i) _ _
          ((0 : ℕ) : ℤ) ((0 : ℕ) - 1 : ℤ) (by omega)) _).trans ?_
      refine congrArg (ConcreteCategory.hom ((mappingCone.inl (TopCat.Sheaf.sectionComplexRestriction
        X ℤᵘᵖ (K'.extend ComplexShape.embeddingUpNat) i)).v ((0 : ℕ) : ℤ) ((0 : ℕ) - 1 : ℤ)
          (by omega))) ?_
      change (HomologicalComplex.mapExtendCanonicalIso (TopCat.Sheaf.supportEvaluation X V) K'
        ComplexShape.embeddingUpNat).inv.f ((0 : ℕ) : ℤ)
          ((HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex ℚ X V)
            ComplexShape.embeddingUpNat).f ((0 : ℕ) : ℤ) rE) = _
      rw [mapExtendCanonicalIso_inv_f _ _ _ (i := 0) (j := ((0 : ℕ) : ℤ)) rfl,
        HomologicalComplex.extendMap_f _ _ (i := 0) (i' := ((0 : ℕ) : ℤ)) rfl]
      simp only [rE, ConcreteCategory.comp_apply]
      erw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, hr]
      have hK := congrArg (fun f => f.hom.app (Opposite.op V))
        ((singularCochainSheafComplex ℚ X).extendXIso ComplexShape.embeddingUpNat
          (rfl : ComplexShape.embeddingUpNat.f 0 = ((0 : ℕ) : ℤ))).hom_inv_id
      exact ConcreteCategory.congr_hom hK _)
  dsimp only [supportedRationalSingularSectionCohomologyEquivRelative, AddEquiv.trans_apply]
  change openSingularSheafRestrictionConeCohomologyEquivRelative X i 0
    (HomologicalComplex.homologyMap eB.hom _
      ((TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone X U V
        (rationalSingularCochainComplex X) (fun _ => inferInstance) ((0 : ℕ) : ℤ)).hom
        ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
          (rationalSingularCochainComplex X)).X₁.homologyπ _ c))) = _
  rw [hA]
  have hB : HomologicalComplex.homologyMap eB.hom _
      ((mappingCone (TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ
        (rationalSingularCochainComplex X) i)).homologyπ _ cA) = (openSingularSheafRestrictionCone ℚ X i).homologyπ _ cB := by
    apply ab_homologyMap_homologyπ
    have h1 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i eB.inv _) cB
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
    rw [h1, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, eB.inv_hom_id]
    rfl
  erw [hB]
  have hC := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality mR
    ((0 : ℕ) - 1 : ℤ)) cR
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hC
  dsimp only [openSingularSheafRestrictionConeCohomologyEquivRelative, AddEquiv.trans_apply]
  rw [Iso.addCommGroupIsoToAddEquiv_apply, Iso.symm_hom]
  erw [← hC]
  rw [asIso_inv]
  erw [IsIso.hom_inv_id_apply]
  exact openRawSingularRestrictionConeCohomologyEquivRelative_homologyπ X i r₀ cR hcR cr hcr

end Assembly

end HodgeLean.RealDefs
