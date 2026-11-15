import HodgeLean.Adapters.CupCocycleSheafDefs
import HodgeLean.RealDefs.FundamentalClass.Cone

/-! # Proof obligations for `CupCocycleSheaf`

One `_aux` per statement of `HodgeLean.Adapters.CupCocycleSheaf`, all open.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Simplicial
open AlgebraicGeometry ComplexPoint
open AlgebraicTopology.Singular (singularCochainPresheaf OpenCochains singularCochainSheafComplex)

namespace HodgeLean.Adapters

theorem spec_cupLeftSheafHom_toSheafify_aux {K : Type} [CommRing K] {Y : TopCat.{0}}
    (a : Cochain K (TopCat.toSSet.obj Y) 1) (n : ℕ) (U : (Opens Y)ᵒᵖ)
    (c : OpenCochains K Y U n) :
    ((TopCat.Sheaf.forget AddCommGrpCat Y).map (cupLeftSheafHom a n)).app U
        ((toSheafify (Opens.grothendieckTopology Y) (singularCochainPresheaf K Y n)).app U c) =
      (toSheafify (Opens.grothendieckTopology Y) (singularCochainPresheaf K Y (1 + n))).app U
        (HodgeLean.Foundations.Singular.cupCochain _ 1 n (cupLeftRestrict a U) c) :=
  (congrArg (fun f => f.app U c)
    (toSheafify_naturality (Opens.grothendieckTopology Y) (cupLeftPresheafHom a n))).symm

theorem spec_cupLeftSheafComplexHom_comp_d_aux {K : Type} [CommRing K] {Y : TopCat.{0}}
    (a : Cochain K (TopCat.toSSet.obj Y) 1) (ha : coboundary K 1 a = 0) (i : ℤ) :
    (cupLeftSheafComplexHom a ha).f i ≫
        ((singularCochainSheafComplex K Y).extend ComplexShape.embeddingUpNat).d (i + 1)
          (i + 1 + 1) =
      -(((singularCochainSheafComplex K Y).extend ComplexShape.embeddingUpNat).d i (i + 1) ≫
        (cupLeftSheafComplexHom a ha).f (i + 1)) := by
  have h := (cupLeftSheafComplexHom a ha).comm i (i + 1)
  rw [CochainComplex.shiftFunctor_obj_d'] at h
  simp only [Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.comp_neg] at h
  rw [← h, neg_neg]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison from raw singular cochains to global sections of the sheaf complex is, in each
degree, the sheafification unit evaluated on the top open set. -/
theorem cupLeft_topOpenToGlobalSingularCochainSheafComplex_f {K : Type} [CommRing K]
    {Y : TopCat.{0}} (n : ℕ) :
    (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex K Y).f n =
      (toSheafify (Opens.grothendieckTopology Y) (singularCochainPresheaf K Y n)).app
        (Opposite.op ⊤) := by
  change ((AlgebraicTopology.Singular.singularCochainToPlusPlusPresheafComplex K Y).f n).app
      (Opposite.op ⊤) ≫
    ((plusPlusIsoSheafify (Opens.grothendieckTopology Y) AddCommGrpCat
      (singularCochainPresheaf K Y n)).hom).app (Opposite.op ⊤) = _
  rw [AlgebraicTopology.Singular.singularCochainToPlusPlusPresheafComplex_f, ← NatTrans.comp_app]
  exact congrArg (fun f => NatTrans.app f (Opposite.op ⊤))
    (toSheafify_plusPlusIsoSheafify_hom (Opens.grothendieckTopology Y) AddCommGrpCat
      (singularCochainPresheaf K Y n))

theorem spec_cupLeftGlobalHom_topOpen_aux {K : Type} [CommRing K] {Y : TopCat.{0}}
    (a : Cochain K (TopCat.toSSet.obj Y) 1) (n : ℕ) (c : Cochain K (TopCat.toSSet.obj Y) n) :
    cupLeftGlobalHom a n
        ((AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex K Y).f n
          (cupLeftRestrict c (Opposite.op ⊤))) =
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex K Y).f (1 + n)
        (cupLeftRestrict (HodgeLean.Foundations.Singular.cupCochain Y 1 n a c)
          (Opposite.op ⊤)) := by
  rw [cupLeft_topOpenToGlobalSingularCochainSheafComplex_f,
    cupLeft_topOpenToGlobalSingularCochainSheafComplex_f]
  refine (spec_cupLeftSheafHom_toSheafify_aux a n (Opposite.op ⊤)
    (cupLeftRestrict c (Opposite.op ⊤))).trans ?_
  congr 1
  rw [cupLeftRestrict, cupLeftRestrict, cupLeftRestrict,
    HodgeLean.Foundations.Singular.cupCochain_naturality]

section SingularClass

variable (Y : TopCat.{0})

attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData

set_option backward.isDefEq.respectTransparency false in
/-- A singular cohomology class is the homology class of a cycle of the singular cochain complex
whose underlying cochain is the given cocycle. -/
theorem cupLeft_exists_cohomologyClass_eq_homologyπ (K : Type) [CommRing K] (n : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cocycle K (TopCat.toSSet.obj Y) n) :
    ∃ c : (AlgebraicTopology.Singular.SingularCochainComplex K Y).cycles n,
      ((AlgebraicTopology.Singular.SingularCochainComplex K Y).iCycles n).hom c = φ.1 ∧
      HodgeLean.Foundations.Singular.cohomologyClass Y n φ =
        ((AlgebraicTopology.Singular.SingularCochainComplex K Y).homologyπ n).hom c := by
  let L := AlgebraicTopology.Singular.SingularChainComplex K Y
  let e := HomologicalComplex.linearDualCochainComplexScIso L n
  have hφ : ((L.sc n).linearDual.g).hom φ.1 = 0 := by
    change ((L.sc n).f.hom.dualMap) φ.1 = 0
    have hψ : AlgebraicTopology.Simplicial.coboundary K n φ.1 = 0 := φ.2
    change (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of K K)).d
      ((ComplexShape.down ℕ).prev n) n).hom.dualMap φ.1 = 0
    rw [ChainComplex.prev]
    exact hψ
  let x : LinearMap.ker (L.sc n).linearDual.g.hom := ⟨φ.1, hφ⟩
  let a := (L.sc n).linearDual.moduleCatCyclesIso.inv.hom x
  refine ⟨(ShortComplex.cyclesMap e.inv).hom a, ?_, ?_⟩
  · have hc := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i e.inv) a
    change ((AlgebraicTopology.Singular.SingularCochainComplex K Y).sc n).iCycles.hom
      ((ShortComplex.cyclesMap e.inv).hom a) = e.inv.τ₂.hom ((L.sc n).linearDual.iCycles.hom a) at hc
    refine hc.trans ?_
    have hs : (L.sc n).linearDual.iCycles.hom a = x.1 :=
      ConcreteCategory.congr_hom (L.sc n).linearDual.moduleCatCyclesIso_inv_iCycles x
    rw [hs]
    rfl
  · have h1 : HodgeLean.Foundations.Singular.cohomologyClass Y n φ =
        (ShortComplex.homologyMap e.inv).hom
          ((L.sc n).linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk x)) := rfl
    have ha : (L.sc n).linearDual.homologyπ.hom a =
        (L.sc n).linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk x) :=
      ConcreteCategory.congr_hom (L.sc n).linearDual.moduleCatCyclesIso_inv_π x
    rw [h1, ← ha]
    exact ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality e.inv) a

set_option backward.isDefEq.respectTransparency false in
/-- The raw comparison sends the class of a singular cocycle to the class of the corresponding
top-open cochain. -/
theorem cupLeft_ordinarySingularCohomologyEquivGlobalRaw_homologyπ (K : Type) [CommRing K] (n : ℕ)
    (c : (AlgebraicTopology.Singular.SingularCochainComplex K Y).cycles n) :
    ∃ c' : (AlgebraicTopology.Singular.globalRawSingularCochainComplex K Y).cycles n,
      (AlgebraicTopology.Singular.globalRawSingularCochainComplex K Y).iCycles n c' =
        ((AlgebraicTopology.Singular.singularCochainComplexIsoTopOpen K Y).hom.f n).hom
          (((AlgebraicTopology.Singular.SingularCochainComplex K Y).iCycles n).hom c) ∧
      AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw K Y n
          (((AlgebraicTopology.Singular.SingularCochainComplex K Y).homologyπ n).hom c) =
        (AlgebraicTopology.Singular.globalRawSingularCochainComplex K Y).homologyπ n c' := by
  let i := AlgebraicTopology.Singular.singularCochainComplexIsoTopOpen K Y
  let T := (AlgebraicTopology.Singular.TopOpenSingularChainComplex K Y).linearDualCochainComplex
  let F := forget₂ (ModuleCat K) AddCommGrpCat
  let G := AlgebraicTopology.Singular.globalRawSingularCochainComplexIso K Y
  let d := (HomologicalComplex.cyclesMap i.hom n).hom c
  let mC := (T.sc n).mapCyclesIso F
  let e : (AlgebraicTopology.Singular.topOpenForgottenSingularCochainComplex K Y).cycles n :=
    mC.inv d
  refine ⟨HomologicalComplex.cyclesMap G.inv n e, ?_, ?_⟩
  · rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
    have h1 : (AlgebraicTopology.Singular.topOpenForgottenSingularCochainComplex K Y).iCycles n e =
        F.map (T.iCycles n) (mC.hom e) := by
      rw [← ConcreteCategory.comp_apply]
      exact (ConcreteCategory.congr_hom (ShortComplex.mapCyclesIso_hom_iCycles (T.sc n) F) e).symm
    rw [h1]
    change (T.iCycles n).hom (mC.hom (mC.inv d)) = _
    rw [Iso.inv_hom_id_apply]
    exact ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i i.hom n) c
  · rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply]
    change HomologicalComplex.homologyMap G.inv n
        ((AlgebraicTopology.Singular.topOpenForgottenSingularCochainHomologyIso K Y n).inv
          (F.map (HomologicalComplex.homologyMap i.hom n)
            (((AlgebraicTopology.Singular.SingularCochainComplex K Y).homologyπ n).hom c))) = _
    congr 1
    have h2 : F.map (HomologicalComplex.homologyMap i.hom n)
        (((AlgebraicTopology.Singular.SingularCochainComplex K Y).homologyπ n).hom c) =
        F.map (T.homologyπ n) d :=
      ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality i.hom n) c
    have h3 : ((T.sc n).mapHomologyIso F).hom (((T.sc n).map F).homologyπ e) =
        F.map (T.homologyπ n) d := by
      have := ConcreteCategory.congr_hom (HodgeLean.RealDefs.homologyπ_mapHomologyIso_hom (T.sc n) F) e
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
      rw [this]
      change F.map (T.homologyπ n) (mC.hom (mC.inv d)) = _
      rw [Iso.inv_hom_id_apply]
    rw [h2, ← h3]
    exact Iso.hom_inv_id_apply _ _

end SingularClass

/-- A chain map sends the class of a cycle to the class of its image. -/
lemma cupLeft_addCommGrp_homologyMap_homologyπ_apply {ι : Type*} {cs : ComplexShape ι}
    {K L : HomologicalComplex AddCommGrpCat cs} (f : K ⟶ L) (n : ι)
    (c : K.cycles n) :
    HomologicalComplex.homologyMap f n (K.homologyπ n c) =
      L.homologyπ n (HomologicalComplex.cyclesMap f n c) := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]

/-- The cycle map is the chain map on underlying elements. -/
lemma cupLeft_addCommGrp_iCycles_cyclesMap_apply {ι : Type*} {cs : ComplexShape ι}
    {K L : HomologicalComplex AddCommGrpCat cs} (f : K ⟶ L) (n : ι)
    (c : K.cycles n) :
    L.iCycles n (HomologicalComplex.cyclesMap f n c) = f.f n (K.iCycles n c) := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]

/-- `extendHomologyIso` on the class of a cycle. -/
lemma cupLeft_addCommGrp_extendHomologyIso_inv_homologyπ_apply (K : CochainComplex AddCommGrpCat ℕ)
    (n : ℕ)
    (d : K.cycles n) :
    (K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).inv (K.homologyπ n d) =
      (K.extend ComplexShape.embeddingUpNat).homologyπ n
        ((K.extendCyclesIso ComplexShape.embeddingUpNat (j := n) rfl).inv d) := by
  have h := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_extendHomologyIso_inv K
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl) d
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

/-- `extendCyclesIso` on underlying elements. -/
lemma cupLeft_addCommGrp_iCycles_extendCyclesIso_inv_apply (K : CochainComplex AddCommGrpCat ℕ)
    (n : ℕ)
    (d : K.cycles n) :
    (K.extend ComplexShape.embeddingUpNat).iCycles n
        ((K.extendCyclesIso ComplexShape.embeddingUpNat (j := n) rfl).inv d) =
      (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl).inv (K.iCycles n d) := by
  have h := ConcreteCategory.congr_hom (HomologicalComplex.extendCyclesIso_inv_iCycles K
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl) d
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

/-- Cycles with the same underlying element are equal. -/
lemma cupLeft_addCommGrp_cycles_ext {K : CochainComplex AddCommGrpCat ℤ} {n : ℤ} {c d : K.cycles n}
    (h : K.iCycles n c = K.iCycles n d) : c = d :=
  (AddCommGrpCat.mono_iff_injective (K.iCycles n)).1 inferInstance h




/-- The class in `CohomologyClass` of a cycle of the Hom complex. -/
theorem cupLeft_homologyAddEquiv_homologyπ {C : Type*} [Category* C] [Abelian C]
    (A B : CochainComplex C ℤ) (n : ℤ) (c : (CochainComplex.HomComplex A B).cycles n) :
    ∃ z : CochainComplex.HomComplex.Cocycle A B n,
      CochainComplex.HomComplex.homologyAddEquiv A B n
          ((CochainComplex.HomComplex A B).homologyπ n c) =
        CochainComplex.HomComplex.CohomologyClass.mk z ∧
      z.1 = (CochainComplex.HomComplex A B).iCycles n c := by
  let D := CochainComplex.HomComplex.leftHomologyData A B n
  refine ⟨D.cyclesIso.hom c, ?_, ?_⟩
  · exact ConcreteCategory.congr_hom D.homologyπ_comp_homologyIso_hom c
  · exact ConcreteCategory.congr_hom D.cyclesIso_hom_comp_i c

set_option backward.isDefEq.respectTransparency false in
/-- `singularToSheafHypercohomology` on the class of a cocycle `φ`: the edge-map class of a
cocycle of `Hom^•(ℤ[0], S•)` whose global section is the one represented by `φ`. -/
theorem cupLeft_singularToSheafHypercohomology_cohomologyClass (K : Type) [CommRing K]
    (X : Over (Spec ↧ℂ)) (k : ℕ)
    (φ : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) k) :
    ∃ z : CochainComplex.HomComplex.Cocycle
        (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X)))
        (singularCochainSheafComplexInt X K) k,
      singularToSheafHypercohomology X K k
          (HodgeLean.Foundations.Singular.cohomologyClass _ k φ) =
        HodgeLean.Foundations.cohomologyClassToHypercohomology X _ k
          (CochainComplex.HomComplex.CohomologyClass.mk z) ∧
      (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X))
          (singularCochainSheafComplexInt X K)).hom.f k z.1 =
        (HodgeLean.Foundations.globalSectionsSingularCochainComplexIntIsoExtendField K X).inv.f k
          (((AlgebraicTopology.Singular.globalSingularCochainSheafComplex K
            (TopCat.of (ComplexPoint X))).extendXIso ComplexShape.embeddingUpNat (i := k) rfl).inv
            ((AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex K
              (TopCat.of (ComplexPoint X))).f k (cupLeftRestrict φ.1 (Opposite.op ⊤)))) := by
  let Y := TopCat.of (ComplexPoint X)
  let S := singularCochainSheafComplexInt X K
  let G := AlgebraicTopology.Singular.globalSingularCochainSheafComplex K Y
  let tG := AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex K Y
  let gI := HodgeLean.Foundations.globalSectionsSingularCochainComplexIntIsoExtendField K X
  let hI := TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y S
  obtain ⟨c0, hc0i, hc0⟩ := cupLeft_exists_cohomologyClass_eq_homologyπ Y K k φ
  obtain ⟨c', hc'i, hc'⟩ := cupLeft_ordinarySingularCohomologyEquivGlobalRaw_homologyπ Y K k c0
  let w := HomologicalComplex.cyclesMap hI.inv k (HomologicalComplex.cyclesMap gI.inv k
    ((G.extendCyclesIso ComplexShape.embeddingUpNat (j := k) rfl).inv
      (HomologicalComplex.cyclesMap tG k c')))
  obtain ⟨z, hz, hz1⟩ := cupLeft_homologyAddEquiv_homologyπ _ S k w
  refine ⟨z, ?_, ?_⟩
  · change HodgeLean.Foundations.cohomologyClassToHypercohomology X S k
      (CochainComplex.HomComplex.homologyAddEquiv _ S k
        (HomologicalComplex.homologyMap hI.inv k (HomologicalComplex.homologyMap gI.inv k
          ((G.extendHomologyIso ComplexShape.embeddingUpNat (j := k) rfl).inv
            (HomologicalComplex.homologyMap tG k
              (AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw K Y k
                (HodgeLean.Foundations.Singular.cohomologyClass _ k φ))))))) = _
    rw [hc0, hc', cupLeft_addCommGrp_homologyMap_homologyπ_apply,
      cupLeft_addCommGrp_extendHomologyIso_inv_homologyπ_apply,
      cupLeft_addCommGrp_homologyMap_homologyπ_apply,
      cupLeft_addCommGrp_homologyMap_homologyπ_apply, hz]
  · rw [hz1, cupLeft_addCommGrp_iCycles_cyclesMap_apply, ← ConcreteCategory.comp_apply,
      ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f,
      ConcreteCategory.id_apply, cupLeft_addCommGrp_iCycles_cyclesMap_apply,
      cupLeft_addCommGrp_iCycles_extendCyclesIso_inv_apply,
      cupLeft_addCommGrp_iCycles_cyclesMap_apply, hc'i, hc0i]
    rfl

section ActionOnClass

universe w

/-- Composing the localized class of a cocycle `z` of degree `n` with a degree-`a` morphism `g`
gives the localized class of the composite cocycle. -/
theorem cupLeft_toSmallShiftedHom_comp_mk {C : Type*} [Category* C] [Abelian C]
    {F L : CochainComplex C ℤ} {n a m : ℤ} (g : L ⟶ L⟦a⟧) (h : a + n = m)
    [Localization.HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ F L]
    [Localization.HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ L L]
    (z : CochainComplex.HomComplex.Cocycle F L n) :
    (CochainComplex.HomComplex.CohomologyClass.mk z).toSmallShiftedHom.comp
        (Localization.SmallShiftedHom.mk _ g) h =
      (CochainComplex.HomComplex.CohomologyClass.mk
        (CochainComplex.HomComplex.Cocycle.equivHomShift
          (ShiftedHom.comp (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z :
            ShiftedHom F L n) g h))).toSmallShiftedHom := by
  let := HasDerivedCategory.standard C
  apply (Localization.SmallShiftedHom.equiv _ DerivedCategory.Q).injective
  rw [Localization.SmallShiftedHom.equiv_comp,
    CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk,
    CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk,
    Localization.SmallShiftedHom.equiv_mk, AddEquiv.symm_apply_apply, ShiftedHom.map_comp]

local instance cupLeftProofsHasDerivedCategory (X : Over (Spec ↧ℂ)) :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

set_option maxHeartbeats 400000 in
/-- A degree-one morphism `g : S ⟶ S⟦1⟧` acts on the edge-map class of a cocycle `z` of
`Hom^•(ℤ[0], S)` by the class of the composite cocycle. -/
theorem cupLeft_cohomologyClassToHypercohomology_comp (X : Over (Spec ↧ℂ))
    (S : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (g : S ⟶ S⟦(1 : ℤ)⟧) {n m : ℤ}
    (h : 1 + n = m)
    (z : CochainComplex.HomComplex.Cocycle
      (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) S n) :
    (HodgeLean.Foundations.cohomologyClassToHypercohomology X S n
        (CochainComplex.HomComplex.CohomologyClass.mk z)).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X) g) h =
      HodgeLean.Foundations.cohomologyClassToHypercohomology X S m
        (CochainComplex.HomComplex.CohomologyClass.mk
          (CochainComplex.HomComplex.Cocycle.equivHomShift
            (ShiftedHom.comp (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z :
              ShiftedHom _ S n) g h))) := by
  have key : (CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom.{1}
      (CochainComplex.HomComplex.CohomologyClass.mk z)).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X) g) h =
      CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom.{1}
        (CochainComplex.HomComplex.CohomologyClass.mk
          (CochainComplex.HomComplex.Cocycle.equivHomShift
            (ShiftedHom.comp (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z :
              ShiftedHom _ S n) g h))) :=
    cupLeft_toSmallShiftedHom_comp_mk g h z
  apply (Localization.SmallShiftedHom.equiv _ DerivedCategory.Q).injective
  dsimp only [HodgeLean.Foundations.cohomologyClassToHypercohomology, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_comp,
    ShiftedHom.comp_assoc _ _ _ (add_zero n) h (by omega)]
  have key2 := congrArg (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q) key
  rw [Localization.SmallShiftedHom.equiv_comp] at key2
  rw [key2]


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
theorem cupLeft_homComplexSingleIntegerIsoGlobalSections_hom_f {Y : TopCat.{0}}
    (S : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) (n : ℤ)
    (c : CochainComplex.HomComplex.Cochain (TopCat.Sheaf.integerConstantSingleComplex Y) S n) :
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y S).hom.f n c =
      TopCat.Sheaf.integerConstantHomAddEquivGlobalSections _
        (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n) c) := by
  dsimp [TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections,
    CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The global section of the composite cocycle is the image under `g` of the global section of
`z`. -/
theorem cupLeft_homComplexSingleIntegerIsoGlobalSections_equivHomShift_comp {Y : TopCat.{0}}
    (S : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) (g : S ⟶ S⟦(1 : ℤ)⟧) {n m : ℤ}
    (h : 1 + n = m)
    (z : CochainComplex.HomComplex.Cocycle (TopCat.Sheaf.integerConstantSingleComplex Y) S n) :
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y S).hom.f m
        (CochainComplex.HomComplex.Cocycle.equivHomShift
          (ShiftedHom.comp (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z :
            ShiftedHom _ S n) g h)).1 =
      (g.f n ≫ (S.XIsoOfEq (show n + 1 = m by omega)).hom).hom.app (Opposite.op ⊤)
        ((TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y S).hom.f n z.1) := by
  rw [cupLeft_homComplexSingleIntegerIsoGlobalSections_hom_f,
    cupLeft_homComplexSingleIntegerIsoGlobalSections_hom_f]
  rw [← TopCat.Sheaf.integerConstantHomAddEquivGlobalSections_naturality]
  congr 1
  simp [CochainComplex.HomComplex.Cochain.fromSingleEquiv,
    CochainComplex.HomComplex.Cocycle.equivHomShift_apply,
    CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply, ShiftedHom.comp,
    CochainComplex.HomComplex.Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero 0),
    CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctorAdd'_inv_app_f']
  rw [CochainComplex.HomComplex.Cochain.rightShift_v z.1 n 0 (zero_add n) 0 0 (add_zero 0) n
    (zero_add n)]
  simp only [CochainComplex.shiftFunctorObjXIso, Category.assoc]
  have key : ∀ (p : ℤ) (hp : p = n) (e : p + 1 = m),
      (S.XIsoOfEq hp).inv ≫ g.f p ≫ (S.XIsoOfEq e).hom =
        g.f n ≫ (S.XIsoOfEq (show n + 1 = m by omega)).hom := by
    intro p hp e
    subst hp
    simp
  rw [key]

end ActionOnClass

/-- The inverse of the extension comparison, in a degree coming from the original complex. -/
lemma cupLeft_mapExtendCanonicalIso_inv_f {C D I J : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [Limits.HasZeroObject C] [Limits.HasZeroObject D]
    {c : ComplexShape I} {c' : ComplexShape J} (F : C ⥤ D) [F.Additive]
    (K : HomologicalComplex C c) (e : c.Embedding c') {i : I} {j : J} (h : e.f i = j) :
    (HomologicalComplex.mapExtendCanonicalIso F K e).inv.f j =
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom ≫
        F.map (K.extendXIso e h).inv := by
  rw [← cancel_epi ((HomologicalComplex.mapExtendCanonicalIso F K e).hom.f j),
    ← HomologicalComplex.comp_f, Iso.hom_inv_id,
    HomologicalComplex.mapExtendCanonicalIso_hom_f F K e h]
  simp [← F.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse of `globalSectionsSingularCochainComplexIntIsoExtendField` in degree `j ≥ 0`. -/
theorem cupLeft_globalSectionsSingularCochainComplexIntIsoExtendField_inv_f (K : Type)
    [CommRing K] (X : Over (Spec ↧ℂ)) (j : ℕ)
    (y : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj
        ((AlgebraicTopology.Singular.singularCochainSheafComplex K
          (TopCat.of (ComplexPoint X))).X j)) :
    (HodgeLean.Foundations.globalSectionsSingularCochainComplexIntIsoExtendField K X).inv.f
        (j : ℤ)
        (((AlgebraicTopology.Singular.globalSingularCochainSheafComplex K
          (TopCat.of (ComplexPoint X))).extendXIso ComplexShape.embeddingUpNat
            (i := j) rfl).inv y) =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
          ((AlgebraicTopology.Singular.singularCochainSheafComplex K
            (TopCat.of (ComplexPoint X))).extendXIso ComplexShape.embeddingUpNat (i := j) rfl).inv)
        y := by
  dsimp only [HodgeLean.Foundations.globalSectionsSingularCochainComplexIntIsoExtendField,
    Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv]
  rw [HomologicalComplex.comp_f]
  erw [HomologicalComplex.extendMap_f _ _ (i := j) rfl,
    cupLeft_mapExtendCanonicalIso_inv_f _ _ _ (i := j) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ConcreteCategory.comp_apply]
  erw [Iso.inv_hom_id_apply]
  rfl

theorem cupLeft_extendXIso_inv_comp_XIsoOfEq {K : Type} [CommRing K] {Y : TopCat.{0}}
    {j : ℕ} {i₁ i₂ : ℤ} (h₁ : ComplexShape.embeddingUpNat.f j = i₁) (h : i₁ = i₂) :
    ((AlgebraicTopology.Singular.singularCochainSheafComplex K Y).extendXIso
        ComplexShape.embeddingUpNat h₁).inv ≫
      (((AlgebraicTopology.Singular.singularCochainSheafComplex K Y).extend
        ComplexShape.embeddingUpNat).XIsoOfEq h).hom =
      ((AlgebraicTopology.Singular.singularCochainSheafComplex K Y).extendXIso
        ComplexShape.embeddingUpNat (h₁.trans h)).inv := by
  subst h
  simp

set_option backward.isDefEq.respectTransparency false in
/-- On global sections, the component of `cupLeftComplexHom X a` sends the section represented
by a cochain `φ` to the section represented by `a ∪ φ`. -/
theorem cupLeft_cupLeftComplexHom_globalSection (K : Type) [CommRing K] (X : Over (Spec ↧ℂ))
    (a : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1) (k : ℕ)
    (φ : Cochain K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) k) :
    (((cupLeftComplexHom X a).f (k : ℤ) ≫ ((singularCochainSheafComplexInt X K).XIsoOfEq
        (show (k : ℤ) + 1 = ((1 + k : ℕ) : ℤ) by push_cast; ring)).hom).hom.app (Opposite.op ⊤))
        ((HodgeLean.Foundations.globalSectionsSingularCochainComplexIntIsoExtendField K X).inv.f k
          (((AlgebraicTopology.Singular.globalSingularCochainSheafComplex K
            (TopCat.of (ComplexPoint X))).extendXIso ComplexShape.embeddingUpNat (i := k) rfl).inv
            ((AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex K
              (TopCat.of (ComplexPoint X))).f k (cupLeftRestrict φ (Opposite.op ⊤))))) =
      (HodgeLean.Foundations.globalSectionsSingularCochainComplexIntIsoExtendField K X).inv.f
          ((1 + k : ℕ) : ℤ)
        (((AlgebraicTopology.Singular.globalSingularCochainSheafComplex K
          (TopCat.of (ComplexPoint X))).extendXIso ComplexShape.embeddingUpNat (i := 1 + k) rfl).inv
          ((AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex K
            (TopCat.of (ComplexPoint X))).f (1 + k)
            (cupLeftRestrict (HodgeLean.Foundations.Singular.cupCochain _ 1 k a.1 φ)
              (Opposite.op ⊤)))) := by
  rw [cupLeft_globalSectionsSingularCochainComplexIntIsoExtendField_inv_f,
    cupLeft_globalSectionsSingularCochainComplexIntIsoExtendField_inv_f,
    ← spec_cupLeftGlobalHom_topOpen_aux]
  generalize (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex K
    (TopCat.of (ComplexPoint X))).f k (cupLeftRestrict φ (Opposite.op ⊤)) = x
  have hm : ((AlgebraicTopology.Singular.singularCochainSheafComplex K
        (TopCat.of (ComplexPoint X))).extendXIso ComplexShape.embeddingUpNat (i' := (k : ℤ))
          (i := k) rfl).inv ≫
        (cupLeftComplexHom X a).f (k : ℤ) ≫ ((singularCochainSheafComplexInt X K).XIsoOfEq
          (show (k : ℤ) + 1 = ((1 + k : ℕ) : ℤ) by push_cast; ring)).hom =
      cupLeftSheafHomX a.1 k ≫ ((AlgebraicTopology.Singular.singularCochainSheafComplex K
        (TopCat.of (ComplexPoint X))).extendXIso ComplexShape.embeddingUpNat
          (i' := ((1 + k : ℕ) : ℤ)) (i := 1 + k) rfl).inv := by
    change _ ≫ cupLeftSheafComplexHomF a.1 (k : ℤ) ≫ _ = _
    rw [cupLeftSheafComplexHomF_natCast]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact congrArg (cupLeftSheafHomX a.1 k ≫ ·) (cupLeft_extendXIso_inv_comp_XIsoOfEq _ _)
  change ((_ ≫ (cupLeftComplexHom X a).f (k : ℤ) ≫ ((singularCochainSheafComplexInt X K).XIsoOfEq
          (show (k : ℤ) + 1 = ((1 + k : ℕ) : ℤ) by push_cast; ring)).hom).hom.app
      (Opposite.op ⊤)) x = ((cupLeftSheafHomX a.1 k ≫ _).hom.app (Opposite.op ⊤)) x
  rw [hm]

section CupDefs
variable {K : Type} [CommRing K] {Y : TopCat.{0}}

/-- The cup `a ∪ φ` of a singular `1`-cocycle with a `k`-cocycle, as a `(1 + k)`-cocycle.
Source: Hatcher, *Algebraic Topology*, §3.2, Lemma 3.6 (the cup of cocycles is a cocycle). -/
def cupLeftCocycle (a : Cocycle K (TopCat.toSSet.obj Y) 1) {k : ℕ}
    (φ : Cocycle K (TopCat.toSSet.obj Y) k) : Cocycle K (TopCat.toSSet.obj Y) (1 + k) :=
  ⟨HodgeLean.Foundations.Singular.cupCochain Y 1 k a.1 φ.1, by
    change coboundary K (1 + k) (HodgeLean.Foundations.Singular.cupCochain Y 1 k a.1 φ.1) = 0
    rw [HodgeLean.Foundations.Singular.coboundary_cupCochain,
      show coboundary K 1 a.1 = 0 from a.2, show coboundary K k φ.1 = 0 from φ.2]
    simp⟩

example (a : Cocycle K (TopCat.toSSet.obj Y) 1) {k : ℕ} (φ : Cocycle K (TopCat.toSSet.obj Y) k) :
    (cupLeftCocycle a φ).1 = HodgeLean.Foundations.Singular.cupCochain Y 1 k a.1 φ.1 := rfl

/-- `[a] ∪ [φ] = [a ∪ φ]`. -/
theorem cup_cohomologyClass_cupLeftCocycle (a : Cocycle K (TopCat.toSSet.obj Y) 1) {k : ℕ}
    (φ : Cocycle K (TopCat.toSSet.obj Y) k) :
    HodgeLean.Foundations.Singular.cup Y rfl
        (HodgeLean.Foundations.Singular.cohomologyClass Y 1 a)
        (HodgeLean.Foundations.Singular.cohomologyClass Y k φ) =
      HodgeLean.Foundations.Singular.cohomologyClass Y (1 + k) (cupLeftCocycle a φ) := by
  simp only [HodgeLean.Foundations.Singular.cup, HodgeLean.Foundations.Singular.cohomologyClass]
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
  erw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  rfl


end CupDefs

theorem spec_cupLeftHypercohomology_singularToSheafHypercohomology_aux (K : Type) [CommRing K]
    (X : Over (Spec ↧ℂ)) (a : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ))
    (y : AlgebraicTopology.Singular.Cohomology K (TopCat.of (ComplexPoint X)) k) :
    cupLeftHypercohomology X a h (singularToSheafHypercohomology X K k y) =
      singularToSheafHypercohomology X K (1 + k)
        (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint X)) rfl
          (HodgeLean.Foundations.Singular.cohomologyClass _ 1 a) y) := by
  obtain ⟨φ, rfl⟩ := HodgeLean.Foundations.Singular.cohomologyClass_surjective _ k y
  rw [cup_cohomologyClass_cupLeftCocycle]
  obtain ⟨z, hz, hzs⟩ := cupLeft_singularToSheafHypercohomology_cohomologyClass K X k φ
  obtain ⟨z₂, hz₂, hz₂s⟩ :=
    cupLeft_singularToSheafHypercohomology_cohomologyClass K X (1 + k) (cupLeftCocycle a φ)
  rw [hz, hz₂]
  change (HodgeLean.Foundations.cohomologyClassToHypercohomology X _ k
      (CochainComplex.HomComplex.CohomologyClass.mk z)).comp
      (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X) (cupLeftComplexHom X a)) h = _
  rw [cupLeft_cohomologyClassToHypercohomology_comp]
  congr 2
  apply CochainComplex.HomComplex.Cocycle.ext
  apply (AddCommGrpCat.mono_iff_injective
    ((TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X))
      (singularCochainSheafComplexInt X K)).hom.f ((1 + k : ℕ) : ℤ))).1 inferInstance
  rw [cupLeft_homComplexSingleIntegerIsoGlobalSections_equivHomShift_comp, hzs, hz₂s]
  exact cupLeft_cupLeftComplexHom_globalSection K X a k φ.1

set_option backward.isDefEq.respectTransparency false in
theorem spec_cupLeftSheafComplexHom_zero_aux {K : Type} [CommRing K] {Y : TopCat.{0}}
    (h0 : coboundary K 1 (0 : Cochain K (TopCat.toSSet.obj Y) 1) = 0) :
    cupLeftSheafComplexHom (0 : Cochain K (TopCat.toSSet.obj Y) 1) h0 = 0 := by
  have hp : ∀ n, cupLeftPresheafHom (0 : Cochain K (TopCat.toSSet.obj Y) 1) n = 0 := by
    intro n
    apply NatTrans.ext
    funext U
    ext c
    change HodgeLean.Foundations.Singular.cupCochain _ 1 n (cupLeftRestrict 0 U) c = 0
    rw [cupLeftRestrict, map_zero, map_zero]
    rfl
  ext i
  rcases i with n | n
  · change cupLeftSheafComplexHomF 0 (n : ℤ) = 0
    rw [cupLeftSheafComplexHomF_natCast, cupLeftSheafHomX, cupLeftSheafHom, hp, Functor.map_zero,
      Limits.zero_comp, Limits.comp_zero]
  · rfl

set_option backward.isDefEq.respectTransparency false in
theorem spec_cupLeftSheafComplexHom_add_aux {K : Type} [CommRing K] {Y : TopCat.{0}}
    (a b : Cochain K (TopCat.toSSet.obj Y) 1) (ha : coboundary K 1 a = 0)
    (hb : coboundary K 1 b = 0) (hab : coboundary K 1 (a + b) = 0) :
    cupLeftSheafComplexHom (a + b) hab = cupLeftSheafComplexHom a ha + cupLeftSheafComplexHom b hb := by
  have hp : ∀ n, cupLeftPresheafHom (a + b) n =
      cupLeftPresheafHom a n + cupLeftPresheafHom b n := by
    intro n
    apply NatTrans.ext
    funext U
    ext c
    change HodgeLean.Foundations.Singular.cupCochain _ 1 n (cupLeftRestrict (a + b) U) c =
      HodgeLean.Foundations.Singular.cupCochain _ 1 n (cupLeftRestrict a U) c +
        HodgeLean.Foundations.Singular.cupCochain _ 1 n (cupLeftRestrict b U) c
    rw [cupLeftRestrict, map_add, map_add]
    rfl
  ext i
  rcases i with n | n
  · change cupLeftSheafComplexHomF (a + b) (n : ℤ) =
      cupLeftSheafComplexHomF a (n : ℤ) + cupLeftSheafComplexHomF b (n : ℤ)
    rw [cupLeftSheafComplexHomF_natCast, cupLeftSheafComplexHomF_natCast,
      cupLeftSheafComplexHomF_natCast, cupLeftSheafHomX, cupLeftSheafHomX, cupLeftSheafHomX,
      cupLeftSheafHom, cupLeftSheafHom, cupLeftSheafHom, hp, Functor.map_add,
      Preadditive.add_comp, Preadditive.comp_add]
  · change (0 : _ ⟶ _) = 0 + 0
    rw [add_zero]

section CoboundaryHomotopy

variable {K : Type} [CommRing K] {Y : TopCat.{0}}

set_option backward.isDefEq.respectTransparency false in
/-- Left cup with a singular `0`-cochain `b` on `Y`, on the presheaves of singular cochains:
`c ↦ b|_U ∪ c`.
Source: Hatcher, *Algebraic Topology*, §3.2 (cup product and its naturality). -/
def cupLeftZeroPresheafHom (b : Cochain K (TopCat.toSSet.obj Y) 0) (n : ℕ) :
    singularCochainPresheaf K Y n ⟶ singularCochainPresheaf K Y (0 + n) where
  app U := AddCommGrpCat.ofHom
    (HodgeLean.Foundations.Singular.cupCochain ((Opens.toTopCat Y).obj U.unop) 0 n
      (cupLeftRestrict b U)).toAddMonoidHom
  naturality {U V} i := by
    ext c
    change HodgeLean.Foundations.Singular.cupCochain _ 0 n (cupLeftRestrict b V)
        (cochainMap K (TopCat.toSSet.map ((Opens.toTopCat Y).map i.unop)) n c) =
      cochainMap K (TopCat.toSSet.map ((Opens.toTopCat Y).map i.unop)) (0 + n)
        (HodgeLean.Foundations.Singular.cupCochain _ 0 n (cupLeftRestrict b U) c)
    rw [HodgeLean.Foundations.Singular.cupCochain_naturality, ← cupLeftRestrict_map b i]
    rfl

example (b : Cochain K (TopCat.toSSet.obj Y) 0) (n : ℕ) (U : (Opens Y)ᵒᵖ)
    (c : OpenCochains K Y U n) :
    (cupLeftZeroPresheafHom b n).app U c =
      HodgeLean.Foundations.Singular.cupCochain _ 0 n (cupLeftRestrict b U) c := rfl

/-- `eqToHom` between presheaves of singular cochains of equal degrees precomposes with the
reindexing of chains. -/
theorem cupLeft_eqToHom_app {m₁ m₂ : ℕ} (hm : m₁ = m₂) (U : (Opens Y)ᵒᵖ)
    (c : OpenCochains K Y U m₁) :
    (eqToHom (congrArg (singularCochainPresheaf K Y) hm)).app U c =
      c.comp ((((TopCat.toSSet.obj ((Opens.toTopCat Y).obj U.unop)).chainComplex
        (ModuleCat.of K K)).XIsoOfEq hm.symm).hom.hom) := by
  subst hm
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf form of the homotopy `C_{δb} = δ ∘ B + B ∘ δ`, for `B = b ∪ ·`, with the degree
casts. -/
theorem cupLeftPresheafHom_coboundary (b : Cochain K (TopCat.toSSet.obj Y) 0) (n : ℕ) :
    cupLeftPresheafHom (coboundary K 0 b) n =
      cupLeftZeroPresheafHom b n ≫ AlgebraicTopology.Singular.singularCochainCoboundary K Y (0 + n) ≫
          eqToHom (congrArg (singularCochainPresheaf K Y) (by omega)) -
        AlgebraicTopology.Singular.singularCochainCoboundary K Y n ≫ cupLeftZeroPresheafHom b (n + 1) ≫
          eqToHom (congrArg (singularCochainPresheaf K Y) (by omega)) := by
  apply NatTrans.ext
  funext U
  ext c
  change HodgeLean.Foundations.Singular.cupCochain _ 1 n (cupLeftRestrict (coboundary K 0 b) U) c =
    (eqToHom (congrArg (singularCochainPresheaf K Y) (show 0 + n + 1 = 1 + n by omega))).app U
        (coboundary K (0 + n)
          (HodgeLean.Foundations.Singular.cupCochain _ 0 n (cupLeftRestrict b U) c)) -
      (eqToHom (congrArg (singularCochainPresheaf K Y) (show 0 + (n + 1) = 1 + n by omega))).app U
        (HodgeLean.Foundations.Singular.cupCochain _ 0 (n + 1) (cupLeftRestrict b U)
          (coboundary K n c))
  rw [cupLeft_eqToHom_app (show 0 + n + 1 = 1 + n by omega),
    cupLeft_eqToHom_app (show 0 + (n + 1) = 1 + n by omega),
    HodgeLean.Foundations.Singular.coboundary_cupCochain]
  have hr : coboundary K 0 (cupLeftRestrict b U) = cupLeftRestrict (coboundary K 0 b) U := by
    rw [cupLeftRestrict, HodgeLean.Foundations.Simplicial.coboundary_cochainMap]
    rfl
  rw [hr, pow_zero, one_smul, LinearMap.add_comp, add_sub_cancel_right, LinearMap.comp_assoc,
    reassocChain, ← ModuleCat.hom_comp, HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom,
    HomologicalComplex.XIsoOfEq_rfl]
  rfl


/-- Left cup with a singular `0`-cochain `b`, between the terms of the sheaf complex: the
sheafification of `cupLeftZeroPresheafHom b n`.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, I.5 and III.1; Hatcher, *Algebraic Topology*,
§3.2 (cup product). -/
def cupLeftZeroSheafHomX (b : Cochain K (TopCat.toSSet.obj Y) 0) (n : ℕ) :
    (singularCochainSheafComplex K Y).X n ⟶ (singularCochainSheafComplex K Y).X (0 + n) :=
  (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map (cupLeftZeroPresheafHom b n)

example (n : ℕ) : cupLeftZeroSheafHomX (0 : Cochain K (TopCat.toSSet.obj Y) 0) n =
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
      (cupLeftZeroPresheafHom 0 n) := rfl

/-- The sheaf form of the homotopy `C_{δb} = δ ∘ B + B ∘ δ`, with the degree casts. -/
theorem cupLeftSheafHomX_coboundary (b : Cochain K (TopCat.toSSet.obj Y) 0) (n : ℕ) :
    cupLeftSheafHomX (coboundary K 0 b) n =
      cupLeftZeroSheafHomX b n ≫ (singularCochainSheafComplex K Y).d (0 + n) (0 + n + 1) ≫
          ((singularCochainSheafComplex K Y).XIsoOfEq (show 0 + n + 1 = 1 + n by omega)).hom -
        (singularCochainSheafComplex K Y).d n (n + 1) ≫ cupLeftZeroSheafHomX b (n + 1) ≫
          ((singularCochainSheafComplex K Y).XIsoOfEq (show 0 + (n + 1) = 1 + n by omega)).hom := by
  have h := congrArg (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
    (cupLeftPresheafHom_coboundary b n)
  rw [Functor.map_sub, Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    eqToHom_map] at h
  rw [AlgebraicTopology.Singular.singularCochainSheafComplex_d,
    AlgebraicTopology.Singular.singularCochainSheafComplex_d]
  exact h

/-- The homotopy `−(b ∪ ·)` on the integer-indexed sheaf complex, as a family
`S^i ⟶ (S⟦1⟧)^j = S^{j+1}` for `j + 1 = i`: in degree `i = n ≥ 0` it is
`−cupLeftZeroSheafHomX b n`, conjugated by `extendXIso`, and `0` in negative degrees.
Source: Hatcher, *Algebraic Topology*, §3.2, Lemma 3.6 (with `p = 0`); Mathlib's
`HomologicalComplex.extendXIso`. -/
def cupLeftZeroHomotopyF (b : Cochain K (TopCat.toSSet.obj Y) 0) : (i j : ℤ) →
    (ComplexShape.up ℤ).Rel j i →
    (((singularCochainSheafComplex K Y).extend ComplexShape.embeddingUpNat).X i ⟶
      (((singularCochainSheafComplex K Y).extend ComplexShape.embeddingUpNat)⟦(1 : ℤ)⟧).X j)
  | Int.ofNat n, j, hij =>
      -(((singularCochainSheafComplex K Y).extendXIso ComplexShape.embeddingUpNat
          (i := n) rfl).hom ≫ cupLeftZeroSheafHomX b n ≫
        ((singularCochainSheafComplex K Y).extendXIso ComplexShape.embeddingUpNat
          (i' := j + 1) (i := 0 + n) (by simp at hij ⊢; omega)).inv)
  | Int.negSucc _, _, _ => 0

example (b : Cochain K (TopCat.toSSet.obj Y) 0) (j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel j (Int.negSucc 0)) :
    cupLeftZeroHomotopyF b (Int.negSucc 0) j hij = 0 := rfl

theorem cupLeftZeroHomotopyF_natCast (b : Cochain K (TopCat.toSSet.obj Y) 0) (n : ℕ) (j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel j (n : ℤ)) :
    cupLeftZeroHomotopyF b (n : ℤ) j hij =
      -(((singularCochainSheafComplex K Y).extendXIso ComplexShape.embeddingUpNat
          (i' := (n : ℤ)) (i := n) rfl).hom ≫ cupLeftZeroSheafHomX b n ≫
        ((singularCochainSheafComplex K Y).extendXIso ComplexShape.embeddingUpNat
          (i' := j + 1) (i := 0 + n) (by simp at hij ⊢; omega)).inv) := rfl

theorem cupLeft_XIsoOfEq_hom_comp_extendXIso_inv {m₁ m₂ : ℕ} (hm : m₁ = m₂) {i' : ℤ}
    (h₂ : ComplexShape.embeddingUpNat.f m₂ = i') :
    ((singularCochainSheafComplex K Y).XIsoOfEq hm).hom ≫
        ((singularCochainSheafComplex K Y).extendXIso ComplexShape.embeddingUpNat h₂).inv =
      ((singularCochainSheafComplex K Y).extendXIso ComplexShape.embeddingUpNat
        (i := m₁) (by rw [hm]; exact h₂)).inv := by
  subst hm
  simp

/-- `C_{δb}` is the null-homotopic map of the homotopy `−(b ∪ ·)`. -/
theorem cupLeftSheafComplexHom_coboundary (b : Cochain K (TopCat.toSSet.obj Y) 0)
    (ha : coboundary K 1 (coboundary K 0 b) = 0) :
    cupLeftSheafComplexHom (coboundary K 0 b) ha =
      Homotopy.nullHomotopicMap' (cupLeftZeroHomotopyF b) := by
  ext i : 1
  rcases lt_or_ge i 0 with hi | hi
  · refine Limits.IsZero.eq_of_src
      (HomologicalComplex.isZero_extend_X _ _ _ fun k hk => ?_) _ _
    simp at hk
    omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  rw [Homotopy.nullHomotopicMap'_f (k₂ := (n : ℤ) - 1) (k₀ := ((n + 1 : ℕ) : ℤ))
    (by simp) (by simp)]
  rw [cupLeftZeroHomotopyF_natCast, cupLeftZeroHomotopyF_natCast]
  change cupLeftSheafComplexHomF _ (n : ℤ) = _
  rw [cupLeftSheafComplexHomF_natCast, CochainComplex.shiftFunctor_obj_d']
  dsimp only
  rw [HomologicalComplex.extend_d_eq _ _ (i' := (n : ℤ)) (j' := ((n + 1 : ℕ) : ℤ))
      (i := n) (j := n + 1) rfl rfl,
    HomologicalComplex.extend_d_eq _ _ (i' := (n : ℤ) - 1 + 1) (j' := (n : ℤ) + 1)
      (i := 0 + n) (j := 0 + n + 1) (by simp) (by simp)]
  simp only [Int.negOnePow_one, Units.neg_smul, one_smul, Category.assoc, Iso.inv_hom_id_assoc,
    Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, cupLeftSheafHomX_coboundary,
    Preadditive.sub_comp, Preadditive.comp_sub, cupLeft_XIsoOfEq_hom_comp_extendXIso_inv]
  exact sub_eq_neg_add _ _

end CoboundaryHomotopy

theorem spec_cupLeftHypercohomology_eq_zero_of_coboundary_aux (K : Type) [CommRing K]
    (X : Over (Spec ↧ℂ)) (a : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (b : Cochain K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 0)
    (hab : a.1 = coboundary K 0 b) {n m : ℤ} (h : 1 + n = m)
    (α : Hypercohomology X (singularCochainSheafComplexInt X K) n) :
    cupLeftHypercohomology X a h α = 0 := by
  let := HasDerivedCategory.standard (AnalyticAdditiveSheaf X)
  have hQ : DerivedCategory.Q.map (cupLeftComplexHom X a) = 0 := by
    obtain ⟨a, ha⟩ := a
    dsimp only at hab
    subst hab
    change DerivedCategory.Q.map (cupLeftSheafComplexHom (coboundary K 0 b) _) = 0
    rw [cupLeftSheafComplexHom_coboundary,
      DerivedCategory.Q_map_eq_of_homotopy (h := Homotopy.nullHomotopy' _), Functor.map_zero]
  apply (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q).injective
  change Localization.SmallShiftedHom.equiv _ _ (α.comp
    (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X) (cupLeftComplexHom X a)) h) = _
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk,
    hypercohomologyEquiv_zero, ShiftedHom.map, hQ, Limits.zero_comp, ShiftedHom.comp_zero]

theorem spec_cupLeftHypercohomology_ne_zero_aux (K : Type) [CommRing K]
    (X : Over (Spec ↧ℂ)) (a : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ))
    (y : AlgebraicTopology.Singular.Cohomology K (TopCat.of (ComplexPoint X)) k)
    (hinj : Function.Injective (singularToSheafHypercohomology X K (1 + k)))
    (hne : HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint X)) rfl
      (HodgeLean.Foundations.Singular.cohomologyClass _ 1 a) y ≠ 0) :
    cupLeftHypercohomology X a h (singularToSheafHypercohomology X K k y) ≠ 0 := by
  rw [spec_cupLeftHypercohomology_singularToSheafHypercohomology_aux K X a k h y]
  intro h0
  apply hne
  apply hinj
  rw [h0, map_zero]

end HodgeLean.Adapters
