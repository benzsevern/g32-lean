import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SectionRestrictionConeNaturality
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SingularSectionNaturality
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.CohomologyInjectiveModel
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Transport.CohomologySheaf
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportedSingularModel
import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.WithSupport

/-! # Enlarging the support, from sheaf cohomology to relative singular cohomology

For closed sets `S ⊆ T` of `X(ℂ)`, upstream's identification of `H^n_S(X(ℂ); ℚ)` with relative
singular cohomology `H^n(X(ℂ), X(ℂ) \ S; ℚ)`,
`complexSupportInjectiveSectionCohomologyEquiv ∘ rationalSupportAddEquivSupportedInjectiveHomology`,
commutes with enlarging the support: on the sheaf side the map of pairs `relH.restrict`, on the
singular side pullback along `(X, X \ T) → (X, X \ S)` (`supportedSingularClass_restrict`).
Upstream proves naturality in the ambient open; this file proves it in the support, layer by
layer: the Ext model (upstream's `relHAddEquivSupportedSectionsHomology_restrict`), the singular
resolution (`complexSupportedSingularInjectiveHomologyIso_support`), the flasque kernel-to-cone
comparison (`supportedSectionHomologyIsoRestrictionCone_support`) and the cone-to-relative
comparison (upstream's `openSingularSheafRestrictionConeCohomologyEquivRelative_naturality`).
Forgetting the support factors through any larger support (`forgetSupport_restrict`). -/

open CategoryTheory Limits TopologicalSpace Opposite Abelian
open AlgebraicTopology.Singular TopCat.Sheaf

noncomputable section

namespace HodgeLean.RealDefs

section General

variable (X : TopCat.{0})

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of sections along the identity is the identity. -/
lemma sectionComplexRestriction_self {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (TopCat.Sheaf AddCommGrpCat X) c) (V : Opens X) (i : V ⟶ V) :
    sectionComplexRestriction X c K i = 𝟙 _ := by
  obtain rfl : i = 𝟙 V := Subsingleton.elim _ _
  apply HomologicalComplex.hom_ext
  intro n
  exact (K.X n).obj.map_id _

variable {U U' : Opens X} (hU : U' ≤ U) (V : Opens X)
  (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Enlarging the support of `Γ_{X \ U}(V, K) → K(V) → K(V ∩ U)`: the identity on `K(V)` and
restriction to `V ∩ U'`. -/
def supportRestrictionSectionsComplexSupportMap :
    supportRestrictionSectionsComplexShortComplex X U V K ⟶
      supportRestrictionSectionsComplexShortComplex X U' V K where
  τ₁ := ((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
    (((sheafSectionsSupportedOutsideMap X hU).mapHomologicalComplex ℤᵘᵖ).app K)
  τ₂ := 𝟙 _
  τ₃ := ((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
    (((openRestrictionPushforwardMap X hU).mapHomologicalComplex ℤᵘᵖ).app K)
  comm₁₂ := by
    change _ ≫ ((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
        (supportRestrictionComplexShortComplex X U' K).f =
      ((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
        (supportRestrictionComplexShortComplex X U K).f ≫ 𝟙 _
    rw [Category.comp_id, ← Functor.map_comp]
    congr 1
    ext n : 1
    exact NatTrans.congr_app (sheafSectionsSupportedOutsideMap_inclusion X hU) (K.X n)
  comm₂₃ := by
    change 𝟙 _ ≫ ((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
        (supportRestrictionComplexShortComplex X U' K).g =
      ((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
        (supportRestrictionComplexShortComplex X U K).g ≫ _
    rw [Category.id_comp, ← Functor.map_comp]
    congr 1
    ext n : 1
    exact (NatTrans.congr_app (toOpenRestrictionPushforward_comp X hU) (K.X n)).symm

/-- The pushforward/intersection identification commutes with enlarging the support. -/
@[reassoc]
lemma supportedOutsideIntersectionIso_support (F : TopCat.Sheaf AddCommGrpCat X) :
    ((openRestrictionPushforwardMap X hU).app F).hom.app (op V) ≫
      (supportedOutsideIntersectionIso X U' V F).hom =
    (supportedOutsideIntersectionIso X U V F).hom ≫
      F.obj.map (homOfLE (inf_le_inf_left V hU)).op := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  congr 1

/-- Naturality of the intersection identification on coefficient complexes. -/
@[reassoc]
lemma supportRestrictionSectionsIntersectionIso_support :
    (supportRestrictionSectionsComplexSupportMap X hU V K).τ₃ ≫
      (supportRestrictionSectionsIntersectionIso X U' V K).hom =
    (supportRestrictionSectionsIntersectionIso X U V K).hom ≫
      sectionComplexRestriction X ℤᵘᵖ K (homOfLE (inf_le_inf_left V hU)) :=
  HomologicalComplex.Hom.ext
    (funext fun n ↦ supportedOutsideIntersectionIso_support X hU V (K.X n))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cone identification respects enlarging the support. -/
@[reassoc]
lemma supportRestrictionSectionsConeIso_support :
    CochainComplex.mappingCone.map _ _
      (supportRestrictionSectionsComplexSupportMap X hU V K).τ₂
      (supportRestrictionSectionsComplexSupportMap X hU V K).τ₃
      (supportRestrictionSectionsComplexSupportMap X hU V K).comm₂₃.symm ≫
        (supportRestrictionSectionsConeIso X U' V K).hom =
    (supportRestrictionSectionsConeIso X U V K).hom ≫
      sectionComplexRestrictionConeMap X K (Opens.infLELeft V U) (Opens.infLELeft V U')
        (𝟙 V) (homOfLE (inf_le_inf_left V hU)) := by
  rw [supportRestrictionSectionsConeIso_hom, supportRestrictionSectionsConeIso_hom]
  dsimp only [sectionComplexRestrictionConeMap]
  rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
  congr 1
  · rw [sectionComplexRestriction_self]
    rfl
  · exact supportRestrictionSectionsIntersectionIso_support X hU V K

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The flasque kernel-to-cone comparison is natural in the support. -/
@[reassoc]
lemma supportedSectionHomologyIsoRestrictionCone_support
    (hK : ∀ n, (K.X n).IsFlasque) (n : ℤ) :
    HomologicalComplex.homologyMap (supportRestrictionSectionsComplexSupportMap X hU V K).τ₁ n ≫
      (supportedSectionHomologyIsoRestrictionCone X U' V K hK n).hom =
    (supportedSectionHomologyIsoRestrictionCone X U V K hK n).hom ≫
      HomologicalComplex.homologyMap
        (sectionComplexRestrictionConeMap X K (Opens.infLELeft V U) (Opens.infLELeft V U')
          (𝟙 V) (homOfLE (inf_le_inf_left V hU))) (n - 1) := by
  let S := supportRestrictionSectionsComplexShortComplex X U V K
  let T := supportRestrictionSectionsComplexShortComplex X U' V K
  let hS := supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U V K hK
  let hT := supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U' V K hK
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ (n - 1)
  change HomologicalComplex.homologyMap (supportRestrictionSectionsComplexSupportMap X hU V K).τ₁ n ≫
      ((CochainComplex.mappingCocone.shortExactHomologyIsoCone T hT (n - 1) n (by omega)).hom ≫
        H.map (supportRestrictionSectionsConeIso X U' V K).hom) =
    ((CochainComplex.mappingCocone.shortExactHomologyIsoCone S hS (n - 1) n (by omega)).hom ≫
        H.map (supportRestrictionSectionsConeIso X U V K).hom) ≫ _
  rw [CochainComplex.mappingCocone.shortExactHomologyIsoCone_naturality_assoc
    (supportRestrictionSectionsComplexSupportMap X hU V K) hS hT (n - 1) n (by omega)]
  simp only [Category.assoc]
  congr 1
  change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
  rw [← H.map_comp, ← H.map_comp, supportRestrictionSectionsConeIso_support]

end General

section Singular

variable (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
  {U U' : Opens X} (hU : U' ≤ U) (V : Opens X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The supported-section-to-relative equivalence is natural in the support. -/
lemma supportedRationalSingularSectionCohomologyEquivRelative_support (n : ℕ)
    (z : ((((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (supportedRationalSingularCochainComplex X U))).homology (n : ℤ)) :
    supportedRationalSingularSectionCohomologyEquivRelative X U' V n
      (HomologicalComplex.homologyMap
        (supportRestrictionSectionsComplexSupportMap X hU V
          (rationalSingularCochainComplex X)).τ₁ (n : ℤ) z) =
    relativeCohomologyMap ℚ n
      (openInclusionPairMap X (Opens.infLELeft V U) (Opens.infLELeft V U')
        (𝟙 V) (homOfLE (inf_le_inf_left V hU)))
      (supportedRationalSingularSectionCohomologyEquivRelative X U V n z) := by
  change openSingularSheafRestrictionConeCohomologyEquivRelative X (Opens.infLELeft V U') n
      ((supportedSingularSectionConeHomologyIso X U' V (n : ℤ)).hom
        (HomologicalComplex.homologyMap
          (supportRestrictionSectionsComplexSupportMap X hU V
            (rationalSingularCochainComplex X)).τ₁ (n : ℤ) z)) = _
  have h : HomologicalComplex.homologyMap
        (supportRestrictionSectionsComplexSupportMap X hU V
          (rationalSingularCochainComplex X)).τ₁ (n : ℤ) ≫
      (supportedSingularSectionConeHomologyIso X U' V (n : ℤ)).hom =
    (supportedSingularSectionConeHomologyIso X U V (n : ℤ)).hom ≫
      HomologicalComplex.homologyMap
        (openSingularSheafRestrictionConeMap ℚ X (Opens.infLELeft V U) (Opens.infLELeft V U')
          (𝟙 V) (homOfLE (inf_le_inf_left V hU))) ((n : ℤ) - 1) := by
    dsimp only [supportedSingularSectionConeHomologyIso, Iso.trans_hom]
    rw [supportedSectionHomologyIsoRestrictionCone_support_assoc X hU V
      (rationalSingularCochainComplex X)]
    simp only [Category.assoc]
    congr 1
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ ((n : ℤ) - 1)
    change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg H.map (sectionComplexRestrictionExtendConeIso_naturality X
      (singularCochainSheafComplex ℚ X) (Opens.infLELeft V U) (Opens.infLELeft V U')
      (𝟙 V) (homOfLE (inf_le_inf_left V hU)))
  have h' := congrArg (fun f => f z) h
  change (supportedSingularSectionConeHomologyIso X U' V (n : ℤ)).hom
      (HomologicalComplex.homologyMap
        (supportRestrictionSectionsComplexSupportMap X hU V
          (rationalSingularCochainComplex X)).τ₁ (n : ℤ) z) =
    HomologicalComplex.homologyMap
      (openSingularSheafRestrictionConeMap ℚ X (Opens.infLELeft V U) (Opens.infLELeft V U')
        (𝟙 V) (homOfLE (inf_le_inf_left V hU))) ((n : ℤ) - 1)
      ((supportedSingularSectionConeHomologyIso X U V (n : ℤ)).hom z) at h'
  rw [h']
  exact openSingularSheafRestrictionConeCohomologyEquivRelative_naturality X
    (Opens.infLELeft V U) (Opens.infLELeft V U') (𝟙 V)
    (homOfLE (inf_le_inf_left V hU)) n _

/-- Enlarging the support as a map of pairs `(V, V \ T) ⟶ (V, V \ S)`. -/
def neighborhoodSupportEnlargePairMap {M : Type} [TopologicalSpace M] (W : Set M)
    {S T : Set M} (h : S ⊆ T) :
    neighborhoodSupportComplementPair W T ⟶ neighborhoodSupportComplementPair W S :=
  TopPair.ofSubsetHom (𝟙 _) (fun _ hw hS => hw (h hS))

/-- The final support-complement comparison is natural in the support. -/
lemma supportedRationalSingularSectionCohomologyEquivSupportComplement_support
    {S T : Set X} (hS : IsClosed S) (hT : IsClosed T) (hST : S ⊆ T) (n : ℕ)
    (z : ((((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩))).homology (n : ℤ)) :
    supportedRationalSingularSectionCohomologyEquivSupportComplement X T hT V n
      (HomologicalComplex.homologyMap
        (supportRestrictionSectionsComplexSupportMap X
          (show (⟨Tᶜ, hT.isOpen_compl⟩ : Opens X) ≤ ⟨Sᶜ, hS.isOpen_compl⟩ from
            Set.compl_subset_compl.mpr hST) V
          (rationalSingularCochainComplex X)).τ₁ (n : ℤ) z) =
    relativeCohomologyMap ℚ n (neighborhoodSupportEnlargePairMap (V : Set X) hST)
      (supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS V n z) := by
  change relativeCohomologyMap ℚ n (openIntersectionPairIsoSupportComplement X T hT V).inv
      (supportedRationalSingularSectionCohomologyEquivRelative X _ V n _) =
    relativeCohomologyMap ℚ n _
      (relativeCohomologyMap ℚ n (openIntersectionPairIsoSupportComplement X S hS V).inv
        (supportedRationalSingularSectionCohomologyEquivRelative X _ V n z))
  rw [supportedRationalSingularSectionCohomologyEquivRelative_support,
    ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    ← relativeCohomologyMap_comp]
  congr 2

end Singular

section Pair

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (CategoryTheory.Sheaf J AddCommGrpCat.{v})]

/-- Forgetting the relative part after a map of pairs `(V, U') → (V, U)` that is the identity on
`V` is forgetting it directly. -/
lemma relH_forget_restrict (F : CategoryTheory.Sheaf J AddCommGrpCat.{v}) {U U' V : C}
    (f : U ⟶ V) (f' : U' ⟶ V) (a : U' ⟶ U) (w : f' ≫ 𝟙 V = a ≫ f) (n : ℕ)
    (x : CategoryTheory.Sheaf.relH F n f) :
    CategoryTheory.Sheaf.relH.forget F f' n
        (CategoryTheory.Sheaf.relH.restrict F f f' a (𝟙 V) w n x) =
      CategoryTheory.Sheaf.relH.forget F f n x := by
  change (Ext.mk₀ (cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf J).map f'))).comp
      ((Ext.mk₀ (CategoryTheory.Sheaf.pairSheafMap f f' a (𝟙 V) w)).comp x (zero_add n))
        (zero_add n) =
    (Ext.mk₀ (cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf J).map f))).comp x (zero_add n)
  rw [Ext.mk₀_comp_mk₀_assoc]
  congr 2
  simp [CategoryTheory.Sheaf.pairSheafMap, cokernel.map]

end Pair

section ComplexPoint

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance (V : Opens (ComplexPoint X)) : ParacompactSpace V := openParacompactSpace X V

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The singular-to-injective comparison of supported sections is natural in the support. -/
lemma complexSupportedSingularInjectiveHomologyIso_support {U U' : Opens (ComplexPoint X)}
    (hU : U' ≤ U) (V : Opens (ComplexPoint X)) (n : ℤ) :
    HomologicalComplex.homologyMap (supportRestrictionSectionsComplexSupportMap
        (TopCat.of (ComplexPoint X)) hU V
        (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).τ₁ n ≫
      (complexSupportedSingularInjectiveHomologyIso X U' V n).hom =
    (complexSupportedSingularInjectiveHomologyIso X U V n).hom ≫
      HomologicalComplex.homologyMap (supportRestrictionSectionsComplexSupportMap
        (TopCat.of (ComplexPoint X)) hU V (ambientRationalInjectiveComplex X)).τ₁ n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1
  dsimp only [supportRestrictionSectionsComplexSupportMap, supportedSingularToInjectiveComplex]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact (((sheafSectionsSupportedOutsideMap _ hU).mapHomologicalComplex ℤᵘᵖ).naturality _).symm

/-- Rational sheaf cohomology of `X(ℂ)` with support in `S`, as relative singular cohomology
`H^n(X(ℂ), X(ℂ) \ S; ℚ)`: upstream's injective model followed by upstream's singular comparison.
Source: HodgeConjecture `rationalSupportAddEquivSupportedInjectiveHomology` and
`complexSupportInjectiveSectionCohomologyEquiv` (`Cycle/Transport/CohomologySheaf.lean`). -/
def supportedSingularClass (S : Closeds (ComplexPoint X)) (n : ℕ) :
    TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n ≃+
      RelativeCohomology ℚ (neighborhoodSupportComplementPair
        ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X)) (S : Set (ComplexPoint X))) n :=
  (rationalSupportAddEquivSupportedInjectiveHomology X S n).trans
    (complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n)

/-- Enlarging the support from `S` to `T` in sheaf cohomology: the map of pairs
`(X, X \ T) → (X, X \ S)`. -/
abbrev supportEnlarge {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (n : ℕ) :
    TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n →+
      TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) T
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n :=
  CategoryTheory.Sheaf.relH.restrict _ (homOfLE le_top) (homOfLE le_top)
    (homOfLE (show T.compl ≤ S.compl from fun _ hx hS => hx (h hS))) (𝟙 _)
    (Subsingleton.elim _ _) n

set_option maxHeartbeats 400000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Upstream's sheaf-to-singular identification commutes with enlarging the support. -/
theorem supportedSingularClass_restrict {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (n : ℕ)
    (a : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n) :
    supportedSingularClass X T n (supportEnlarge X h n a) =
      relativeCohomologyMap ℚ n (neighborhoodSupportEnlargePairMap _
          (SetLike.coe_subset_coe.mpr h))
        (supportedSingularClass X S n a) := by
  have hU : T.compl ≤ S.compl := fun _ hx hS => hx (h hS)
  have := ambientRationalInjectiveComplex_isKInjective X
  have := ambientRationalInjectiveSingleAugmentation_quasiIso X
  have h1 := relHAddEquivSupportedSectionsHomology_restrict (TopCat.of (ComplexPoint X))
    (top_inf_eq S.compl) (top_inf_eq T.compl) hU (le_refl ⊤) hU
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
    (ambientRationalInjectiveComplex X) (ambientRationalInjectiveSingleAugmentation X) n a
  have hres : supportedSectionsRestriction (TopCat.of (ComplexPoint X)) hU (le_refl ⊤)
      (ambientRationalInjectiveComplex X) =
      (supportRestrictionSectionsComplexSupportMap (TopCat.of (ComplexPoint X)) hU ⊤
        (ambientRationalInjectiveComplex X)).τ₁ := by
    rw [supportedSectionsRestriction, sectionComplexRestriction_self, Category.comp_id]
    rfl
  rw [hres] at h1
  have h3 : rationalSupportAddEquivSupportedInjectiveHomology X T n (supportEnlarge X h n a) =
      HomologicalComplex.homologyMap (supportRestrictionSectionsComplexSupportMap
        (TopCat.of (ComplexPoint X)) hU ⊤ (ambientRationalInjectiveComplex X)).τ₁ n
        (rationalSupportAddEquivSupportedInjectiveHomology X S n a) := h1
  simp only [supportedSingularClass, AddEquiv.trans_apply]
  rw [h3]
  generalize rationalSupportAddEquivSupportedInjectiveHomology X S n a = y
  simp only [complexSupportInjectiveSectionCohomologyEquiv, AddEquiv.trans_apply]
  have key' : (complexSupportedSingularInjectiveHomologyIso X S.compl ⊤ n).inv ≫
      HomologicalComplex.homologyMap (supportRestrictionSectionsComplexSupportMap
        (TopCat.of (ComplexPoint X)) hU ⊤
        (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).τ₁ n =
      HomologicalComplex.homologyMap (supportRestrictionSectionsComplexSupportMap
        (TopCat.of (ComplexPoint X)) hU ⊤ (ambientRationalInjectiveComplex X)).τ₁ n ≫
      (complexSupportedSingularInjectiveHomologyIso X T.compl ⊤ n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact complexSupportedSingularInjectiveHomologyIso_support X hU ⊤ n
  have h2 := ConcreteCategory.congr_hom key' y
  simp only [ConcreteCategory.comp_apply] at h2
  erw [← h2]
  exact supportedRationalSingularSectionCohomologyEquivSupportComplement_support _ ⊤
    S.isClosed T.isClosed (SetLike.coe_subset_coe.mpr h) n _

/-- Forgetting the support factors through any larger support. -/
theorem forgetSupport_restrict {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (n : ℕ)
    (a : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n) :
    ComplexPoint.forgetSupport ℚ X S n a =
      ComplexPoint.forgetSupport ℚ X T n (supportEnlarge X h n a) := by
  simp only [ComplexPoint.forgetSupport, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  congr 1
  exact (relH_forget_restrict _ _ _ _ _ n a).symm

end ComplexPoint

end HodgeLean.RealDefs

end
