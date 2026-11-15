import HodgeLean.RealDefs.FundamentalClass.Constants
import HodgeLean.RealDefs.FundamentalClass.Chart
import HodgeLean.RealDefs.FundamentalClass.Point
import HodgeLean.RealDefs.FundamentalClass.Cone
import HodgeLean.RealDefs.FundamentalClass.Augmentation
import HodgeLean.RealDefs.FundamentalClass.SingularChase
import HodgeLean.RealDefs.FundamentalClass.ConstantSection

/-! # `[X] = 1` against upstream's definitions

Roadmap item U3, closed: `cycleComponentSheafClass_generic`. The proof follows the constant class
through every layer of upstream's normalization; `docs/notes/fundamental-class-unit.md` lists the
layers and the files under `FundamentalClass/` that prove them. -/

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry ComplexPoint
open AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance (V : Opens (ComplexPoint X)) : ParacompactSpace V := openParacompactSpace X V

/-- The claim that was left for `[X] = 1` after the first leg of `hlean-u3`, proved below as
`constantCochainNormalization`: upstream's identification of supported singular-section
cohomology with relative singular cohomology sends the class of the constant cochain to the
full-support coclass. Here `g` is the lift of the unit, and `c` any cycle whose underlying supported
section is `g ≫ ρ⁰`. -/
def ConstantCochainNormalization (Z : Closeds (ComplexPoint X)) (hZ : Z = ⊤) : Prop :=
  ∀ (g : TopCat.Sheaf.pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _) ⟶
      (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)),
    forgetSupport ℚ X Z 0 (Abelian.Ext.mk₀ g) = unitClass X →
    ∀ (c : (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
        ℤᵘᵖ).obj (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X))
          Z.compl)).cycles 0),
    (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
        ℤᵘᵖ).obj (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X))
          Z.compl)).iCycles 0 c =
      (TopCat.Sheaf.pairSheafHomIsoSupportedSections (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl
        (top_inf_eq _) ((rationalSingularCochainComplex (TopCat.of (ComplexPoint X))).X 0)).hom
        (g ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (rationalSingularAugmentation X).f 0) →
    supportedRationalSingularSectionCohomologyEquivSupportComplement
        (TopCat.of (ComplexPoint X)) Z Z.isClosed ⊤ 0
        ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
          ℤᵘᵖ).obj (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X))
            Z.compl)).homologyπ 0 c) =
      fullSupportCoclass 0 _ _ (by rw [hZ]; exact Set.subset_univ _)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
/-- `[X] = 1`, given the constant-cochain normalization. -/
theorem cycleComponentSheafClass_eq_unitClass_of_constantCochain (x : X.left)
    (hx : Order.coheight x = 0)
    (h : ConstantCochainNormalization X (cycleComponentAnalyticClosedSupport X x)
      (by obtain rfl := eq_genericPoint_of_coheight_zero x hx
          exact cycleComponentAnalyticClosedSupport_genericPoint X)) :
    cycleComponentSheafClass X x hx = unitClass X := by
  have hZ : cycleComponentAnalyticClosedSupport X x = ⊤ := by
    obtain rfl := eq_genericPoint_of_coheight_zero x hx
    exact cycleComponentAnalyticClosedSupport_genericPoint X
  obtain ⟨u, hu⟩ := forgetSupport_surjective_of_eq_top X _ hZ 0 (unitClass X)
  obtain ⟨g, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 u
  obtain ⟨c, hc⟩ := exists_supportedSections_cycle (TopCat.of (ComplexPoint X))
    (cycleComponentAnalyticClosedSupport X x).compl ⊤ _ (top_inf_eq _) _
    (rationalSingularAugmentation X) g
  apply cycleComponentSheafClass_eq_unitClass_of_normalization X x hx _ hu
  refine (cycleComponentSupportedClassNormalizationIso_eq_restrict X x hx _).trans ?_
  have h4 := complexSupportInjectiveSectionCohomologyEquiv_mk₀ X
    (cycleComponentAnalyticClosedSupport X x) g c hc
  have hN := h g hu c hc
  refine Eq.trans ?_ (cycleComponentSmoothSupportCoclassSection_eq_fullSupportCoclass X x hx).symm
  refine (congrArg (fun a => (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * 0)).obj.map
        (homOfLE (le_top : cycleComponentSmoothSupportAmbientOpen X x ≤ ⊤)).op
      ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * 0)).app (op ⊤) a)) (h4.trans hN)).trans ?_
  refine (supportRelativeCohomologyToSheaf_map_apply _ _ _ _).trans ?_
  exact congrArg _ (relativeCohomologyMap_fullSupportCoclass _ _ _ _ _ _)


set_option maxHeartbeats 1000000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constant-cochain normalization holds. -/
theorem constantCochainNormalization (Z : Closeds (ComplexPoint X)) (hZ : Z = ⊤) :
    ConstantCochainNormalization X Z hZ := by
  intro g hg c hc
  have hW : (⊤ : Opens (TopCat.of (ComplexPoint X))) ⊓ Z.compl = ⊥ := by
    subst hZ; ext; simp
  obtain ⟨cr, hcr⟩ := exists_relativeAugmentationCocycle (X := TopCat.of (ComplexPoint X)) ⊤
    (Opens.infLELeft ⊤ Z.compl) hW
  have h1 := supportedRationalSingularSectionCohomologyEquivRelative_homologyπ
    (TopCat.of (ComplexPoint X)) Z.compl ⊤ c
    (constantRawCochain (TopCat.of (ComplexPoint X)) ⊤)
    (constantRawCochain_d (TopCat.of (ComplexPoint X)) ⊤)
    (openCochains_eq_zero_of_eq_bot _ hW _)
    (constantRawCochain_sheafify_eq X Z g hg c hc) cr
    (hcr.trans (constantRawCochain_eq (TopCat.of (ComplexPoint X)) ⊤).symm)
  have := isIso_relativeChainProjection _
    (isEmpty_openInclusionPair_snd (X := TopCat.of (ComplexPoint X)) ⊤ (Opens.infLELeft ⊤ Z.compl) hW)
  have h2 := homologyπ_eq_augmentationClass _ cr hcr
  rw [fullSupportCoclass_zero_eq_augmentationClass]
  change relativeCohomologyMap ℚ 0
    (openIntersectionPairIsoSupportComplement (TopCat.of (ComplexPoint X)) Z Z.isClosed ⊤).inv
    (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl
      ⊤ 0 _) = _
  erw [h1, h2]
  have := isIso_relativeChainProjection_of_subset
    ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X)) (Z : Set (ComplexPoint X))
    (by rw [hZ]; exact Set.subset_univ _)
  have := isIso_relativeChainProjection _
    (isEmpty_openInclusionPair_snd (X := TopCat.of (ComplexPoint X)) ⊤
      (Opens.infLELeft ⊤ ⟨(Z : Set (ComplexPoint X))ᶜ, Z.isClosed.isOpen_compl⟩)
      (by subst hZ; ext; simp))
  exact relativeCohomologyMap_augmentationClass _

/-- `[X] = 1`: upstream's fundamental class of the generic point is the constant class `1` in
`H^0(X(ℂ); ℚ)`, against Paul-Lez's definitions, with no hypothesis beyond the section's
instances.

Checks: F-1683 -/
theorem cycleComponentSheafClass_generic (x : X.left) (hx : Order.coheight x = 0) :
    cycleComponentSheafClass X x hx = unitClass X :=
  cycleComponentSheafClass_eq_unitClass_of_constantCochain X x hx
    (constantCochainNormalization X _ _)

/-- The constant class `1 ∈ H^0(X(ℂ); ℚ)` is nonzero.

Checks: F-1683 -/
theorem unitClass_ne_zero' : unitClass X ≠ 0 := by
  rw [← cycleComponentSheafClass_generic X (genericPoint X.left) (coheight_genericPoint X.left)]
  exact cycleComponentSheafClass_genericPoint_ne_zero X _

end HodgeLean.RealDefs
