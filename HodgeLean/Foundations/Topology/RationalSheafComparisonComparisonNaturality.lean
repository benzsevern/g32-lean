import HodgeLean.Foundations.Topology.RationalSheafComparisonRegrade

/-! Naturality through the explicit regrading and forgetful identifications.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Topology.RationalSheafComparison

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def resolutionRegradeIso (X : TopCat.{0}) (n : ℕ) :
    (TopCat.Sheaf.globalSectionsComplexInt X (resolution X).cochainComplex).homology (n : ℤ) ≅
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
        (.up ℕ)).obj (resolution X).cocomplex).homology n :=
  HomologicalComplex.homologyMapIso (HomologicalComplex.mapExtendCanonicalIso
      (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X)
      (resolution X).cocomplex ComplexShape.embeddingUpNat) (n : ℤ) ≪≫
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
      (.up ℕ)).obj (resolution X).cocomplex).extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem resolutionRegradeIso_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap (globalResolutionPullback f) (n : ℤ) ≫
        (resolutionRegradeIso X n).hom =
      (resolutionRegradeIso Y n).hom ≫ HomologicalComplex.homologyMap (globalResolutionPullbackNat f) n := by
  dsimp only [resolutionRegradeIso, Iso.trans_hom, HomologicalComplex.homologyMapIso]
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    globalResolutionPullback_regrade, HomologicalComplex.homologyMap_comp, Category.assoc,
    HomologicalComplex.extendHomologyIso_hom_naturality]
  simp only [Category.assoc]

/-- Source: Bredon, Sheaf Theory, second edition, II.4 and III.1. -/
def comparisonNat (X : TopCat.{0})
    (hX : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U) (n : ℕ) :=
  (HomologicalComplex.homologyMap (comparisonComplex X hX) n).hom.comp
    (((SingularCochainComplex ℚ X).sc n).mapHomologyIso
      (forget₂ (ModuleCat ℚ) AddCommGrpCat)).inv.hom

/-- Source: Bredon, Sheaf Theory, second edition, II.4 and III.1. -/
theorem comparisonNat_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hX : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hY : ∀ (y : Y) (U : Opens Y), y ∈ U →
      ∃ V : Opens Y, y ∈ V ∧ ContractibleSpace V ∧ V ≤ U) (n : ℕ) (v : Cohomology ℚ Y n) :
    comparisonNat X hX n (cohomologyMap ℚ n f v) =
      HomologicalComplex.homologyMap (globalResolutionPullbackNat f) n (comparisonNat Y hY n v) := by
  have hf := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.up ℕ) n).map (singularCochainComplexMap ℚ f))
    (forget₂ (ModuleCat ℚ) AddCommGrpCat)
  have ht := congrArg (fun k => k ≫ HomologicalComplex.homologyMap (comparisonComplex X hX) n) hf
  simp only [Category.assoc] at ht
  change (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
      (HomologicalComplex.homologyMap (singularCochainComplexMap ℚ f) n) ≫
      (((SingularCochainComplex ℚ X).sc n).mapHomologyIso
        (forget₂ (ModuleCat ℚ) AddCommGrpCat)).inv ≫
      HomologicalComplex.homologyMap (comparisonComplex X hX) n =
    (((SingularCochainComplex ℚ Y).sc n).mapHomologyIso
        (forget₂ (ModuleCat ℚ) AddCommGrpCat)).inv ≫
      HomologicalComplex.homologyMap
        (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
          (singularCochainComplexMap ℚ f)) n ≫
      HomologicalComplex.homologyMap (comparisonComplex X hX) n at ht
  rw [← HomologicalComplex.homologyMap_comp, comparisonComplex_naturality_homology f hX hY n,
    HomologicalComplex.homologyMap_comp] at ht
  have h := ConcreteCategory.congr_hom ht v
  simp only [ConcreteCategory.comp_apply] at h
  dsimp only [comparisonNat, AddMonoidHom.comp_apply]
  convert h using 1 <;> rfl

/-- Source: Bredon, Sheaf Theory, second edition, II.4 and III.1. -/
theorem comparison_naturality_from_resolution {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hX : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hY : ∀ (y : Y) (U : Opens Y), y ∈ U →
      ∃ V : Opens Y, y ∈ V ∧ ContractibleSpace V ∧ V ≤ U) (n : ℕ) (v : Cohomology ℚ Y n) :
    comparison X hX n (cohomologyMap ℚ n f v) = sheafPullback f n (comparison Y hY n v) := by
  have hi (w) : (resolutionRegradeIso X n).inv
      (HomologicalComplex.homologyMap (globalResolutionPullbackNat f) n w) =
    HomologicalComplex.homologyMap (globalResolutionPullback f) (n : ℤ)
      ((resolutionRegradeIso Y n).inv w) := by
    let eX := (resolutionRegradeIso X n).addCommGroupIsoToAddEquiv
    let eY := (resolutionRegradeIso Y n).addCommGroupIsoToAddEquiv
    apply eX.injective
    change eX (eX.symm (HomologicalComplex.homologyMap (globalResolutionPullbackNat f) n w)) = _
    rw [AddEquiv.apply_symm_apply]
    have h := ConcreteCategory.congr_hom (resolutionRegradeIso_naturality f n)
      (eY.symm w)
    change eX (HomologicalComplex.homologyMap (globalResolutionPullback f) (n : ℤ) (eY.symm w)) =
      HomologicalComplex.homologyMap (globalResolutionPullbackNat f) n (eY (eY.symm w)) at h
    rw [AddEquiv.apply_symm_apply] at h
    exact h.symm
  change resolutionCohomologyEquiv X n ((resolutionRegradeIso X n).inv
      (comparisonNat X hX n (cohomologyMap ℚ n f v))) =
    sheafPullback f n (resolutionCohomologyEquiv Y n
      ((resolutionRegradeIso Y n).inv (comparisonNat Y hY n v)))
  rw [comparisonNat_naturality, hi, resolutionCohomologyEquiv_naturality]

end HodgeLean.Topology.RationalSheafComparison
