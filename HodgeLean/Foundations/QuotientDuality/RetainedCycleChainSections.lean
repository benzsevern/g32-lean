import HodgeLean.Foundations.QuotientDuality.RetainedCycleCapCupHomology
import HodgeLean.RealDefs.Port.AlgebraicTopology.Sheaf.HomologySection

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology AlgebraicTopology.Singular
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Sections on the specified open set of the actual chain-sheaf complex. -/
def retainedChainSheafSectionComplex (X : TopCat.{0}) (U : Opens X) :
    ChainComplex AddCommGrpCat ℕ :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op U)).mapHomologicalComplex (.down ℕ)).obj
    (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex (.down ℕ)).obj
      (singularChainSheafComplex ℚ X))

/-- Actual relative chains give sections through evaluation and the chain-sheafification unit. -/
def retainedRelativeChainSheafSectionMap (X : TopCat.{0}) (U : Opens X) :
    ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.down ℕ)).obj
      ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (U : Set X)ᶜ)) ⟶
        retainedChainSheafSectionComplex X U :=
  (singularChainPresheafComplexEvaluationIso ℚ X U).inv ≫
    (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op U)).mapHomologicalComplex (.down ℕ)).map
      (singularChainSheafificationUnit ℚ X)

/-- The relative section comparison retains the exact degreewise sheafification map. -/
theorem retained_relative_chain_sheaf_section_component (X : TopCat.{0}) (U : Opens X) (n : ℕ) :
    (retainedRelativeChainSheafSectionMap X U).f n =
      (toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf ℚ X n)).app (op U) := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- Actual absolute singular chains give sections by relative projection followed by sheafification. -/
def retainedChainSheafSectionMap (X : TopCat.{0}) (U : Opens X) :
    ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.down ℕ)).obj
      (SingularChainComplex ℚ X) ⟶ retainedChainSheafSectionComplex X U :=
  ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.down ℕ)).map
      (relativeChainProjection ℚ (TopPair.ofSubset (U : Set X)ᶜ)) ≫
    retainedRelativeChainSheafSectionMap X U

/-- Every absolute comparison component is the literal relative projection and sheafification map. -/
theorem retained_chain_sheaf_section_component (X : TopCat.{0}) (U : Opens X) (n : ℕ) :
    (retainedChainSheafSectionMap X U).f n =
      (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
        ((relativeChainProjection ℚ (TopPair.ofSubset (U : Set X)ᶜ)).f n) ≫
      (toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf ℚ X n)).app (op U) := by
  rw [retainedChainSheafSectionMap, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, retained_relative_chain_sheaf_section_component]

/-- The relative-chain section comparison intertwines the actual relative and sheaf cap operations. -/
theorem retained_relative_chain_sheaf_section_cap (X : TopCat.{0}) (U : Opens X) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p) :
    (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
        (retainedRelativeAmbientCapHom (TopPair.ofSubset (U : Set X)ᶜ) p q φ) ≫
        (retainedRelativeChainSheafSectionMap X U).f q =
      (retainedRelativeChainSheafSectionMap X U).f (p + q) ≫
        (retainedChainSheafAmbientCap X p q φ).hom.app (op U) := by
  rw [retained_relative_chain_sheaf_section_component, retained_relative_chain_sheaf_section_component]
  have h := congrArg (fun f => f.app (op U)) (retained_chain_sheaf_ambient_cap_unit X p q φ)
  simp only [NatTrans.comp_app, retainedChainPresheafAmbientCap] at h
  exact h.symm

/-- The actual absolute-chain comparison intertwines singular cap and cap on sheaf sections. -/
theorem retained_chain_sheaf_section_cap (X : TopCat.{0}) (U : Opens X) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p) :
    (forget₂ (ModuleCat ℚ) AddCommGrpCat).map (Simplicial.capHom ℚ p q φ) ≫
        (retainedChainSheafSectionMap X U).f q =
      (retainedChainSheafSectionMap X U).f (p + q) ≫
        (retainedChainSheafAmbientCap X p q φ).hom.app (op U) := by
  let J := forget₂ (ModuleCat ℚ) AddCommGrpCat
  have h := retained_relative_chain_sheaf_section_cap X U p q φ
  simp only [retainedChainSheafSectionMap, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f]
  simp only [← Category.assoc]
  rw [← J.map_comp]
  erw [← retained_relative_projection_ambient_cap (TopPair.ofSubset (U : Set X)ᶜ) p q φ]
  rw [J.map_comp]
  dsimp only [J]
  simp only [Category.assoc]
  rw [h]

/-- The canonical map from actual singular homology to homology of actual chain-sheaf sections. -/
def retainedChainSheafSectionHomologyMap (X : TopCat.{0}) (U : Opens X) (n : ℕ) :
    (forget₂ (ModuleCat ℚ) AddCommGrpCat).obj (Homology ℚ X n) ⟶
      (retainedChainSheafSectionComplex X U).homology n :=
  (((SingularChainComplex ℚ X).sc n).mapHomologyIso (forget₂ (ModuleCat ℚ) AddCommGrpCat)).inv ≫
    HomologicalComplex.homologyMap (retainedChainSheafSectionMap X U) n

/-- The section-homology comparison is induced by the actual comparison map on cycles. -/
theorem retained_chain_sheaf_section_homology_cycles (X : TopCat.{0}) (U : Opens X) (n : ℕ) :
    let J := forget₂ (ModuleCat ℚ) AddCommGrpCat
    let K := (J.mapHomologicalComplex (.down ℕ)).obj (SingularChainComplex ℚ X)
    K.homologyπ n ≫ (((SingularChainComplex ℚ X).sc n).mapHomologyIso J).hom ≫
        retainedChainSheafSectionHomologyMap X U n =
      HomologicalComplex.cyclesMap (retainedChainSheafSectionMap X U) n ≫
        (retainedChainSheafSectionComplex X U).homologyπ n := by
  dsimp only
  unfold retainedChainSheafSectionHomologyMap
  rw [Iso.hom_inv_id_assoc]
  exact HomologicalComplex.homologyπ_naturality (retainedChainSheafSectionMap X U) n

end HodgeLean.Foundations.QuotientDuality
