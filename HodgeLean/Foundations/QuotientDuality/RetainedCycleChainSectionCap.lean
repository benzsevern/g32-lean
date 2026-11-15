import HodgeLean.Foundations.QuotientDuality.RetainedCycleChainSections

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology AlgebraicTopology.Singular
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual chain section comparison intertwines induced cap maps on homology. -/
theorem retained_chain_sheaf_section_cap_homology_square
    (X : TopCat.{0}) (U : Opens X) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    let J := forget₂ (ModuleCat ℚ) AddCommGrpCat
    let ρ := retainedChainSheafSectionMap X U
    let ρN := (HomologicalComplex.shortComplexFunctor AddCommGrpCat (.down ℕ) (p + q)).map ρ
    let ρQ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat (.down ℕ) q).map ρ
    ShortComplex.homologyMap
      (J.mapShortComplex.map (Simplicial.capShortComplexHom ℚ p q φ hφ) ≫ ρQ) =
    ShortComplex.homologyMap
      (ρN ≫ ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op U)).mapShortComplex.map
        ((TopCat.Sheaf.forget AddCommGrpCat.{0} X).mapShortComplex.map
          (retainedChainSheafCapShortComplex X p q φ hφ))) := by
  dsimp only
  apply retained_homology_map_eq_of_middle
  change (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
      (Simplicial.capShortComplexHom ℚ p q φ hφ).τ₂ ≫ (retainedChainSheafSectionMap X U).f q =
    (retainedChainSheafSectionMap X U).f (p + q) ≫
      (retainedChainSheafCapShortComplex X p q φ hφ).τ₂.hom.app (op U)
  rw [Simplicial.capShortComplexHom_τ₂, retained_chain_sheaf_cap_short_complex_middle]
  exact retained_chain_sheaf_section_cap X U p q φ

/-- The normalized actual singular-homology section comparison intertwines the actual cap maps. -/
theorem retained_chain_sheaf_section_homology_cap
    (X : TopCat.{0}) (U : Opens X) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
        (ModuleCat.ofHom (Simplicial.capHomologyMap ℚ p q φ hφ)) ≫
        retainedChainSheafSectionHomologyMap X U q =
      retainedChainSheafSectionHomologyMap X U (p + q) ≫
        ShortComplex.homologyMap
          (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op U)).mapShortComplex.map
            ((TopCat.Sheaf.forget AddCommGrpCat.{0} X).mapShortComplex.map
              (retainedChainSheafCapShortComplex X p q φ hφ))) := by
  let J := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let A := Simplicial.capShortComplexHom ℚ p q φ hφ
  let SN := (SingularChainComplex ℚ X).sc (p + q)
  let SQ := (SingularChainComplex ℚ X).sc q
  let ρ := retainedChainSheafSectionMap X U
  let ρN := (HomologicalComplex.shortComplexFunctor AddCommGrpCat (.down ℕ) (p + q)).map ρ
  let ρQ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat (.down ℕ) q).map ρ
  have hh := retained_chain_sheaf_section_cap_homology_square X U p q φ hφ
  dsimp only at hh
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at hh
  unfold retainedChainSheafSectionHomologyMap
  change J.map (ShortComplex.homologyMap A) ≫ (SQ.mapHomologyIso J).inv ≫
      ShortComplex.homologyMap ρQ =
    (SN.mapHomologyIso J).inv ≫ ShortComplex.homologyMap ρN ≫ _
  erw [ShortComplex.mapHomologyIso_inv_naturality_assoc]
  rw [hh]
  rfl

end HodgeLean.Foundations.QuotientDuality
