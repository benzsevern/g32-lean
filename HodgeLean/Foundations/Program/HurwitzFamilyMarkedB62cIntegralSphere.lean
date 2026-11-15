import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CoefficientExcision

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false in
def b6m_facetCarrierAffineIntegralHomotopy (d : ℕ) :
    Homotopy
      (standardFacetCarrierChainMap d ≫ standardAffineBoundaryIntegralChainMap d)
      (coverSmallIntegralSingularChainInclusion
        (puncturedPair ℝ d).snd (standardPuncturedFacetCover d)) := by
  have h : Homotopy
      ((standardFacetCarrierChainMap d ≫ standardAffineBoundaryIntegralChainMap d :
        CoverSmallIntegralSingularChainComplex
          (puncturedPair ℝ d).snd (standardPuncturedFacetCover d) ⟶
            IntegralSingularChainComplexObj (puncturedPair ℝ d).snd) -
        standardFacetSmallBarycentricLastVertexIntegralChainMap d ≫
          coverSmallIntegralSingularChainInclusion
            (puncturedPair ℝ d).snd (standardPuncturedFacetCover d)) 0 :=
    (Homotopy.ofEq (standardFacetCarrierDiscrepancyChainMap_eq d).symm).trans
      (standardFacetCarrierDiscrepancyIntegralHomotopy d)
  exact (Homotopy.equivSubZero.symm h).trans
    ((barycentricSubdivisionLastVertexHomotopyCanonical
      (coverSmallSingularSubcomplex
        (puncturedPair ℝ d).snd (standardPuncturedFacetCover d) : SSet)).compRightId _)

theorem b6m_affineBoundaryIntegral_factor (d : ℕ) :
    SSet.chainComplexMap (standardAffineBoundaryToFacetSmall d) (AddCommGrpCat.of ℤ) ≫
      coverSmallIntegralSingularChainInclusion
        (puncturedPair ℝ d).snd (standardPuncturedFacetCover d) =
      standardAffineBoundaryIntegralChainMap d := by
  change SSet.chainComplexMap (standardAffineBoundaryToFacetSmall d) (AddCommGrpCat.of ℤ) ≫
    SSet.chainComplexMap (coverSmallSingularSubcomplex
      (puncturedPair ℝ d).snd (standardPuncturedFacetCover d)).ι (AddCommGrpCat.of ℤ) =
    SSet.chainComplexMap (standardAffineBoundarySimplicialMap d) (AddCommGrpCat.of ℤ)
  rw [← Functor.map_comp, standardAffineBoundaryToFacetSmall_comp_inclusion]

set_option backward.isDefEq.respectTransparency false in
def b6m_affineBoundaryIntegralHomotopyEquiv (d : ℕ) :
    HomotopyEquiv
      ((∂Δ[d] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ))
      ((TopCat.toSSet.obj (puncturedPair ℝ d).snd).chainComplex (AddCommGrpCat.of ℤ)) := by
  let E := coverSmallChainHomotopyEquiv_of_openCover
    (puncturedPair ℝ d).snd (standardPuncturedFacetCover d)
    (isOpen_standardPuncturedFacetCover d) (iUnion_standardPuncturedFacetCover d)
  let A := standardAffineBoundaryIntegralChainMap d
  let C := standardFacetCarrierChainMap d
  let S := SSet.chainComplexMap (standardAffineBoundaryToFacetSmall d) (AddCommGrpCat.of ℤ)
  have hE : E.hom = coverSmallIntegralSingularChainInclusion
      (puncturedPair ℝ d).snd (standardPuncturedFacetCover d) :=
    coverSmallChainHomotopyEquiv_of_openCover_hom _ _ _ _
  have hfac : S ≫ E.hom = A := by
    rw [hE]
    exact b6m_affineBoundaryIntegral_factor d
  have hSC : Homotopy (S ≫ C) (𝟙 _) :=
    (Homotopy.ofEq (standardAffineSmall_comp_standardFacetCarrierChainMap d)).trans
      (barycentricSubdivisionLastVertexHomotopyCanonical (∂Δ[d] : SSet.{0}))
  have hCA : Homotopy (C ≫ A) E.hom :=
    (b6m_facetCarrierAffineIntegralHomotopy d).trans (Homotopy.ofEq hE.symm)
  refine ⟨A, E.inv ≫ C, ?_, ?_⟩
  · have heq : A ≫ (E.inv ≫ C) = (S ≫ (E.hom ≫ E.inv)) ≫ C := by
      rw [← hfac]
      simp only [Category.assoc]
    exact (Homotopy.ofEq heq).trans
      (((E.homotopyHomInvId.compLeft S).compRight C).trans
        ((Homotopy.ofEq (by simp only [Category.comp_id])).trans hSC))
  · exact (Homotopy.ofEq (Category.assoc E.inv C A)).trans
      ((hCA.compLeft E.inv).trans E.homotopyInvHomId)

def b6m_affineBoundaryCoefficientHomotopyEquiv (R : Type) [CommRing R] (d : ℕ) :
    HomotopyEquiv
      ((∂Δ[d] : SSet.{0}).chainComplex (ModuleCat.of R R))
      ((TopCat.toSSet.obj (puncturedPair ℝ d).snd).chainComplex (ModuleCat.of R R)) :=
  coefficientizeSimplicialChainHomotopyEquiv R (∂Δ[d] : SSet.{0})
    (TopCat.toSSet.obj (puncturedPair ℝ d).snd)
    (b6m_affineBoundaryIntegralHomotopyEquiv d)

theorem b6m_affineBoundaryCoefficientHomotopyEquiv_hom
    (R : Type) [CommRing R] (d : ℕ) :
    (b6m_affineBoundaryCoefficientHomotopyEquiv R d).hom =
      SSet.chainComplexMap (standardAffineBoundarySimplicialMap d) (ModuleCat.of R R) :=
  coefficientizeSimplicialChainMap_chainComplexMap R (standardAffineBoundarySimplicialMap d)

theorem b6m_punctured_homology_isZero_of_dimension_le
    (R : Type) [CommRing R] (d k : ℕ) (hk : d ≤ k) :
    CategoryTheory.Limits.IsZero (Homology R (puncturedPair ℝ d).snd k) := by
  exact ((∂Δ[d] : SSet.{0}).isZero_homology_of_hasDimensionLT
    (ModuleCat.of R R) k d hk).of_iso
      ((b6m_affineBoundaryCoefficientHomotopyEquiv R d).toHomologyIso k).symm

end HodgeLean.Foundations.Program
