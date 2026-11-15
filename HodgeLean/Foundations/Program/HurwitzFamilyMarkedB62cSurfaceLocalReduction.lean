import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLocalClassReduction
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceOrientation

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular

def b6m_surfaceLocalPairMap {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    (x : C) : puncturedPair ℝ 2 ⟶ pointComplementPair x :=
  (standardComplexRealPairIso 1).inv ≫ chartModelEmbeddingPair 1 (b6m_surfaceChart x) x
    (by simpa only [b6m_surfaceChart_source] using mem_chart_source ℂ x)

set_option backward.isDefEq.respectTransparency false in
theorem b6m_surfaceLocalClass_eq_image (R : Type) [CommRing R]
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] (x : C) :
    b6m_surfaceLocalClass R x = relativeHomologyMap R 2 (b6m_surfaceLocalPairMap x)
      (standardLocalClass R 2) := by
  unfold b6m_surfaceLocalClass b6m_localClassOfChart standardComplexLocalClass
  change relativeHomologyMap R 2 _
    (relativeHomologyMap R 2 (standardComplexRealPairIso 1).inv (standardLocalClass R 2)) = _
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem b6m_surfaceLocalClass_reduction
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] (n : ℕ)
    (c : (SingularChainComplex ℤ (TopCat.of C)).cycles 2)
    (d : (SingularChainComplex (ZMod n) (TopCat.of C)).cycles 2)
    (hrep : ((SingularChainComplex (ZMod n) (TopCat.of C)).iCycles 2).hom d =
      b6m_singularReduction (TopCat.of C) n 2
        (((SingularChainComplex ℤ (TopCat.of C)).iCycles 2).hom c))
    (hclass : ∀ x : C, (relativeHomologyProjection ℤ (pointComplementPair x) 2).hom
      (((SingularChainComplex ℤ (TopCat.of C)).homologyπ 2).hom c) =
        b6m_surfaceLocalClass ℤ x) :
    ∀ x : C, (relativeHomologyProjection (ZMod n) (pointComplementPair x) 2).hom
      (((SingularChainComplex (ZMod n) (TopCat.of C)).homologyπ 2).hom d) =
        b6m_surfaceLocalClass (ZMod n) x := by
  intro x
  exact (b6m_localImageClass_reduction (pointComplementPair x) (b6m_surfaceLocalPairMap x)
    n c d hrep ((hclass x).trans (b6m_surfaceLocalClass_eq_image ℤ x))).trans
      (b6m_surfaceLocalClass_eq_image (ZMod n) x).symm

end HodgeLean.Foundations.Program
