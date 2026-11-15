import HodgeLean.Foundations.Program.SchoenSelectedGeometryRationalInjection

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Rational coefficient extension commutes with singular chain pushforward. -/
theorem s0_qToCChainMap_naturality {X Y : TopCat} (f : X ⟶ Y) :
    singularChainComplexMap ℚ f ≫ qToCChainMap Y =
      qToCChainMap X ≫
        ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (singularChainComplexMap ℂ f) := by
  ext n : 1
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X)
  intro x
  ext
  change qToCChainGroup Y n
      (((SSet.ιChainComplex (C := ModuleCat ℚ) (R := ModuleCat.of ℚ ℚ)
        (TopCat.toSSet.obj X) x) ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f n).hom 1) =
    ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℂ ℂ)).f n).hom
      (qToCChainGroup X n ((SSet.ιChainComplex (C := ModuleCat ℚ)
        (R := ModuleCat.of ℚ ℚ) (TopCat.toSSet.obj X) x).hom 1))
  rw [SSet.ι_chainComplexMap_f, qToCChainGroup_iota, qToCChainGroup_iota]
  change _ = ((SSet.ιChainComplex (C := ModuleCat ℂ) (R := ModuleCat.of ℂ ℂ)
    (TopCat.toSSet.obj X) x) ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℂ ℂ)).f n).hom _
  rw [SSet.ι_chainComplexMap_f]

#print axioms s0_qToCChainMap_naturality
end HodgeLean.Foundations.Program
