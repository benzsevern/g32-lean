import HodgeLean.Foundations.Program.SchoenSelectedGeometryCoefficientNaturality

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Rational coefficient extension commutes with singular homology pushforward. -/
theorem s0_qToCHomology_naturality {X Y : TopCat} (n : ℕ) (f : X ⟶ Y)
    (z : Homology ℚ X n) :
    qToCHomology Y n (homologyMap ℚ n f z) =
      homologyMap ℂ n f (qToCHomology X n z) := by
  let R := ModuleCat.restrictScalars (algebraMap ℚ ℂ)
  let F := R.mapHomologicalComplex (ComplexShape.down ℕ)
  have h := congrArg (fun g ↦ HomologicalComplex.homologyMap g n)
    (s0_qToCChainMap_naturality f)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  have hi : HomologicalComplex.homologyMap (F.map (singularChainComplexMap ℂ f)) n ≫
      (restrictedCChainsHomologyIso Y n).hom =
      (restrictedCChainsHomologyIso X n).hom ≫
        R.map (HomologicalComplex.homologyMap (singularChainComplexMap ℂ f) n) := by
    exact ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat ℂ) (ComplexShape.down ℕ) n).map
        (singularChainComplexMap ℂ f)) R
  have hh := congrArg (fun g ↦ g ≫ (restrictedCChainsHomologyIso Y n).hom) h
  rw [Category.assoc, Category.assoc, hi, ← Category.assoc] at hh
  exact congrArg (fun g ↦ g.hom z) hh

#print axioms s0_qToCHomology_naturality
end HodgeLean.Foundations.Program
