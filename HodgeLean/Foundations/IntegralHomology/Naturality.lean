import HodgeLean.Foundations.IntegralHomology.CoefficientConstruction

/-! Naturality of singular coefficient extension.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.IntegralHomology

lemma coefficient_chain_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (cX : ZChains X ⟶ RestrictedQChains X)
    (cY : ZChains Y ⟶ RestrictedQChains Y)
    (hcX : ∀ n z, (cX.f n).hom z = coefficient X n z)
    (hcY : ∀ n z, (cY.f n).hom z = coefficient Y n z) :
    SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ) ≫ cY =
      cX ≫ ((ModuleCat.restrictScalars (algebraMap ℤ ℚ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map
          (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply SSet.chainComplex_hom_ext
  intro x
  ext
  let z : ℤ := 1
  change (cY.f n).hom
      (((SSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) (TopCat.toSSet.obj X) x) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f n).hom z) =
    ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f n).hom
      ((cX.f n).hom ((SSet.ιChainComplex (R := ModuleCat.of ℤ ℤ)
        (TopCat.toSSet.obj X) x).hom z))
  rw [SSet.ι_chainComplexMap_f, hcY, hcX]
  change rational_zToQChainGroup Y n _ = _
  rw [rational_zToQChainGroup_iota]
  change _ = ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f n).hom
    (rational_zToQChainGroup X n _)
  rw [rational_zToQChainGroup_iota]
  exact (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (SSet.ι_chainComplexMap_f (C := ModuleCat ℚ)
      (X := TopCat.toSSet.obj X) (Y := TopCat.toSSet.obj Y)
      (f := TopCat.toSSet.map f) (R := ModuleCat.of ℚ ℚ) x))
    (algebraMap ℤ ℚ z)).symm

set_option backward.defeqAttrib.useBackward true in
lemma restricted_homology_naturality {X Y : TopCat.{0}}
    (q : QChains X ⟶ QChains Y) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((ModuleCat.restrictScalars (algebraMap ℤ ℚ)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map q) n ≫
      (rational_restrictedQChainsModelHomologyIso Y n).hom =
    (rational_restrictedQChainsModelHomologyIso X n).hom ≫
      (ModuleCat.restrictScalars (algebraMap ℤ ℚ)).map
        (HomologicalComplex.homologyMap q n) := by
  have h := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map q)
    (ModuleCat.restrictScalars (algebraMap ℤ ℚ))
  exact h

end HodgeLean.Foundations.IntegralHomology
