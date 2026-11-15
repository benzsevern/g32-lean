import HodgeLean.Foundations.IntegralHomology.StageTwo.Retractions
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! Freeness in degree zero for actual integral singular chains.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

theorem integralHomologyZero_free (X : TopCat.{0}) :
    Module.Free ℤ ((ZChains X).homology 0) := by
  let e := TopCat.singularHomology₀Iso X (ModuleCat.of ℤ ℤ) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (ZerothHomotopy X))
  letI : Module.Free ℤ (ModuleCat.finsuppCocone ℤ ℤ (ZerothHomotopy X)).pt :=
    Module.Free.of_basis (Finsupp.basisSingleOne)
  exact Module.Free.of_equiv e.toLinearEquiv.symm

theorem integralBoundaryQuotient_free (X : TopCat.{0}) :
    Module.Free ℤ ((ZChains X).X 0 ⧸ LinearMap.range ((ZChains X).d 1 0).hom) := by
  letI : Module ℤ ((ZChains X).X 0 ⧸ LinearMap.range ((ZChains X).d 1 0).hom) :=
    Submodule.Quotient.module _
  letI := integralHomologyZero_free X
  let e := (ZChains X).isoHomologyι₀ ≪≫
    ShortComplex.opcyclesMapIso ((ZChains X).isoSc' 1 0 0 (by simp) (by simp)) ≪≫
    ((ZChains X).sc' 1 0 0).moduleCatOpcyclesIso
  have hmod : Submodule.Quotient.module (LinearMap.range ((ZChains X).d 1 0).hom) =
      AddCommGroup.toIntModule ((ZChains X).X 0 ⧸ LinearMap.range ((ZChains X).d 1 0).hom) :=
    Subsingleton.elim _ _
  rw [← hmod]
  exact Module.Free.of_equiv e.toLinearEquiv
end HodgeLean.Foundations.IntegralHomology.StageTwo
