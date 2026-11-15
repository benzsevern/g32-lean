import HodgeLean.Foundations.IntegralHomology.StageTwo.FiniteModel
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
open scoped TensorProduct
open HodgeLean.Foundations.IntegralHomology
open HodgeLean.Foundations.IntegralHomology.StageTwo
namespace HodgeLean.Foundations.QuotientDuality

/-- A finite integral chain model gives finite rational singular cohomology in every degree.
Source: Hatcher, Algebraic Topology, §2.2 and Theorem 3.2. -/
theorem finiteModel_rational_cohomology (X : TopCat.{0}) (M : FiniteChainModel X) (n : ℕ) :
    FiniteDimensional ℚ (Cohomology ℚ X n) := by
  let F : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ := ModuleCat.extendScalars (Int.castRingHom ℚ)
  letI : F.Additive := {
    map_add := by
      intro A B f g
      apply ModuleCat.hom_ext
      apply TensorProduct.AlgebraTensorModule.ext
      intro s m
      exact TensorProduct.tmul_add s (f.hom m) (g.hom m) }
  let L := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj M.chains
  let e₀ : F.obj (ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℚ ℚ :=
    (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toModuleIso
  let e : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (ZChains X) ≅
      SingularChainComplex ℚ X :=
    (SSet.chainComplexFunctorObjCompMapIso.{0} F (ModuleCat.of ℤ ℤ)).app
      (TopCat.toSSet.obj X) ≪≫
    ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} ℚ)).mapIso e₀).app (TopCat.toSSet.obj X)
  let E : HomotopyEquiv L (SingularChainComplex ℚ X) := (F.mapHomotopyEquiv M.comparison).trans (HomotopyEquiv.ofIso e)
  letI : Module.Finite ℤ (M.chains.X n) := Module.Finite.of_basis (M.basis n)
  letI : Module.Finite ℚ (L.X n) := by
    change Module.Finite ℚ (ℚ ⊗[ℤ] (M.chains.X n))
    infer_instance
  let S := L.sc n
  letI : Module.Finite ℚ S.X₂ := inferInstanceAs (Module.Finite ℚ (L.X n))
  letI : Module.Finite ℚ (LinearMap.ker S.g.hom) :=
    Module.Finite.of_injective (LinearMap.ker S.g.hom).subtype Subtype.val_injective
  letI : Module.Finite ℚ S.moduleCatLeftHomologyData.H :=
    Module.Finite.of_surjective (LinearMap.range S.moduleCatToCycles).mkQ
      (Submodule.mkQ_surjective _)
  letI : Module.Finite ℚ S.homology :=
    Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm
  letI : Module.Finite ℚ (L.homology n) := inferInstanceAs (Module.Finite ℚ S.homology)
  letI : Module.Finite ℚ (Homology ℚ X n) :=
    Module.Finite.equiv (E.toHomologyIso n).toLinearEquiv
  exact Module.Finite.equiv (cohomologyEquivDualHomology ℚ X n).symm

end HodgeLean.Foundations.QuotientDuality
