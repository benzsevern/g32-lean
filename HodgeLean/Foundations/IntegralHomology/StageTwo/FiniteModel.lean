import HodgeLean.Foundations.IntegralHomology.StageTwo.Defs
import HodgeLean.Foundations.IntegralHomology.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! Finite generation transported from an actual finite integral chain model.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

def FiniteChainModel.transport {X Y : TopCat.{0}} (M : FiniteChainModel X)
    (e : X ≅ Y) : FiniteChainModel Y where
  chains := M.chains
  rank := M.rank
  basis := M.basis
  dimension := M.dimension
  bounded := M.bounded
  comparison := M.comparison.trans (HomotopyEquiv.ofIso
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso e))

theorem FiniteChainModel.homology_finite {X : TopCat.{0}} (M : FiniteChainModel X)
    (n : ℕ) : Module.Finite ℤ ((ZChains X).homology n) := by
  letI : Module.Finite ℤ (M.chains.X n) := Module.Finite.of_basis (M.basis n)
  let S := M.chains.sc n
  letI : Module.Finite ℤ S.X₂ := by
    change Module.Finite ℤ (M.chains.X n)
    infer_instance
  letI : IsNoetherian ℤ S.X₂ := inferInstance
  letI : Module ℤ (LinearMap.ker S.g.hom) := (LinearMap.ker S.g.hom).module
  letI : Module.Finite ℤ (LinearMap.ker S.g.hom) :=
    Module.Finite.of_injective (LinearMap.ker S.g.hom).subtype Subtype.val_injective
  letI : Module.Finite ℤ S.moduleCatLeftHomologyData.H := by
    exact Module.Finite.of_surjective (LinearMap.range S.moduleCatToCycles).mkQ
      (Submodule.mkQ_surjective _)
  letI : Module.Finite ℤ S.homology :=
    Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm
  letI : Module.Finite ℤ (M.chains.homology n) := by
    change Module.Finite ℤ S.homology
    infer_instance
  exact Module.Finite.equiv (M.comparison.toHomologyIso n).toLinearEquiv

theorem FiniteChainModel.lattice_finiteFree {X : TopCat.{0}} (M : FiniteChainModel X) :
    Module.Finite ℤ (H1 X) ∧ Module.Finite ℤ (Lattice X) ∧ Module.Free ℤ (Lattice X) := by
  letI := M.homology_finite 1
  exact ⟨inferInstance, IntegralHomology.lattice_finiteFree X⟩
end HodgeLean.Foundations.IntegralHomology.StageTwo
