import HodgeLean.Foundations.QuotientDuality.RetainedCycleChainSectionCap
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
open scoped Simplicial
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- A finite coefficient family gives its actual simplicial chain. -/
def retainedChainFromCoordinates (X : SSet.{0}) (n : ℕ) :
    (X _⦋n⦌ →₀ ℚ) →ₗ[ℚ] Simplicial.ChainGroup ℚ X n :=
  Finsupp.linearCombination ℚ (fun σ => Simplicial.chainOfSimplex ℚ σ)

/-- The universal coproduct map records the actual finite simplex coefficients of a chain. -/
def retainedChainCoordinates (X : SSet.{0}) (n : ℕ) :
    Simplicial.ChainGroup ℚ X n →ₗ[ℚ] (X _⦋n⦌ →₀ ℚ) :=
  ((X.isColimitChainComplexXCofan (ModuleCat.of ℚ ℚ) n).desc
    (Cofan.mk (ModuleCat.of ℚ (X _⦋n⦌ →₀ ℚ))
      (fun σ => ModuleCat.ofHom (Finsupp.lsingle σ)))).hom

/-- The coordinate family of an actual simplex chain is its literal singleton coefficient family. -/
theorem retained_chain_coordinates_simplex (X : SSet.{0}) (n : ℕ) (σ : X _⦋n⦌) :
    retainedChainCoordinates X n (Simplicial.chainOfSimplex ℚ σ) = Finsupp.single σ 1 := by
  have h := (X.isColimitChainComplexXCofan (ModuleCat.of ℚ ℚ) n).fac
    (Cofan.mk (ModuleCat.of ℚ (X _⦋n⦌ →₀ ℚ))
      (fun τ => ModuleCat.ofHom (Finsupp.lsingle τ))) (Discrete.mk σ)
  have hv := ConcreteCategory.congr_hom h (1 : ℚ)
  change retainedChainCoordinates X n (Simplicial.chainOfSimplex ℚ σ) = Finsupp.single σ 1 at hv
  exact hv

/-- Reconstruction from actual simplex coordinates is the identity on chains. -/
theorem retained_chain_from_coordinates_comp_coordinates (X : SSet.{0}) (n : ℕ) :
    (retainedChainFromCoordinates X n).comp (retainedChainCoordinates X n) = LinearMap.id := by
  have h : ModuleCat.ofHom ((retainedChainFromCoordinates X n).comp (retainedChainCoordinates X n)) =
      𝟙 (Simplicial.ChainGroup ℚ X n) := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change retainedChainFromCoordinates X n
      (retainedChainCoordinates X n (Simplicial.chainOfSimplex ℚ σ)) = Simplicial.chainOfSimplex ℚ σ
    rw [retained_chain_coordinates_simplex]
    simp only [retainedChainFromCoordinates, Finsupp.linearCombination_single, one_smul]
  exact congrArg ModuleCat.Hom.hom h

/-- Taking coordinates of a reconstructed finite chain recovers its literal coefficients. -/
theorem retained_chain_coordinates_comp_from_coordinates (X : SSet.{0}) (n : ℕ) :
    (retainedChainCoordinates X n).comp (retainedChainFromCoordinates X n) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply, retainedChainFromCoordinates, Finsupp.linearCombination_single,
    map_smul, retained_chain_coordinates_simplex, LinearMap.id_apply, Finsupp.smul_single,
    smul_eq_mul, mul_one]

/-- Actual simplicial chains are canonically equivalent to finite simplex coefficient families. -/
def retainedChainCoordinateEquiv (X : SSet.{0}) (n : ℕ) :
    Simplicial.ChainGroup ℚ X n ≃ₗ[ℚ] (X _⦋n⦌ →₀ ℚ) where
  toLinearMap := retainedChainCoordinates X n
  invFun := retainedChainFromCoordinates X n
  left_inv c := LinearMap.congr_fun (retained_chain_from_coordinates_comp_coordinates X n) c
  right_inv a := LinearMap.congr_fun (retained_chain_coordinates_comp_from_coordinates X n) a

/-- The actual cochain extracting the coefficient of one specified simplex. -/
def retainedSimplexCoordinate (X : SSet.{0}) (n : ℕ) (σ : X _⦋n⦌) :
    Simplicial.Cochain ℚ X n :=
  (Finsupp.lapply σ).comp (retainedChainCoordinates X n)

/-- A simplex coordinate evaluates on a simplex chain by its literal singleton coefficient. -/
theorem retained_simplex_coordinate_simplex (X : SSet.{0}) (n : ℕ) (σ τ : X _⦋n⦌) :
    retainedSimplexCoordinate X n σ (Simplicial.chainOfSimplex ℚ τ) = (Finsupp.single τ 1) σ := by
  rw [retainedSimplexCoordinate, LinearMap.comp_apply, retained_chain_coordinates_simplex]
  rfl

end HodgeLean.Foundations.QuotientDuality
