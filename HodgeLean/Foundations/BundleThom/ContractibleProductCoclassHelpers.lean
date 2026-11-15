import HodgeLean.Foundations.BundleThom.ContractibleBaseHelpers
import HodgeLean.Foundations.BundleThom.ProductRelativeHomotopyHelpers
import HodgeLean.Foundations.BundleThom.ChainDualQuasiIsoHelpers

/-! # Actual fibre detection over contractible topological bases

The coclass equivalence is restriction to the supplied actual fibre, in every degree.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Relative homology of a product over a contractible base vanishes off twice the complex rank.
Source: Hatcher, Algebraic Topology, §2.1 and §2.2, relative homotopy and Euclidean local homology. -/
theorem i1_contractibleProductNormalRelativeHomology_isZero {B : Type} [TopologicalSpace B]
    [ContractibleSpace B] (k n : ℕ) (hn : n ≠ 2 * k) :
    IsZero (RelativeHomology ℚ (i1_productNormalPair B k) n) := by
  let b : B := Classical.choice inferInstance
  exact i1_productNormalRelativeHomology_isZero_of_contraction k b
    (i1_contractibleBaseContraction b) n hn

/-- Actual restriction to any specified fibre is a coclass equivalence over a contractible base.
Source: Hatcher, Algebraic Topology, §3.1, homotopy invariance and universal coefficients. -/
def i1_contractibleProductFibreCoclassEquiv {B : Type} [TopologicalSpace B] [ContractibleSpace B]
    (k : ℕ) (b : B) (n : ℕ) :
    RelativeCohomology ℚ (i1_productNormalPair B k) n ≃ₗ[ℚ]
      RelativeCohomology ℚ (puncturedPair ℂ k) n := by
  let e := i1_productNormalRelativeChainHomotopyEquiv k b (i1_contractibleBaseContraction b)
  haveI : QuasiIso e.inv := inferInstance
  exact i1_chainDualPullbackEquiv n e.inv

/-- The actual fibre coclass equivalence is the supplied fibre-section pullback.
Source: Hatcher, Algebraic Topology, §3.1, relative restriction. -/
theorem i1_contractibleProductFibreCoclassEquiv_apply {B : Type} [TopologicalSpace B]
    [ContractibleSpace B] (k : ℕ) (b : B) (n : ℕ)
    (u : RelativeCohomology ℚ (i1_productNormalPair B k) n) :
    i1_contractibleProductFibreCoclassEquiv k b n u =
      relativeCohomologyMap ℚ n (i1_productNormalSection k b) u := rfl

/-- Fibre restriction detects actual product coclasses over a contractible base.
Source: Hatcher, Algebraic Topology, §3.1, homotopy invariance. -/
theorem i1_contractibleProductCoclass_ext {B : Type} [TopologicalSpace B] [ContractibleSpace B]
    (k : ℕ) (b : B) (n : ℕ) (u v : RelativeCohomology ℚ (i1_productNormalPair B k) n)
    (h : relativeCohomologyMap ℚ n (i1_productNormalSection k b) u =
      relativeCohomologyMap ℚ n (i1_productNormalSection k b) v) : u = v :=
  (i1_contractibleProductFibreCoclassEquiv k b n).injective h

end HodgeLean.Foundations.BundleThom
