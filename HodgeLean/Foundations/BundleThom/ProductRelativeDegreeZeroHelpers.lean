import HodgeLean.Foundations.BundleThom.ProductComplementHomologyHelpers
import HodgeLean.Foundations.BundleThom.ChainCokernelHomologyZeroHelpers

/-! # Actual product relative degree-zero vanishing over arbitrary bases

A supplied nonzero vector splits complement inclusion on homology without any condition on the base.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- The actual product relative degree-zero homology vanishes over every base when the normal fibre has a specified nonzero vector.
Source: Hatcher, Algebraic Topology, §2.1, degree-zero relative homology and complement inclusion. -/
theorem i1_productNormalRelativeHomologyZero_isZero {B : Type} [TopologicalSpace B]
    (k : ℕ) (w : Fin k → ℂ) (hw : w ≠ 0) :
    IsZero (RelativeHomology ℚ (i1_productNormalPair B k) 0) := by
  haveI := i1_productComplementHomology_epi (B := B) k w hw 0
  change IsZero ((cokernel ((chainPairFunctor ℚ).obj (i1_productNormalPair B k)).hom).homology 0)
  exact i1_chainCokernelHomologyZero_isZero _

/-- Every positive complex rank has zero actual product relative degree-zero homology over an arbitrary topological base.
Source: Hatcher, Algebraic Topology, §2.1, degree-zero relative product homology. -/
theorem i1_productNormalRelativeHomologyZero_isZero_of_pos {B : Type} [TopologicalSpace B]
    (k : ℕ) (hk : 0 < k) : IsZero (RelativeHomology ℚ (i1_productNormalPair B k) 0) := by
  apply i1_productNormalRelativeHomologyZero_isZero k (fun _ => 1)
  intro h
  exact one_ne_zero (congrFun h ⟨0, hk⟩)

end HodgeLean.Foundations.BundleThom
