import HodgeLean.Foundations.BundleThom.DirectedRelativeCoclassDetectionHelpers
import HodgeLean.Foundations.BundleThom.FullRelativeSmallChainHelpers
import HodgeLean.Foundations.BundleThom.ChainDualQuasiIsoHelpers

/-! # Directed actual singular-domain detection for topological relative coclasses

The full relative comparison transfers the directed-chain result to the supplied topological pair.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Simplicial
namespace HodgeLean.Foundations.BundleThom

/-- Directed actual singular domains covering n-simplices detect rational relative n-coclasses of the supplied topological pair.
Source: Hatcher, Algebraic Topology, §2.1 and §3.1, directed relative chain unions. -/
theorem i1_actualDirectedRelativeCoclass_ext {ι : Type} [Nonempty ι]
    (X : TopCat) (Z : Set X) (U : ι → (TopCat.toSSet.obj X).Subcomplex)
    (hdir : Directed (· ≤ ·) U) (n : ℕ)
    (hcover : ∀ σ : (TopCat.toSSet.obj X) _⦋n⦌,
      ∃ i, σ ∈ (U i).obj (Opposite.op ⦋n⦌))
    (u v : RelativeCohomology ℚ (TopPair.ofSubset (X := X) Z) n)
    (h : ∀ i, i1_chainDualPullback n (i1_relativeSmallChainComparison X Z (U i)) u =
      i1_chainDualPullback n (i1_relativeSmallChainComparison X Z (U i)) v) : u = v := by
  letI := i1_fullRelativeSmallChainComparison_quasiIso X Z
  apply (i1_chainDualPullback_bijective n (i1_relativeSmallChainComparison X Z ⊤)).1
  apply i1_directedRelativeCoclass_ext (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)
    U hdir n hcover
  intro i
  rw [← LinearMap.comp_apply, ← i1_chainDualPullback_comp,
    i1_relativeSmallChainComparison_naturality,
    ← LinearMap.comp_apply, ← i1_chainDualPullback_comp,
    i1_relativeSmallChainComparison_naturality]
  exact h i

end HodgeLean.Foundations.BundleThom
