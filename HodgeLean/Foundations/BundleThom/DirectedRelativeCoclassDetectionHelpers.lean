import HodgeLean.Foundations.BundleThom.DirectedRelativeChainCoverHelpers
import HodgeLean.Foundations.BundleThom.ChainCoverCoclassDetectionHelpers

/-! # Rational coclass detection in actual directed relative chain unions

The directed covering condition is imposed on actual simplices in the degree under consideration.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology Simplicial
namespace HodgeLean.Foundations.BundleThom

/-- Restrictions to a directed family covering all n-simplices detect rational relative n-coclasses on the ambient singular complex.
Source: Hatcher, Algebraic Topology, §2.1 and §3.1, directed chain unions and universal coefficients. -/
theorem i1_directedRelativeCoclass_ext {ι : Type} [Nonempty ι]
    (X : SSet) (Z : X.Subcomplex) (U : ι → X.Subcomplex) (hdir : Directed (· ≤ ·) U)
    (n : ℕ) (hcover : ∀ σ : X _⦋n⦌, ∃ i, σ ∈ (U i).obj (Opposite.op ⦋n⦌))
    (u v : ((i1_relativeSubcomplexChainFunctor X Z).obj ⊤).linearDualCochainComplex.homology n)
    (h : ∀ i, i1_chainDualPullback n
      ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE (le_top : U i ≤ ⊤))) u =
      i1_chainDualPullback n
      ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE (le_top : U i ≤ ⊤))) v) :
    u = v := by
  let F := i1_relativeSubcomplexChainFunctor X Z
  let p : ∀ i, F.obj (U i) ⟶ F.obj ⊤ := fun i => F.map (homOfLE le_top)
  haveI : ∀ i j, Mono ((p i).f j) := by
    intro i j
    haveI := i1_relativeSubcomplexChainMap_mono X Z (U i) ⊤ le_top
    dsimp [p]
    infer_instance
  exact i1_chainCoverCoclass_ext (F.obj ⊤) (fun i => F.obj (U i)) p n
    (i1_directedRelativeChain_scalar_factor X Z U hdir n hcover) u v h

end HodgeLean.Foundations.BundleThom
