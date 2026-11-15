import HodgeLean.Foundations.BundleThom.RelativeSubcomplexPushoutHelpers

/-! # The actual relative rational intersection–union chain sequence

Relative complexes are the specified cokernels, and the sequence retains their canonical inclusion maps.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- The actual relative rational chain short complex for a fixed subspace and two ambient domains.
Source: Hatcher, Algebraic Topology, §2.2, relative Mayer–Vietoris chain sequence. -/
def i1_relativeSubcomplexChainSequence (X : SSet) (Z U V : X.Subcomplex) :
    ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) :=
  (i1_relativeSubcomplexChains_isPushout X Z U V).shortComplex

/-- The actual relative rational intersection–union chain sequence is exact.
Source: Hatcher, Algebraic Topology, §2.2, relative Mayer–Vietoris chain sequence. -/
theorem i1_relativeSubcomplexChainSequence_exact (X : SSet) (Z U V : X.Subcomplex) :
    (i1_relativeSubcomplexChainSequence X Z U V).Exact :=
  (i1_relativeSubcomplexChains_isPushout X Z U V).exact_shortComplex

/-- The actual relative rational union chain map is an epimorphism.
Source: Hatcher, Algebraic Topology, §2.2, relative Mayer–Vietoris chain sequence. -/
theorem i1_relativeSubcomplexChainSequence_epi (X : SSet) (Z U V : X.Subcomplex) :
    Epi (i1_relativeSubcomplexChainSequence X Z U V).g :=
  (i1_relativeSubcomplexChains_isPushout X Z U V).epi_shortComplex_g

end HodgeLean.Foundations.BundleThom
