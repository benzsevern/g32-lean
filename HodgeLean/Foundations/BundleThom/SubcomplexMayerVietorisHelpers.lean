import HodgeLean.Foundations.BundleThom.SubcomplexChainPushoutHelpers
import Mathlib.CategoryTheory.Limits.MonoCoprod

/-! # The actual rational intersection–union chain sequence

The difference map from intersection chains and the sum map to union chains form a short exact sequence.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- The actual rational chain short complex of a supplied subcomplex intersection and union.
Source: Hatcher, Algebraic Topology, §2.2, Mayer–Vietoris chain sequence. -/
def i1_subcomplexChainSequence (X : SSet) (U V : X.Subcomplex) :
    ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) :=
  (i1_subcomplexChains_isPushout X U V).shortComplex

/-- The actual rational intersection–union chain sequence is exact.
Source: Hatcher, Algebraic Topology, §2.2, Mayer–Vietoris chain sequence. -/
theorem i1_subcomplexChainSequence_exact (X : SSet) (U V : X.Subcomplex) :
    (i1_subcomplexChainSequence X U V).Exact :=
  (i1_subcomplexChains_isPushout X U V).exact_shortComplex

/-- The actual rational intersection–union chain sequence is short exact.
Source: Hatcher, Algebraic Topology, §2.2, Mayer–Vietoris chain sequence. -/
theorem i1_subcomplexChainSequence_shortExact (X : SSet) (U V : X.Subcomplex) :
    (i1_subcomplexChainSequence X U V).ShortExact := by
  haveI : Mono (SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.of ℚ ℚ)) := by
    dsimp [SSet.chainComplexMap, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  refine { exact := i1_subcomplexChainSequence_exact X U V, mono_f := ?_, epi_g := ?_ }
  · change Mono (biprod.lift _ _)
    infer_instance
  · exact (i1_subcomplexChains_isPushout X U V).epi_shortComplex_g

end HodgeLean.Foundations.BundleThom
