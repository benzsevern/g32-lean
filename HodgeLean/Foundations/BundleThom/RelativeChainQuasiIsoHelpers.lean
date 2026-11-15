import HodgeLean.Foundations.BundleThom.RelativeSubcomplexMonomorphismHelpers
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Quasi-isomorphisms of actual relative cokernel chains

The two component chain comparisons give the comparison of their actual relative cokernels.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- The actual morphism of cokernel chain sequences induced by a supplied chain-arrow comparison.
Source: Hatcher, Algebraic Topology, §2.1, naturality of relative chain sequences. -/
def i1_chainArrowCokernelSequenceHom
    {a b : Arrow (ChainComplex (ModuleCat ℚ) ℕ)} (p : a ⟶ b) :
    ShortComplex.cokernelSequence a.hom ⟶ ShortComplex.cokernelSequence b.hom :=
  ShortComplex.homMk p.left p.right ((coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map p)
    p.w ((coker.π (ChainComplex (ModuleCat ℚ) ℕ)).naturality p)

/-- The actual cokernel chain sequence of a monic chain arrow is short exact.
Source: Hatcher, Algebraic Topology, §2.1, relative chain sequence. -/
theorem i1_chainArrowCokernelSequence_shortExact
    (a : Arrow (ChainComplex (ModuleCat ℚ) ℕ)) [Mono a.hom] :
    (ShortComplex.cokernelSequence a.hom).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by change Mono a.hom; infer_instance
  epi_g := by infer_instance

/-- Quasi-isomorphisms on both actual chain-arrow components induce a quasi-isomorphism on the relative cokernels.
Source: Hatcher, Algebraic Topology, §2.1, relative homology sequence and the five lemma. -/
theorem i1_chainArrowCokernelMap_quasiIso
    {a b : Arrow (ChainComplex (ModuleCat ℚ) ℕ)} (p : a ⟶ b) [Mono a.hom] [Mono b.hom]
    (hleft : QuasiIso p.left) (hright : QuasiIso p.right) :
    QuasiIso ((coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map p) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (i1_chainArrowCokernelSequenceHom p)
    (i1_chainArrowCokernelSequence_shortExact a) (i1_chainArrowCokernelSequence_shortExact b)
    hleft hright

/-- Component quasi-isomorphisms for an actual subcomplex inclusion give its actual relative chain quasi-isomorphism.
Source: Hatcher, Algebraic Topology, §2.2, relative small-chain comparison. -/
theorem i1_relativeSubcomplexChainMap_quasiIso (X : SSet) (Z U V : X.Subcomplex) (hUV : U ≤ V)
    (hleft : QuasiIso ((i1_relativeSubcomplexArrowFunctor X Z).map (homOfLE hUV)).left)
    (hright : QuasiIso ((i1_relativeSubcomplexArrowFunctor X Z).map (homOfLE hUV)).right) :
    QuasiIso ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE hUV)) := by
  haveI : Mono ((i1_relativeSubcomplexArrowFunctor X Z).obj U).hom := by
    dsimp [i1_relativeSubcomplexArrowFunctor, SSet.chainComplexMap, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  haveI : Mono ((i1_relativeSubcomplexArrowFunctor X Z).obj V).hom := by
    dsimp [i1_relativeSubcomplexArrowFunctor, SSet.chainComplexMap, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  exact i1_chainArrowCokernelMap_quasiIso
    ((i1_relativeSubcomplexArrowFunctor X Z).map (homOfLE hUV)) hleft hright

end HodgeLean.Foundations.BundleThom
