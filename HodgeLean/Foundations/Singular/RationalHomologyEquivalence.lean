import HodgeLean.Foundations.Singular.RationalHomologyHomotopy

/-! Actual rational chain homotopy equivalences with zero-differential homology complexes. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- Inclusion of the chosen rational homology representatives followed by projection is the identity chain map.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
theorem rationalHomologyChainInclusion_projection (K : ChainComplex (ModuleCat ℚ) ℕ) :
    rationalHomologyChainInclusion K ≫ rationalHomologyChainProjection K = 𝟙 (rationalHomologyComplex K) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact rationalHomologyProjection_inclusion K n

/-- Every actual rational chain complex is chain homotopy equivalent to its zero-differential homology quotients.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
def rationalHomologyHomotopyEquiv (K : ChainComplex (ModuleCat ℚ) ℕ) :
    HomotopyEquiv K (rationalHomologyComplex K) where
  hom := rationalHomologyChainProjection K
  inv := rationalHomologyChainInclusion K
  homotopyHomInvId := (rationalHomologyDeformationHomotopy K).symm
  homotopyInvHomId := Homotopy.ofEq (rationalHomologyChainInclusion_projection K)

#print axioms rationalHomologyHomotopyEquiv
#print axioms rationalHomologyChainInclusion_projection
end HodgeLean.Foundations.Singular
