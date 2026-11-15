import HodgeLean.Foundations.Singular.RationalHomologyComplex

/-! Actual chain maps to and from the chosen rational homology representatives. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Singular

/-- The chosen homology projection is an actual map of rational chain complexes.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
def rationalHomologyChainProjection (K : ChainComplex (ModuleCat ℚ) ℕ) :
    K ⟶ rationalHomologyComplex K where
  f n := ModuleCat.ofHom (rationalHomologyProjection K n)
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change 0 = rationalHomologyProjection K j ((K.d (j + 1) j).hom z)
    exact (rationalHomologyProjection_boundary K j z).symm

/-- The chosen homology representatives give an actual map of rational chain complexes.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
def rationalHomologyChainInclusion (K : ChainComplex (ModuleCat ℚ) ℕ) :
    rationalHomologyComplex K ⟶ K where
  f n := ModuleCat.ofHom (rationalHomologyInclusion K n)
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (K.d (j + 1) j).hom (rationalHomologyInclusion K (j + 1) z) =
      rationalHomologyInclusion K j 0
    rw [map_zero]
    exact (rationalHomologyRepresentative K (j + 1) z).property

#print axioms rationalHomologyChainInclusion
#print axioms rationalHomologyChainProjection
end HodgeLean.Foundations.Singular
