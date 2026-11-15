import HodgeLean.Adapters.HolomorphicPeriodsCocycleProofs
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Cap.Simplicial

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData

/-- The chain-level cap product transported to the actual singular cohomology carrier.
Source: Hatcher, Algebraic Topology, §3.3, cap product. -/
def s4_selected_singular_cap (T : TopCat.{0}) (p q : ℕ) :
    Cohomology ℚ T p →ₗ[ℚ] (Homology ℚ T (p + q) →ₗ[ℚ] Homology ℚ T q) :=
  (capCohomologyLinear ℚ p q).comp
    (cochainCohomologyEquiv ℚ T p).symm.toLinearMap

/-- The transported cap product evaluates a cocycle by the original homological cap map.
Source: Hatcher, Algebraic Topology, §3.3, descent of cap from chains and cocycles. -/
theorem s4_selected_singular_cap_cocycle (T : TopCat.{0}) (p q : ℕ)
    (φ : Cocycle ℚ (TopCat.toSSet.obj T) p) :
    s4_selected_singular_cap T p q (Singular.cohomologyClass T p φ) =
      capHomologyMap ℚ p q φ.1 φ.2 := by
  let K := SingularChainComplex ℚ T
  let D := (K.sc p).linearDual
  let φ' : LinearMap.ker D.g.hom := ⟨φ.1, by
    change (((TopCat.toSSet.obj T).chainComplex (ModuleCat.of ℚ ℚ)).d
      ((ComplexShape.down ℕ).prev p) p).hom.dualMap φ.1 = 0
    rw [ChainComplex.prev]
    exact φ.2⟩
  have hc : Singular.cohomologyClass T p φ =
      cochainCohomologyEquiv ℚ T p
        (D.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk φ')) := rfl
  rw [hc]
  change capCohomologyLinear ℚ p q
    ((cochainCohomologyEquiv ℚ T p).symm
      (cochainCohomologyEquiv ℚ T p
        (D.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk φ')))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact capCohomologyLinear_on_cycle (X := TopCat.toSSet.obj T) ℚ p q φ'

#print axioms s4_selected_singular_cap
#print axioms s4_selected_singular_cap_cocycle
end HodgeLean.Foundations.Program
