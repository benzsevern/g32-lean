import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralCoefficients
import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralCycles

/-! Scalar integration pairings on actual integral singular homology modulo torsion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Manifold
open HodgeLean.Adapters
open scoped ContDiff
namespace HodgeLean.Foundations.Program
variable (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom]
    [ChartedSpace ℂ (ComplexPoint Y)] [IsManifold 𝓘(ℂ, ℂ) ω (ComplexPoint Y)]
    [T2Space (ComplexPoint Y)] [CompactSpace (ComplexPoint Y)]
    [ConnectedSpace (ComplexPoint Y)]

local instance : Module.Finite ℤ (b3_periodLattice ℂ (ComplexPoint Y)) :=
  b3_periodLattice_finite (Module.finrank_self ℂ)
local instance : Module.Free ℤ (b3_periodLattice ℂ (ComplexPoint Y)) :=
  b3_periodLattice_free
local instance : DiscreteTopology
    (b2_latticeMap (b3_periodLattice ℂ (ComplexPoint Y))
      (b3_periodF ℂ (ComplexPoint Y))).range :=
  b2_latticeMap_discrete _ (b3_isWeightOne (Module.finrank_self ℂ))

/-- The scalar integration functional obtained from a continuous Abel–Jacobi map. -/
def s4_c1a6_integralFormPairing
    (aj : ComplexPoint Y → b3_Jacobian ℂ (ComplexPoint Y)) (haj : Continuous aj)
    (θ : b3_HolForm ℂ (ComplexPoint Y)) : s4_c1a6_integralLattice Y →ₗ[ℤ] ℂ :=
  s4_c1a6_integralCocyclePairing (TopCat.of (ComplexPoint Y))
    (b3Rest2_integCocycle aj haj (AddMonoidHom.id ℂ) θ)

theorem s4_c1a6_integralFormPairing_loop
    (aj : ComplexPoint Y → b3_Jacobian ℂ (ComplexPoint Y)) (haj : Continuous aj)
    (p₀ : ComplexPoint Y) (h : b3_IsAbelJacobi ℂ (ComplexPoint Y) p₀ aj)
    (θ : b3_HolForm ℂ (ComplexPoint Y)) (γ : b3_SmoothLoop ℂ (ComplexPoint Y)) :
    s4_c1a6_integralFormPairing Y aj haj θ
      (s4_c1a6_cycleClass Y (s4_c1a6_smoothLoopCycle Y γ)) =
      b3_period ℂ (ComplexPoint Y) γ θ := by
  change s4_c1a6_integralCocyclePairing (TopCat.of (ComplexPoint Y))
    (b3Rest2_integCocycle aj haj (AddMonoidHom.id ℂ) θ)
    (Submodule.Quotient.mk ((s4_c1a6_ZChains (TopCat.of (ComplexPoint Y))).homologyπ 1
      (s4_c1a6_smoothLoopCycle Y γ))) = _
  rw [s4_c1a6_integralCocyclePairing_cycle]
  change (b3Rest2_integCocycle aj haj (AddMonoidHom.id ℂ) θ).val
    (s4_c1a6_zToCChainGroup (TopCat.of (ComplexPoint Y)) 1
      ((s4_c1a6_chains Y).iCycles 1 (s4_c1a6_smoothLoopCycle Y γ))) = _
  rw [s4_c1a6_smoothLoopCycle_chain, s4_c1a6_pathChain_loop]
  change (b3Rest2_integCocycle aj haj (AddMonoidHom.id ℂ) θ).val
    (s4_c1a6_zToCChainGroup (TopCat.of (ComplexPoint Y)) 1
      ((SSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) _ _).hom 1)) = _
  rw [s4_c1a6_zToCChainGroup_iota, Int.cast_one]
  exact b3Rest2_integCocycle_loop aj haj (Module.finrank_self ℂ) p₀ h
    (AddMonoidHom.id ℂ) θ γ (b3Rest2_circ γ) (b3Rest2_circ_apply γ)

end HodgeLean.Foundations.Program
