import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.PeriodFormDuality
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.IntegralSource

/-! # Original period covectors on integral lattice vectors

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations.Program HodgeLean.Foundations.IntegralHomology
open scoped TensorProduct Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- The original cover covector evaluates a lattice vector as its original curve period.
Source: Forster, §21; b3_cplxPeriod; b2_latticeMap.
HC no distance; AV milestone no distance. -/
theorem periodLinear_lattice [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (θ : b3_HolForm E C) (l : b3_periodLattice E C) :
    periodLinear θ (b5_lattice (b3_periodLattice E C) (b3_periodF E C) l) = l.val θ := by
  change (b3_periodF E C).liftQ (b3_cplxPeriod E C) le_rfl
    ((b2_coord (b3Rest2_QJ E C)).symm
      ((b2_coord (b3Rest2_QJ E C)) (Submodule.Quotient.mk ((1 : ℂ) ⊗ₜ[ℤ] l)))) θ = l.val θ
  rw [LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  change LinearMap.liftBaseChange ℂ (b3_periodLattice E C).subtype.toIntLinearMap ((1 : ℂ) ⊗ₜ[ℤ] l) θ = _
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  rfl

/-- The source integral equivalence retains every original integration-cocycle evaluation.
Source: Forster, §21; StageThree.surfaceIntegrationLattice.
HC no distance; AV milestone no distance. -/
theorem curvePeriodEquiv_pairing (h : Module.finrank ℂ E = 1) (p : C)
    (a : IntegralHomology.Lattice (TopCat.of C)) (θ : b3_HolForm E C) :
    letI := b3_periodLattice_finite (C := C) h
    letI := b3_periodLattice_free (E := E) (C := C)
    letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := C) h)
    (curvePeriodEquiv h p a).val θ = StageThree.cocyclePairing (TopCat.of C)
      (b3Rest2_integCocycle (analyticAbel h p) (analyticAbel_continuous h p)
        (AddMonoidHom.id ℂ) θ) a := by
  letI := b3_periodLattice_finite (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := C) h)
  rfl

#print axioms periodLinear_lattice
#print axioms curvePeriodEquiv_pairing
end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
