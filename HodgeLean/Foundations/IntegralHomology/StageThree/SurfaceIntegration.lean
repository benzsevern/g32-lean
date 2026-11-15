import HodgeLean.Foundations.IntegralHomology.StageThree.Defs
import HodgeLean.Foundations.IntegralHomology.StageThree.SurfaceSpan
import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralCoefficientPairing
import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralTorsionKernel

/-! Integral surface integration with the specified Abel–Jacobi normalization. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Manifold
open HodgeLean.Foundations.Program HodgeLean.Adapters
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.IntegralHomology.StageThree
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]

def surfaceIntegration (aj : C → b3_Jacobian E C) (haj : Continuous aj) :
    Lattice (TopCat.of C) →ₗ[ℤ] (b3_HolForm E C → ℂ) :=
  LinearMap.pi (fun θ => cocyclePairing (TopCat.of C)
    (b3Rest2_integCocycle aj haj (AddMonoidHom.id ℂ) θ))

theorem surfaceIntegration_lift (aj : C → b3_Jacobian E C) (haj : Continuous aj)
    (z : (ZChains (TopCat.of C)).cycles (1 : ℕ)) (θ : b3_HolForm E C) :
    surfaceIntegration aj haj (Submodule.Quotient.mk ((ZChains (TopCat.of C)).homologyπ (1 : ℕ) z)) θ =
      b3Rest2_ellV θ (s4_c1a6_liftChain (b3Rest2_covHom (E := E) (C := C))
        b3Rest2_covHom_spec aj haj ((ZChains (TopCat.of C)).iCycles (1 : ℕ) z)) :=
  s4_c1a6_liftCocycle_pairing_cycle (b3Rest2_covHom (E := E) (C := C))
    b3Rest2_covHom_spec aj haj ((AddMonoidHom.id ℂ).comp (b3Rest2_ellV θ)) z

theorem surfaceIntegration_mem (aj : C → b3_Jacobian E C) (haj : Continuous aj)
    (a : Lattice (TopCat.of C)) : surfaceIntegration aj haj a ∈ b3_periodLattice E C := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ZChains (TopCat.of C)).homologyπ (1 : ℕ))).mp inferInstance x
  let v := s4_c1a6_liftChain (b3Rest2_covHom (E := E) (C := C))
    b3Rest2_covHom_spec aj haj ((ZChains (TopCat.of C)).iCycles (1 : ℕ) z)
  have hv := s4_c1a6_liftChain_cycle_project_zero
    (b3Rest2_covHom (E := E) (C := C)) b3Rest2_covHom_spec aj haj z
  change (QuotientAddGroup.mk ((b2_coord (b3Rest2_QJ E C)).symm v) : b3_Jacobian E C) = 0 at hv
  obtain ⟨l, hl⟩ := (QuotientAddGroup.eq_zero_iff _).mp hv
  have he : surfaceIntegration aj haj (Submodule.Quotient.mk
      ((ZChains (TopCat.of C)).homologyπ (1 : ℕ) z)) = l.val := by
    funext θ
    rw [surfaceIntegration_lift]
    change (b3_periodF E C).liftQ (b3_cplxPeriod E C) le_rfl
      ((b2_coord (b3Rest2_QJ E C)).symm v) θ = l.val θ
    rw [← hl]
    change b3_cplxPeriod E C ((1 : ℂ) ⊗ₜ[ℤ] l) θ = l.val θ
    rw [b3_cplxPeriod, LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  rw [he]
  exact l.property

def surfaceIntegrationLattice (aj : C → b3_Jacobian E C) (haj : Continuous aj) :
    Lattice (TopCat.of C) →ₗ[ℤ] b3_periodLattice E C :=
  (surfaceIntegration aj haj).codRestrict (b3_periodLattice E C).toIntSubmodule
    (surfaceIntegration_mem aj haj)

theorem surfaceIntegration_loop (hE : Module.finrank ℂ E = (1 : ℕ))
    (p₀ : C) (aj : C → b3_Jacobian E C) (haj : Continuous aj)
    (h : b3_IsAbelJacobi E C p₀ aj) (γ : b3_SmoothLoop E C) :
    surfaceIntegrationLattice aj haj (Submodule.Quotient.mk
      ((ZChains (TopCat.of C)).homologyπ (1 : ℕ)
        (((ZChains (TopCat.of C)).sc (1 : ℕ)).moduleCatCyclesIso.inv
          (loopCycle ℤ (b3Rest2_circ γ))))) = b3_latticePeriod E C γ := by
  apply Subtype.ext
  funext θ
  change s4_c1a6_integralCocyclePairing (TopCat.of C)
    (b3Rest2_integCocycle aj haj (AddMonoidHom.id ℂ) θ)
    (Submodule.Quotient.mk ((ZChains (TopCat.of C)).homologyπ (1 : ℕ)
      (((ZChains (TopCat.of C)).sc (1 : ℕ)).moduleCatCyclesIso.inv
        (loopCycle ℤ (b3Rest2_circ γ))))) = b3_period E C γ θ
  rw [s4_c1a6_integralCocyclePairing_cycle]
  change (b3Rest2_integCocycle aj haj (AddMonoidHom.id ℂ) θ).val
    (s4_c1a6_zToCChainGroup _ (1 : ℕ)
      (((((ZChains (TopCat.of C)).sc (1 : ℕ)).moduleCatCyclesIso.inv) ≫
        ((ZChains (TopCat.of C)).sc (1 : ℕ)).iCycles) (loopCycle ℤ (b3Rest2_circ γ)))) = _
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles]
  change (b3Rest2_integCocycle aj haj (AddMonoidHom.id ℂ) θ).val
    (s4_c1a6_zToCChainGroup _ (1 : ℕ)
      ((SSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) _ (loopSimplex (b3Rest2_circ γ))).hom (1 : ℤ))) = _
  rw [s4_c1a6_zToCChainGroup_iota, Int.cast_one]
  exact b3Rest2_integCocycle_loop aj haj hE p₀ h (AddMonoidHom.id ℂ) θ γ
    (b3Rest2_circ γ) (b3Rest2_circ_apply γ)

theorem surfaceIntegration_surjective (hE : Module.finrank ℂ E = (1 : ℕ))
    (p₀ : C) (aj : C → b3_Jacobian E C) (haj : Continuous aj)
    (h : b3_IsAbelJacobi E C p₀ aj) : Function.Surjective (surfaceIntegrationLattice aj haj) := by
  have hr : b3_periodLattice E C ≤ (surfaceIntegration aj haj).toAddMonoidHom.range := by
    rw [b3_periodLattice, AddSubgroup.closure_le]
    rintro _ ⟨γ, rfl⟩
    refine ⟨Submodule.Quotient.mk ((ZChains (TopCat.of C)).homologyπ (1 : ℕ)
      (((ZChains (TopCat.of C)).sc (1 : ℕ)).moduleCatCyclesIso.inv
        (loopCycle ℤ (b3Rest2_circ γ)))), ?_⟩
    exact congrArg Subtype.val (surfaceIntegration_loop hE p₀ aj haj h γ)
  intro l
  obtain ⟨a, ha⟩ := hr l.property
  exact ⟨a, Subtype.ext ha⟩

theorem surfaceIntegration_real_cycle (aj : C → b3_Jacobian E C) (haj : Continuous aj)
    (z : (ZChains (TopCat.of C)).cycles (1 : ℕ)) (θ : b3_HolForm E C) :
    s4_c1a6_integralCocyclePairing (TopCat.of C)
      (b3Rest2_integCocycle aj haj b3Rest2_gre θ)
      (Submodule.Quotient.mk ((ZChains (TopCat.of C)).homologyπ (1 : ℕ) z)) =
    ((surfaceIntegration aj haj
      (Submodule.Quotient.mk ((ZChains (TopCat.of C)).homologyπ (1 : ℕ) z)) θ).re : ℂ) := by
  rw [surfaceIntegration_lift]
  exact s4_c1a6_liftCocycle_pairing_cycle
    (b3Rest2_covHom (E := E) (C := C)) b3Rest2_covHom_spec aj haj
    (b3Rest2_gre.comp (b3Rest2_ellV θ)) z

theorem surfaceIntegration_injective (hE : Module.finrank ℂ E = (1 : ℕ))
    (p₀ : C) (aj : C → b3_Jacobian E C) (haj : Continuous aj)
    (h : b3_IsAbelJacobi E C p₀ aj) : Function.Injective (surfaceIntegrationLattice aj haj) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ZChains (TopCat.of C)).homologyπ (1 : ℕ))).mp inferInstance x
  have hz : surfaceIntegration aj haj
      (Submodule.Quotient.mk ((ZChains (TopCat.of C)).homologyπ (1 : ℕ) z)) = 0 :=
    congrArg Subtype.val ha
  let X := TopCat.of C
  let u := s4_c1a6_zbc_zToCHomology X (1 : ℕ) ((ZChains X).homologyπ (1 : ℕ) z)
  let ev : AlgebraicTopology.Singular.Cohomology ℂ X (1 : ℕ) →ₗ[ℂ] ℂ :=
    (LinearMap.applyₗ u).comp
      (AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ X (1 : ℕ)).toLinearMap
  letI := b3_holForm_finiteDimensional (E := E) (C := C) hE
  let b := Module.finBasis ℝ (b3_HolForm E C)
  have he (θ : b3_HolForm E C) : ev (surfaceRealClass C aj haj θ) = 0 := by
    change AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ X (1 : ℕ)
      (Singular.cohomologyClass X (1 : ℕ) (b3Rest2_integCocycle aj haj b3Rest2_gre θ)) u = 0
    dsimp only [u]
    erw [s4_c1a6_cohomologyClass_zToCHomology]
    rw [surfaceIntegration_real_cycle, hz]
    rfl
  have hk : (⊤ : Submodule ℂ (AlgebraicTopology.Singular.Cohomology ℂ X (1 : ℕ))) ≤ ev.ker := by
    rw [← surfaceRealClass_span C hE aj haj p₀ h b]
    exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact he (b j))
  have hu : u = 0 := by
    apply (Module.forall_dual_apply_eq_zero_iff ℂ u).mp
    intro l
    obtain ⟨c, rfl⟩ :=
      (AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ X (1 : ℕ)).surjective l
    exact hk (Submodule.mem_top : c ∈ (⊤ : Submodule ℂ _))
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (s4_c1a6_zToCHomology_zero_mem_torsion X (1 : ℕ) _ hu)

end HodgeLean.Foundations.IntegralHomology.StageThree
