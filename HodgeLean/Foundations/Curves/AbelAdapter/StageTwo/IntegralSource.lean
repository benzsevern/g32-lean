import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.Defs

/-! # Source integral coordinates for the retained Abel map

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations.Program HodgeLean.Foundations.IntegralHomology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Continuity of the retained analytic Abel map.
Source: Forster, §21; b3_abelJacobi_holomorphic.
HC no distance; AV milestone no distance. -/
theorem analyticAbel_continuous (h : Module.finrank ℂ E = 1) (p : C) :
    Continuous (analyticAbel h p) := by
  letI := b3_periodLattice_finite (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := C) h)
  exact (b3_abelJacobi_holomorphic h p _ (b3_exists_abelJacobi h p).choose_spec).continuous

/-- Integral source coordinates obtained from integration, with the retained base point.
Source: Forster, §§19–21; StageThree.surfaceIntegration_injective and
StageThree.surfaceIntegration_surjective.
HC no distance; AV milestone no distance. -/
def curvePeriodEquiv (h : Module.finrank ℂ E = 1) (p : C) :
    IntegralHomology.Lattice (TopCat.of C) ≃ₗ[ℤ] b3_periodLattice E C := by
  letI := b3_periodLattice_finite (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := C) h)
  exact LinearEquiv.ofBijective
    (StageThree.surfaceIntegrationLattice (analyticAbel h p) (analyticAbel_continuous h p))
    ⟨StageThree.surfaceIntegration_injective h p _ _
      (b3_exists_abelJacobi h p).choose_spec,
     StageThree.surfaceIntegration_surjective h p _ _
      (b3_exists_abelJacobi h p).choose_spec⟩

/-- Integration coordinates retain the literal period of every smooth loop.
Source: Forster, §21; StageThree.surfaceIntegration_loop.
HC no distance; AV milestone no distance. -/
theorem curvePeriodEquiv_loop (h : Module.finrank ℂ E = 1) (p : C)
    (c : b3_SmoothLoop E C) :
    curvePeriodEquiv h p (loopClass c) = b3_latticePeriod E C c := by
  letI := b3_periodLattice_finite (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := C) h)
  exact StageThree.surfaceIntegration_loop h p _ _ (b3_exists_abelJacobi h p).choose_spec c

/-- Maps on integral source homology are determined on smooth-loop classes.
Source: Hatcher, §2.1; Forster, §21; curvePeriodEquiv_loop.
HC no distance; AV milestone no distance. -/
theorem curveLattice_hom_ext (h : Module.finrank ℂ E = 1) (p : C)
    {M : Type*} [AddCommGroup M]
    (f g : IntegralHomology.Lattice (TopCat.of C) →+ M)
    (he : ∀ c : b3_SmoothLoop E C, f (loopClass c) = g (loopClass c)) : f = g := by
  let e := curvePeriodEquiv h p
  have hall : ∀ l : b3_periodLattice E C, f (e.symm l) = g (e.symm l) := by
    rintro ⟨l, hl⟩
    induction hl using AddSubgroup.closure_induction with
    | mem l hl =>
        obtain ⟨c, rfl⟩ := hl
        have hc : e.symm (b3_latticePeriod E C c) = loopClass c := by
          apply e.injective
          rw [e.apply_symm_apply]
          exact (curvePeriodEquiv_loop h p c).symm
        exact (congrArg f hc).trans ((he c).trans (congrArg g hc).symm)
    | zero =>
        change f (e.symm 0) = g (e.symm 0)
        simp only [map_zero]
    | add a b ha hb hfa hfb =>
        change f (e.symm (⟨a, ha⟩ + ⟨b, hb⟩)) = g (e.symm (⟨a, ha⟩ + ⟨b, hb⟩))
        simp only [map_add, hfa, hfb]
    | neg a ha hfa =>
        change f (e.symm (-⟨a, ha⟩)) = g (e.symm (-⟨a, ha⟩))
        simp only [map_neg, hfa]
  ext a
  simpa only [e.symm_apply_apply] using hall (e a)

#print axioms analyticAbel_continuous
#print axioms curvePeriodEquiv
#print axioms curvePeriodEquiv_loop
#print axioms curveLattice_hom_ext

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
