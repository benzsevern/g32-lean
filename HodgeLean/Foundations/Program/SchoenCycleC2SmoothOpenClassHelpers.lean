import HodgeLean.Foundations.Program.SchoenCycleC2OpenInstances
import HodgeLean.Adapters.NormalConeB4aClassExistsPure

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual component has a normalized supported class in its containing
smooth scheme neighbourhood. -/
theorem s2e_componentCycle_normalized_class_on_open
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (U : W.left.Opens) (hU : Set.range ι.left ⊆ U)
    (hsm : Smooth (U.ι ≫ W.hom)) (k : ℕ)
    (hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = k) :
    ∃ j : Q ⟶ ComplexPoint.openScheme W U,
      j ≫ ComplexPoint.openInclusion W U = ι ∧ IsClosedImmersion j.left ∧
      ∃ c : s2e_supportedClass (ComplexPoint.openScheme W U) (s2e_componentCycle j ℚ) k,
        a3b4_IsCycleClass (ComplexPoint.openScheme W U).hom (s2e_componentCycle j ℚ) k c := by
  letI : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  letI : CompactSpace W.left := a3b4_compactSpace W.hom
  letI : IsNoetherian W.left := {}
  letI : Smooth (ComplexPoint.openScheme W U).hom := hsm
  letI : QuasiCompact (ComplexPoint.openScheme W U).hom := inferInstance
  letI : IsSeparated (ComplexPoint.openScheme W U).hom := inferInstance
  obtain ⟨j, hj, hji, hjc⟩ := s2e_componentCycle_factor_open ι U hU k hcodim
  refine ⟨j, hj, hji, ?_⟩
  apply a3b4a_cycleClass_exists_of_codimension
  intro x hx
  rw [hjc x hx]

end HodgeLean.Foundations.Program
