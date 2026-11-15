import HodgeLean.Foundations.Program.SchoenCycleIntersectionDefs
import HodgeLean.Foundations.Program.SchoenCycleC2ComponentClassHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ComponentUniquenessHelpers

/-! # Normalized classes for the retained component

The ambient may be singular outside the specified smooth open. Neither the
immersion nor the supported group is replaced when selecting a representative.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Existence and uniqueness of the actual normalized supported component class.
Source: Fulton, Intersection Theory, second edition, §19.1; Schoen (1988), p. 15. -/
theorem g32w12_normalized_component_exists_unique
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
    (U : W.left.Opens) (hU : Set.range ι.left ⊆ U)
    (hsm : Smooth (U.ι ≫ W.hom))
    (hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = k) :
    ∃! c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k,
      a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c := by
  obtain ⟨c, hc⟩ := s2e_componentCycle_normalized_class_of_smooth_open
    ι U hU hsm k hcodim
  exact ⟨c, hc, fun d hd =>
    s2e_componentCycle_class_unique_of_smooth_open ι k U hU hsm hcodim d c hd hc⟩

/-- The native self-restriction is independent of its normalized representative.
Source: Fulton, Intersection Theory, second edition, §§6.3, 19.1. -/
theorem g32w12_normalEuler_eq_of_normalized
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
    (U : W.left.Opens) (hU : Set.range ι.left ⊆ U)
    (hsm : Smooth (U.ι ≫ W.hom))
    (hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = k)
    (c d : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c)
    (hd : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k d) :
    s2e_normalEuler ι k c = s2e_normalEuler ι k d := by
  rw [s2e_componentCycle_class_unique_of_smooth_open ι k U hU hsm hcodim c d hc hd]

#print axioms g32w12_normalized_component_exists_unique
#print axioms g32w12_normalEuler_eq_of_normalized
end HodgeLean.Foundations.Program
