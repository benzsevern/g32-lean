import HodgeLean.Foundations.Program.SchoenCycleC2ComponentPairHelpers
import HodgeLean.Foundations.Program.CompensationAssemblyRelativeProduct
import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientCohomology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Forgetting component support commutes with the actual open-immersion pullback. -/
theorem s2e_componentOpenPairMap_absolute
    {Q V W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (j : Q ⟶ V) (i : V ⟶ W)
    [IsClosedImmersion j.left] [IsOpenImmersion i.left]
    [IsClosedImmersion (j ≫ i).left] (k : ℕ)
    (c : s2e_supportedClass W (s2e_componentCycle (j ≫ i) ℚ) k) :
    s2e_classToAbsolute V (s2e_componentCycle j ℚ) k
      (relativeCohomologyMap ℚ (2 * k) (s2e_componentOpenPairMap j i) c) =
      s2e_pullback ℚ i (2 * k)
        (s2e_classToAbsolute W (s2e_componentCycle (j ≫ i) ℚ) k c) := by
  exact cq_relativeToAbsolute_naturality (s2e_componentOpenPairMap j i) (2 * k) c

/-- The identity scheme morphism gives identity on the actual singular cohomology. -/
theorem s2e_pullback_id (W : Over (Spec ↧ℂ)) (n : ℕ) :
    s2e_pullback ℚ (𝟙 W) n = LinearMap.id := by
  exact cohomologyMap_id ℚ (TopCat.of (ComplexPoint W)) n

/-- Inverse pullback cancels pullback by a scheme isomorphism. -/
theorem s2e_pullback_inv_cancel {V W : Over (Spec ↧ℂ)}
    (f : V ⟶ W) [IsIso f] (n : ℕ)
    (a : Cohomology ℚ (TopCat.of (ComplexPoint W)) n) :
    s2e_pullback ℚ (inv f) n (s2e_pullback ℚ f n a) = a := by
  have h := congrArg (fun L => L a) (s2e_quotient_pullback_comp (inv f) f n)
  rw [IsIso.inv_hom_id, s2e_pullback_id, LinearMap.id_apply, LinearMap.comp_apply] at h
  exact h.symm

end HodgeLean.Foundations.Program
