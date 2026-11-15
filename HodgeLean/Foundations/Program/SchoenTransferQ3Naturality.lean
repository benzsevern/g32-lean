import HodgeLean.Foundations.Program.SchoenTransferDefs
import HodgeLean.Foundations.Program.CompensationAssemblyRelativeProduct

/-! Supported-to-absolute naturality for the retained transfer map. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Forgetting support commutes with the specified singular pullback for any
support certificate, including certificates obtained after prime collection. -/
theorem s4_q3_supported_pullback_forget
    {X W : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType W.hom] (q : X ⟶ W)
    (γ : AlgebraicCycle X.left ℚ) (z : AlgebraicCycle W.left ℚ) (k : ℕ)
    (hS : ∀ x, Point.map q x ∈ a3b4_cycleSupport W.hom z →
      x ∈ a3b4_cycleSupport X.hom γ)
    (c : s2e_supportedClass W z k) :
    s2e_classToAbsolute X γ k
      (relativeCohomologyMap ℚ (2 * k)
        (a3b4_supportPairMap (TopCat.ofHom (Point.continuousMap q))
          (a3b4_cycleSupport X.hom γ) (a3b4_cycleSupport W.hom z) hS) c) =
      s4_singularPullback q (2 * k) (s2e_classToAbsolute W z k c) := by
  exact cq_relativeToAbsolute_naturality
    (a3b4_supportPairMap (TopCat.ofHom (Point.continuousMap q))
      (a3b4_cycleSupport X.hom γ) (a3b4_cycleSupport W.hom z) hS) (2 * k) c

end HodgeLean.Foundations.Program
