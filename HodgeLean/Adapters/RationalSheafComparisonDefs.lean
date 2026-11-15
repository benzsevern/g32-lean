import HodgeLean.Foundations.Topology.RationalSheafComparisonDefs
import HodgeLean.Foundations.Program.SchoenTransferQuotientSheaf

/-! Rational singular and constant-sheaf comparison interfaces.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Topology.RationalSheafComparison
namespace HodgeLean.Adapters.RationalSheafComparison

/-- The project adapter uses the existing rational sheaf-cohomology carrier.
Source: Bredon, Sheaf Theory, second edition, II.4 and III.1;
AlgebraicTopology.Singular singular-cochain and constant-sheaf constructions. -/
def pullback {X Y : Over (Spec ↧ℂ)} (q : X ⟶ Y) (n : ℕ) : HQ Y n →+ HQ X n :=
  sheafPullback (TopCat.ofHom (Point.continuousMap q)) n

/-- The rational comparison specialized to the actual complex-point space, retaining its basis input.
Source: Bredon, Sheaf Theory, second edition, II.4 and III.1;
AlgebraicTopology.Singular singular-cochain and constant-sheaf constructions. -/
def comparison (X : Over (Spec ↧ℂ))
    (hX : ∀ (x : ComplexPoint X) (U : TopologicalSpace.Opens (ComplexPoint X)), x ∈ U →
      ∃ V : TopologicalSpace.Opens (ComplexPoint X),
        x ∈ V ∧ ContractibleSpace V ∧ V ≤ U) (n : ℕ) :
    AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint X)) n →+ HQ X n :=
  HodgeLean.Topology.RationalSheafComparison.comparison (TopCat.of (ComplexPoint X)) hX n

end HodgeLean.Adapters.RationalSheafComparison
