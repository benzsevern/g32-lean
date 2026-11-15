import HodgeLean.Foundations.AnalyticDivisorAlgebraic22ChowProofs

/-! # Set-level Chow reduction for descended divisor supports

This is an implication from the published set-level Chow theorem. It constructs neither
codimension-one scheme points nor squarefree local equations. Those are further obligations
for the bh4 algebraization consumer. The bh4 branch is not imported.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic22
open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic21
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs
open scoped Manifold CategoryTheory.MonObj

/-- Set-level Chow implies algebraic irreducible supports for the descended weighted family.
The explicit Chow binder applies to all closed analytic subsets, independently of divisor data.
Source: Serre, Géométrie algébrique et géométrie analytique, Théorème 3 (Chow);
Chirka §5.1 (irreducibility); Hartshorne I.1 (irreducible components). -/
theorem gaga22_chow_support (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C) :
    Finite (gaga22_descendedOnX X hD hper).Component ∧
    ∃ C : (gaga22_descendedOnX X hD hper).Component → Set X.left,
      Function.Injective C ∧
      (∀ O, IsClosed (C O) ∧ IsIrreducible (C O) ∧
        (gaga22_descendedOnX X hD hper).carrier O =
          (Point.underlying : ComplexPoint X → X.left) ⁻¹' C O ∧
        0 < (gaga22_descendedOnX X hD hper).multiplicity O) ∧
      abelianExp X '' localDivisorSupport V f =
        ⋃ O, (Point.underlying : ComplexPoint X → X.left) ⁻¹' C O :=
  gaga22_chow_support_aux X hD hper hChow

end HodgeLean.Foundations.AnalyticDivisorAlgebraic22
