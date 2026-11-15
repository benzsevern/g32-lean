import HodgeLean.Foundations.AnalyticDivisorAlgebraic22Orbits
import HodgeLean.Adapters.ThetaDivisorOnX

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic22
open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic21
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs
open scoped Manifold CategoryTheory.MonObj

/-- The same orbit-indexed carrier family on complex points, using the canonical exponential.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, §1.1; `abelianExp`. -/
def gaga22_descendedOnX (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p) : gaga21_WeightedCarrierFamily (ComplexPoint X) where
  Component := gaga22_ComponentOrbit (abelianPeriodLattice X).toAddSubgroup hD hper
  carrier O := abelianExp X '' gaga21_componentCarrier (Quotient.out O)
  multiplicity O := (gaga21_gluedDivisor V f).multiplicity (Quotient.out O)

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p) : gaga21_WeightedCarrierFamily (ComplexPoint X) :=
  gaga22_descendedOnX X hD hper

end HodgeLean.Foundations.AnalyticDivisorAlgebraic22
