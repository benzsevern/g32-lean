import HodgeLean.Foundations.Singular.TorusTransport
import HodgeLean.Adapters.CupProductOf
import HodgeLean.Adapters.Lefschetz
import HodgeLean.RealDefs.AbelianExterior

/-! # C7 for abelian varieties
Stage S13 retires C7, C1 and O7 for abelian X, and reduces O3 to nondegeneracy.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Singular
namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- Rational cohomology of an abelian variety identified with its real model torus.
Source: `cupComparison` and `complexPointTorusHomeomorph`; Birkenhake–Lange,
Complex Abelian Varieties, Lemma 1.3.1. -/
def abelianTorusComparison (m : ℕ) : HQ X m ≃ₗ[ℚ]
    AlgebraicTopology.Singular.Cohomology ℚ
      (TopCat.of (UnitAddTorus (Fin (2 * dim X.left)))) m :=
  (cupComparison X m).trans
    (cohomologyHomeomorphEquiv (complexPointTorusHomeomorph X (dim X.left)) m)

example (m : ℕ) : Function.Bijective (abelianTorusComparison X m) :=
  (abelianTorusComparison X m).bijective

/-- C7 for the instantiated cup product on every smooth projective integral complex group.
The equivalence is induced by the specified cup-wedge map, not an arbitrary dimension match.
Source: Birkenhake–Lange, Complex Abelian Varieties, Lemma 1.3.1;
S5, S7 and S12, via `complexPointWedgeEquiv` and `cupComparison_cupWedgeMap`.
HC no distance; AV milestone no distance. -/
theorem torusCohomology_cupProductOf : TorusCohomology (cupProductOf X) := by
  refine ⟨?_, ?_, fun m => ?_⟩
  · let := finite_cohomology_unitAddTorus (2 * dim X.left) 1
    exact Module.Finite.equiv (abelianTorusComparison X 1).symm
  · rw [(abelianTorusComparison X 1).finrank_eq, finrank_cohomology_one_unitAddTorus]
  · have h := cupComparison_cupWedgeMap X m
    have hb : Function.Bijective
        ((cupComparison X m).toLinearMap.comp ((cupProductOf X).cupWedgeMap m)) := by
      rw [h]
      exact (complexPointWedgeEquiv X m).bijective.comp
        (exteriorPowerEquiv (cupComparison X 1) m).bijective
    exact ⟨fun a b hab => hb.1 (by simpa using congrArg (cupComparison X m) hab),
      fun b => by
        obtain ⟨a, ha⟩ := hb.2 (cupComparison X m b)
        exact ⟨a, (cupComparison X m).injective ha⟩⟩

example : TorusCohomology (cupProductOf X) := torusCohomology_cupProductOf X

/-- C1 for abelian varieties, supplied by the exterior-algebra description.
Source: `RealDefs.finiteBetti_of_torusCohomology` and `torusCohomology_cupProductOf`. -/
theorem finiteBetti_abelian : FiniteBetti X :=
  finiteBetti_of_torusCohomology (torusCohomology_cupProductOf X)

example : FiniteBetti X := finiteBetti_abelian X

/-- O7 for abelian varieties: cohomology vanishes above twice the complex dimension.
Source: `RealDefs.vanishingAboveTop_of_torusCohomology` and `torusCohomology_cupProductOf`. -/
theorem vanishingAboveTop_abelian : VanishingAboveTop X :=
  vanishingAboveTop_of_torusCohomology (torusCohomology_cupProductOf X)

example : VanishingAboveTop X := vanishingAboveTop_abelian X

/-- O3 for the instantiated product, conditional only on nondegeneracy of the
polarization's exterior preimage (in addition to the geometric scope).
Source: `hardLefschetz_of_torusCohomology`; Huybrechts, Complex Geometry, §1.2. -/
theorem hardLefschetz_abelian {η : HQ X 2}
    (hη : Symplectic.IsNondegenerate
      (((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm η)) :
    HardLefschetz X (cupProductOf X) η :=
  hardLefschetz_of_torusCohomology (torusCohomology_cupProductOf X) hη

example {η : HQ X 2} (hη : Symplectic.IsNondegenerate
    (((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm η)) :
    HardLefschetz X (cupProductOf X) η := hardLefschetz_abelian X hη

end HodgeLean.Adapters
