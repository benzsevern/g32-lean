import HodgeLean.Adapters.DegreeOneLattice
import HodgeLean.Adapters.TopCupPower
import HodgeLean.Foundations.AppellHumbertSectionsDefs

/-! # The lattice class in `HQ X 2`: definitions (FROZEN)

The stage-7 class `latticeClass E ∈ ⋀²(Λ →+ ℚ)` of an integral form `E` on the S12 period lattice
`Λ = abelianPeriodLattice X`, transported to `HQ X 2` along the inverse of the period equivalence
`HQ X 1 ≃ₗ[ℚ] (Λ →+ ℚ)` of `spec_abelianPeriod_equiv` and the canonical cup-wedge map
`(cupProductOf X).cupWedgeMap 2`. Nothing here says the class is algebraic, a Chern class or of
Hodge type `(1,1)`. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- The S12 period lattice is a free `ℤ`-module, by its S12 basis.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; `abelianLatticeBasis`. -/
instance abelianPeriodLattice_free : Module.Free ℤ (abelianPeriodLattice X) :=
  Module.Free.of_basis (abelianLatticeBasis X)

example : Module.Free ℤ (abelianPeriodLattice X) := inferInstance

/-- The S12 period lattice is a finitely generated `ℤ`-module, by its S12 basis.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; `abelianLatticeBasis`. -/
instance abelianPeriodLattice_finite : Module.Finite ℤ (abelianPeriodLattice X) :=
  Module.Finite.of_basis (abelianLatticeBasis X)

example : Module.Finite ℤ (abelianPeriodLattice X) := inferInstance

/-- The period equivalence `HQ X 1 ≃ₗ[ℚ] (Λ →+ ℚ)` of `spec_abelianPeriod_equiv`. It is determined
by the period map (`x ↦ (l ↦ abelianPeriod X x l)`), so the choice made here is unique.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`H¹(X, ℤ) = Hom(Λ, ℤ)`);
`spec_abelianPeriod_equiv`. -/
def abelianPeriodEquiv : HQ X 1 ≃ₗ[ℚ] (abelianPeriodLattice X →+ ℚ) :=
  Classical.choose (spec_abelianPeriod_equiv X)

example (x : HQ X 1) (l : abelianPeriodLattice X) :
    abelianPeriodEquiv X x l = abelianPeriod X x l :=
  Classical.choose_spec (spec_abelianPeriod_equiv X) x l

/-- The class in `HQ X 2` of an integral form `E` on the S12 period lattice: the stage-7 class
`latticeClass E ∈ ⋀²(Λ →+ ℚ)`, carried to `⋀²(HQ X 1)` by the exterior square of the inverse of
`abelianPeriodEquiv`, then to `HQ X 2` by the canonical cup-wedge map.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.3 and Lemma 1.3.1
(`H²(X, ℤ) = Alt²(Λ, ℤ)`); `latticeClass`, `abelianPeriodEquiv`, `CupProduct.cupWedgeMap`. -/
def latticeClassHQ (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ) : HQ X 2 :=
  (cupProductOf X).cupWedgeMap 2
    (exteriorPower.map 2 (abelianPeriodEquiv X).symm.toLinearMap (latticeClass E))

example (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ) :
    latticeClassHQ X E = (cupProductOf X).cupWedgeMap 2
      (exteriorPower.map 2 (abelianPeriodEquiv X).symm.toLinearMap (latticeClass E)) := rfl

example : latticeClassHQ X 0 = 0 := by simp [latticeClassHQ, latticeClass]

end HodgeLean.Adapters
