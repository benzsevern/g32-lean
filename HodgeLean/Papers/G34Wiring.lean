import HodgeLean.Papers.G34Assembly
import HodgeLean.Papers.PapersLefschetz
import HodgeLean.Papers.PapersWeilCup

/-! # G34 Theorem B wiring -/

noncomputable section
set_option maxHeartbeats 400000
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]
variable (hComp : ∀
  (W : letI := (finiteBetti_abelian A).finite 1
    HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
  (hW : letI := (finiteBetti_abelian A).finite 1; W.IsWeilType)
  (pol : HQ A 2)
  (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
  (_hRos : letI := (finiteBetti_abelian A).finite 1;
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J)
  (_hPos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
  (_hDim : TopologicalSpace.dim A.left = 6),
  (∀ (X : Over (Spec ↧ℂ)),
    [GrpObj X] → [IsCommMonObj X] → [IsIntegral X.left] →
    [Smooth X.hom] → [IsProjective X.hom] → G34TheoremAStatement X) →
  letI := (finiteBetti_abelian A).finite 1
  WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hW)

include hComp

/-- The general G34 paper conclusion from the named bundle and compensation input. -/
theorem g34w_skelg34_theoremC (B : g34a_premises) :
    type_of% (fun {L : Type*} [Field L] [Algebra ℚ L]
      {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
      [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ} =>
      skelg34_theoremC (A := A) (L := L) (Y := Y) (r := r)
        (hB := g34a_theoremB_of_premises B A hComp)) :=
  fun {_} _ _ {_} _ _ _ _ _ {_} =>
    skelg34_theoremC (A := A) (hB := g34a_theoremB_of_premises B A hComp)

/-- The former statement remains available with its direct Theorem B input. -/
example : type_of% @HodgeLean.Papers.skelg34_theoremC := skelg34_theoremC

/--
info: 'HodgeLean.Papers.g34w_skelg34_theoremC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms g34w_skelg34_theoremC

/-- The Lefschetz-specialized G34 paper conclusion from the bundle and compensation input. -/
theorem g34w_papl_skelg34_theoremC (B : g34a_premises) :
    type_of% (fun {L : Type*} [Field L] [Algebra ℚ L]
      {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
      [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ} =>
      papl_skelg34_theoremC (A := A) (L := L) (Y := Y) (r := r)
        (hB := g34a_theoremB_of_premises B A hComp)) :=
  fun {_} _ _ {_} _ _ _ _ _ {_} =>
    papl_skelg34_theoremC (A := A) (hB := g34a_theoremB_of_premises B A hComp)

/-- The former specialized statement remains available with its direct Theorem B input. -/
example : type_of% @HodgeLean.Papers.papl_skelg34_theoremC := papl_skelg34_theoremC

/--
info: 'HodgeLean.Papers.g34w_papl_skelg34_theoremC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms g34w_papl_skelg34_theoremC

/-- The narrow cup-input G34 paper conclusion from the bundle and compensation input. -/
theorem g34w_papw_skelg34_theoremC (B : g34a_premises) :
    type_of% (fun {L : Type*} [Field L] [Algebra ℚ L]
      {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
      [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ} =>
      papw_skelg34_theoremC (A := A) (L := L) (Y := Y) (r := r)
        (hB := g34a_theoremB_of_premises B A hComp)) :=
  fun {_} _ _ {_} _ _ _ _ _ {_} =>
    papw_skelg34_theoremC (A := A) (hB := g34a_theoremB_of_premises B A hComp)

/-- The former narrow-input statement remains available with its direct Theorem B input. -/
example : type_of% @HodgeLean.Papers.papw_skelg34_theoremC := papw_skelg34_theoremC

/--
info: 'HodgeLean.Papers.g34w_papw_skelg34_theoremC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms g34w_papw_skelg34_theoremC

end HodgeLean.Papers
