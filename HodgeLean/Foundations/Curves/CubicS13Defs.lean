import HodgeLean.Foundations.Curves.CubicGrpObj

/-! # Curves C5: the named group object on the cubic (FROZEN DEFINITIONS)

The group-object instance on `E` chosen from C4's `exists_grpObj` with the C3 comparison and
morphisms. Every datum is chosen from a proved existence statement; nothing is assumed.
Relation to the goal: HC no distance; AV milestone no distance.
-/

namespace HodgeLean.Foundations.Curves

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

/-- The C3 comparison of complex points of `E` with Mathlib's points of `W`, chosen.
Source: C3 S1, `exists_isCubicPointEquiv` (`CubicGroup.lean`). -/
noncomputable def cubicPointEquiv : ComplexPoint E ≃ W.toAffine.Point :=
  exists_isCubicPointEquiv.choose

theorem cubicPointEquiv_isCubicPointEquiv : IsCubicPointEquiv cubicPointEquiv :=
  exists_isCubicPointEquiv.choose_spec

example : IsCubicPointEquiv cubicPointEquiv := cubicPointEquiv_isCubicPointEquiv

/-- The C3 addition morphism on `E`, chosen for `cubicPointEquiv`.
Source: C3 S2, `exists_add_morphism` (`CubicGroup.lean`); Silverman, *The Arithmetic of
Elliptic Curves*, III.3.6. -/
noncomputable def cubicAdd : E ⊗ E ⟶ E :=
  (exists_add_morphism cubicPointEquiv cubicPointEquiv_isCubicPointEquiv).choose

theorem cubicAdd_spec (P Q : ComplexPoint E) :
    lift P Q ≫ cubicAdd = cubicPointEquiv.symm (cubicPointEquiv P + cubicPointEquiv Q) :=
  (exists_add_morphism cubicPointEquiv cubicPointEquiv_isCubicPointEquiv).choose_spec P Q

example (P Q : ComplexPoint E) :
    lift P Q ≫ cubicAdd = cubicPointEquiv.symm (cubicPointEquiv P + cubicPointEquiv Q) :=
  cubicAdd_spec P Q

/-- The C3 negation morphism on `E`, chosen for `cubicPointEquiv`.
Source: C3 S3, `exists_neg_morphism` (`CubicGroup.lean`); Silverman, *The Arithmetic of
Elliptic Curves*, III.2.3. -/
noncomputable def cubicNeg : E ⟶ E :=
  (exists_neg_morphism cubicPointEquiv cubicPointEquiv_isCubicPointEquiv).choose

theorem cubicNeg_spec (P : ComplexPoint E) :
    P ≫ cubicNeg = cubicPointEquiv.symm (-cubicPointEquiv P) :=
  (exists_neg_morphism cubicPointEquiv cubicPointEquiv_isCubicPointEquiv).choose_spec P

example (P : ComplexPoint E) : P ≫ cubicNeg = cubicPointEquiv.symm (-cubicPointEquiv P) :=
  cubicNeg_spec P

/-- **The named group object on `E`**: the one given by C4 T3 for the chosen C3 data, with unit
the infinity section, multiplication `cubicAdd` and inverse `cubicNeg`.
Source: C4 T3, `exists_grpObj` (`CubicGrpObj.lean`); Silverman, *The Arithmetic of Elliptic
Curves*, III.3.6. -/
noncomputable instance cubicGrpObj : GrpObj E :=
  (exists_grpObj cubicPointEquiv cubicPointEquiv_isCubicPointEquiv cubicAdd cubicAdd_spec
    cubicNeg cubicNeg_spec).choose

theorem cubicGrpObj_spec :
    cubicGrpObj.one = Over.homMk infinity infinity_over ∧ cubicGrpObj.mul = cubicAdd ∧
      cubicGrpObj.inv = cubicNeg :=
  (exists_grpObj cubicPointEquiv cubicPointEquiv_isCubicPointEquiv cubicAdd cubicAdd_spec
    cubicNeg cubicNeg_spec).choose_spec

example : μ[E] = cubicAdd := cubicGrpObj_spec.2.1

end HodgeLean.Foundations.Curves
