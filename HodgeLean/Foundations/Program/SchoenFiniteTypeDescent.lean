import HodgeLean.Foundations.Program.SchoenInvariantFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Artin--Tate descends finite type through a finite affine morphism with
injective pullback on sections over a Noetherian affine base. -/
theorem s2_affine_finiteType_descent {X Y S : Scheme.{0}}
    [IsAffine X] [IsAffine Y] [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (q : X ⟶ Y) [IsFinite q] (g : Y ⟶ S) [LocallyOfFiniteType (q ≫ g)]
    (hq : Function.Injective q.appTop) : LocallyOfFiniteType g := by
  letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (q ≫ g).appTop.hom.toAlgebra
  letI : IsScalarTower Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (by
      exact congrArg CommRingCat.Hom.hom (Scheme.Hom.comp_appTop q g))
  haveI : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) := by
    apply RingHom.finiteType_algebraMap.mp
    exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := q ≫ g)).mp
      inferInstance
  haveI : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) :=
    RingHom.finite_algebraMap.mp q.finite_appTop
  haveI : Algebra.FiniteType Γ(S, ⊤) Γ(Y, ⊤) :=
    ⟨fg_of_fg_of_fg Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤)
      Algebra.FiniteType.out Module.Finite.fg_top hq⟩
  apply (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := g)).mpr
  exact RingHom.finiteType_algebraMap.mpr inferInstance

end HodgeLean.Foundations.Program
