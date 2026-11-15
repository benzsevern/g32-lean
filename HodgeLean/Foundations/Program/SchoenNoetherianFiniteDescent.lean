import HodgeLean.Foundations.Program.SchoenFiniteTypeDescent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finiteness descends through an injective section pullback between affine schemes
when the final affine target has a Noetherian section ring. -/
theorem s2_affine_finite_descent {X Y S : Scheme.{0}}
    [IsAffine X] [IsAffine Y] [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (q : X ⟶ Y) (g : Y ⟶ S) [IsFinite (q ≫ g)]
    (hq : Function.Injective q.appTop) : IsFinite g := by
  letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (q ≫ g).appTop.hom.toAlgebra
  letI : IsScalarTower Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (Scheme.Hom.comp_appTop q g))
  haveI : Module.Finite Γ(S, ⊤) Γ(X, ⊤) :=
    RingHom.finite_algebraMap.mp (q ≫ g).finite_appTop
  haveI : Module.Finite Γ(S, ⊤) Γ(Y, ⊤) :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤)).toLinearMap hq
  apply (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mpr
  exact ⟨inferInstance, RingHom.finite_algebraMap.mpr inferInstance⟩

end HodgeLean.Foundations.Program
