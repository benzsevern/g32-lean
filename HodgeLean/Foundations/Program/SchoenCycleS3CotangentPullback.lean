module

public import HodgeLean.Foundations.Program.SchoenCycleS3AffinePullback
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # The associated cotangent sheaf as an affine pullback -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
universe u
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Extension of scalars of an ideal to its quotient ring is its cotangent module. -/
def s2e_idealExtensionCotangentIso {R : CommRingCat.{u}} (I : Ideal R) :
    (ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I)).obj (ModuleCat.of R I) ≅
      ModuleCat.of (R ⧸ I) I.Cotangent := by
  let e := TensorProduct.quotTensorEquivQuotSMul I I
  let e' : ((R ⧸ I) ⊗[R] I) ≃ₗ[R ⧸ I] I.Cotangent :=
    { __ := e.toEquiv
      map_add' := e.map_add
      map_smul' := fun r x => by
        induction r using Quotient.inductionOn' with
        | h r =>
          change e (r • x) = r • e x
          exact e.map_smul r x }
  exact e'.toModuleIso

/-- Pulling the associated ideal sheaf to its quotient spectrum gives the cotangent sheaf. -/
def s2e_tildeIdealPullbackCotangentIso {R : CommRingCat.{u}} (I : Ideal R) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
        (tilde (ModuleCat.of R I)) ≅
      tilde (ModuleCat.of (CommRingCat.of (R ⧸ I)) I.Cotangent) :=
  (s2e_affinePullbackTildeIso (CommRingCat.ofHom (Ideal.Quotient.mk I))).app
      (ModuleCat.of R I) ≪≫
    (tilde.functor _).mapIso (s2e_idealExtensionCotangentIso I)

end HodgeLean.Foundations.Program
