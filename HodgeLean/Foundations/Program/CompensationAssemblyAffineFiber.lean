import HodgeLean.Foundations.Program.CompensationAssemblyFiniteSmoothFiber
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

def cq_algHom_fiber_equiv (R B : Type) [CommRing R] [CommRing B]
    [Algebra ℂ R] [Algebra ℂ B] (f : R →ₐ[ℂ] B) (φ : R →ₐ[ℂ] ℂ) :
    letI : Algebra R B := f.toRingHom.toAlgebra
    letI : Algebra R ℂ := φ.toRingHom.toAlgebra
    (B →ₐ[R] ℂ) ≃ {g : B →ₐ[ℂ] ℂ // g.comp f = φ} := by
  letI : Algebra R B := f.toRingHom.toAlgebra
  letI : Algebra R ℂ := φ.toRingHom.toAlgebra
  exact
    { toFun := fun g => by
        let h : B →ₐ[ℂ] ℂ :=
          { g.toRingHom with
            commutes' := fun c => by
              have ht := g.commutes (algebraMap ℂ R c)
              change g (f (algebraMap ℂ R c)) = φ (algebraMap ℂ R c) at ht
              rw [f.commutes, φ.commutes] at ht
              exact ht }
        exact ⟨h, AlgHom.ext fun r => g.commutes r⟩
      invFun := fun g =>
        { g.1.toRingHom with
          commutes' := fun r => by
            change g.1 (f r) = φ r
            exact DFunLike.congr_fun g.2 r }
      left_inv := fun g => by ext b; rfl
      right_inv := fun g => by apply Subtype.ext; ext b; rfl }

def cq_affineSpec_fiber_equiv (R B : Type) [CommRing R] [CommRing B]
    [Algebra ℂ R] [Algebra ℂ B] (f : R →ₐ[ℂ] B)
    (y : ComplexPoint (Over.mk (affineSpecStructureMap R))) :
    {z : ComplexPoint (Over.mk (affineSpecStructureMap B)) // affineSpecComplexPointMap f z = y} ≃
      {g : B →ₐ[ℂ] ℂ // g.comp f = affineSpecEquiv R y} := by
  apply Equiv.subtypeEquiv (affineSpecEquiv B)
  intro z
  rw [← affineSpecEquiv_affineSpecComplexPointMap f z]
  exact (affineSpecEquiv R).injective.eq_iff.symm

theorem cq_finite_smooth_affine_fiber_degree (R B : Type)
    [CommRing R] [IsDomain R] [CharZero R] [CommRing B] [IsDomain B]
    [Algebra ℂ R] [Algebra ℂ B] (f : R →ₐ[ℂ] B)
    (hfinite : f.toRingHom.Finite) (hsmooth : f.toRingHom.Smooth)
    (hinj : Function.Injective f)
    (y : ComplexPoint (Over.mk (affineSpecStructureMap R))) :
    a1p_degree (Spec.map (CommRingCat.ofHom f.toRingHom))
        (⟨⊥, inferInstance⟩ : Spec (CommRingCat.of B)) =
      Nat.card {z : ComplexPoint (Over.mk (affineSpecStructureMap B)) //
        affineSpecComplexPointMap f z = y} := by
  letI : Algebra R B := f.toRingHom.toAlgebra
  letI : Algebra R ℂ := (affineSpecEquiv R y).toRingHom.toAlgebra
  letI : Module.Finite R B := hfinite
  letI : Algebra.Smooth R B := hsmooth
  change a1p_degree (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (⟨⊥, inferInstance⟩ : Spec (CommRingCat.of B)) = _
  rw [cq_finite_smooth_complex_points_degree R B hinj]
  exact Nat.card_congr ((cq_algHom_fiber_equiv R B f (affineSpecEquiv R y)).trans
    (cq_affineSpec_fiber_equiv R B f y).symm)

end HodgeLean.Foundations.Program
