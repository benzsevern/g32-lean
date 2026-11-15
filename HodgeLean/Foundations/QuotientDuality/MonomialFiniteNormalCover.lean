import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.NormalCover
import Mathlib.RingTheory.FiniteType

/-! A normal finite-type integral cover containing the field generator covers its normalization finitely. -/
noncomputable section
set_option maxHeartbeats 400000
open AlgebraicGeometry.TameMonomialCover.Helpers
namespace HodgeLean.Foundations.QuotientDuality

theorem normal_cover_finite_over_normalization
    {R K A L : Type*} [CommRing R] [Field K] [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field L]
    [Algebra R K] [Algebra R A] [Algebra R L]
    [Algebra.IsIntegral R A] [Algebra.FiniteType R A]
    (v : K) (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (f : K →ₐ[R] L) (σ : A →ₐ[R] L) (hσ : Function.Injective σ)
    (V : A) (hV : σ V = f v) :
    ∃ β : integralClosure R K →ₐ[R] A,
      Function.Injective β ∧ β.toRingHom.Finite ∧ ∀ b, σ (β b) = f (b : K) := by
  let F := FractionRing A
  let σF : F →ₐ[R] L := IsFractionRing.liftAlgHom hσ
  have hσF (a : A) : σF (algebraMap A F a) = σ a :=
    IsFractionRing.lift_algebraMap hσ a
  obtain ⟨fF, hfF⟩ := lift_generated_field v hgen f σF
    ⟨algebraMap A F V, (hσF V).trans hV⟩
  obtain ⟨β, hβ⟩ := integralClosure_lift_to_normal_cover (A := A) fF
  have heval (b : integralClosure R K) : σ (β b) = f (b : K) :=
    (hσF (β b)).symm.trans ((congrArg σF (hβ b)).trans (AlgHom.congr_fun hfF (b : K)))
  have hinj : Function.Injective β := by
    intro a b hab
    apply Subtype.ext
    apply f.injective
    exact (heval a).symm.trans ((congrArg σ hab).trans (heval b))
  have hcomp : β.toRingHom.comp (algebraMap R (integralClosure R K)) = algebraMap R A :=
    β.comp_algebraMap
  have hint : β.toRingHom.IsIntegral :=
    RingHom.IsIntegral.tower_top _ _ (by
      rw [hcomp]
      exact algebraMap_isIntegral_iff.mpr inferInstance)
  have hft : β.toRingHom.FiniteType := RingHom.FiniteType.of_comp_finiteType
    (f := algebraMap R (integralClosure R K)) (by
      rw [hcomp]
      exact RingHom.finiteType_algebraMap.mpr inferInstance)
  exact ⟨β, hinj, hint.to_finite hft, heval⟩

#print axioms normal_cover_finite_over_normalization
end HodgeLean.Foundations.QuotientDuality
