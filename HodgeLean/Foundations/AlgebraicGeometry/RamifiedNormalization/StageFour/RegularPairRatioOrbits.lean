import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RegularPairEvaluationExt
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RetainedEvaluationOrbits
import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

section
variable {R K L X : Type} [CommRing R] [Algebra ℂ R] [Field K] [Field L]
variable (u v : R)
local notation "A" => RegularPairChart.ring u v

/-- On the original coefficient fibre, equal literal ratios give one orbit under the retained normalization-ring restriction. -/
theorem normalized_regular_pair_ratio_fibre_orbit
    [IsDomain A] [IsIntegrallyClosed A]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (δ : L ≃ₐ[K] L) (hδ : orderOf δ = Module.finrank K L)
    (ρ : integralClosure A L ≃+* integralClosure A L)
    (hρ : ∀ b, (ρ b : L) = δ (b : L))
    (ev : X → (integralClosure A L →+* ℂ)) (hev : Function.Injective ev) (d : X → X)
    (heval : ∀ x b, ev (d x) b = ev x (ρ b))
    (hscalar : ∀ x c, ev x (algebraMap A (integralClosure A L) (algebraMap ℂ A c)) = c)
    (hcoeff : ∀ x y,
      ((ev x).comp (algebraMap A (integralClosure A L))).comp (RegularPairChart.coeff u v) =
      ((ev y).comp (algebraMap A (integralClosure A L))).comp (RegularPairChart.coeff u v)) :
    ∀ x y, ev x (algebraMap A (integralClosure A L) (RegularPairChart.ratio u v)) =
      ev y (algebraMap A (integralClosure A L) (RegularPairChart.ratio u v)) →
      ∃ n : ℕ, d^[n] x = y := by
  have hiter : ∀ n x b, ev (d^[n] x) b = ev x (ρ^[n] b) := by
    intro n
    induction n with
    | zero => intro x b; rfl
    | succ n ih =>
      intro x b
      calc
        ev (d^[n + 1] x) b = ev (d^[n] x) (ρ b) := by
          rw [Function.iterate_succ_apply', heval]
        _ = ev x (ρ^[n] (ρ b)) := ih x (ρ b)
        _ = ev x (ρ^[n + 1] b) := by rw [Function.iterate_succ_apply]
  intro x y hratio
  have hbaseRing : (ev x).comp (algebraMap A (integralClosure A L)) =
      (ev y).comp (algebraMap A (integralClosure A L)) :=
    regular_pair_evaluation_ext u v _ _ (hcoeff x y) hratio
  have hbase (a : A) : ev x (algebraMap A (integralClosure A L) a) =
      ev y (algebraMap A (integralClosure A L) a) :=
    congrArg (fun f : A →+* ℂ => f a) hbaseRing
  obtain ⟨n, hn⟩ := integralClosure_evaluation_retained_orbit δ hδ ρ hρ
    (ev x) (ev y) hbase (hscalar x) (hscalar y)
  refine ⟨n, hev ?_⟩
  apply RingHom.ext
  intro b
  rw [hiter n x b]
  exact hn b

end
end AlgebraicGeometry.RamifiedNormalization.StageFour
