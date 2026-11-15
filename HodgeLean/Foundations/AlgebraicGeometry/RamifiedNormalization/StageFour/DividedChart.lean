import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.EquationHelpers

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

theorem divided_chart_integral_element
    {R A K : Type} [CommRing R] [CommRing A] [Field K]
    (f : R →+* K) (g : R →+* A) (F : A →+* K)
    (hF : F.comp g = f) (m α : ℕ) (hm : 0 < m) (hα : α ≤ m)
    (ε u v : R) (t : K) (hu : f u ≠ 0) (hv : f v ≠ 0)
    (ht : t ^ m = f ε * f u ^ α * f v ^ (m - α))
    (s : A) (hs : g u = s * g v) :
    ∃ w : normalizedChart F,
      (w : K) = dividedGenerator t (f v) ∧
      w ^ m = StageTwo.integralCoeff F (g ε * s ^ α) ∧
      ∀ ev : normalizedChart F →+* ℂ,
        ev w ^ m = ev (StageTwo.integralCoeff F (g ε)) *
          ev (StageTwo.integralCoeff F s) ^ α := by
  have hFg (x : R) : F (g x) = f x := congrArg (fun q : R →+* K => q x) hF
  have hratio : F s = f u / f v := by
    apply (eq_div_iff hv).mpr
    have he := congrArg F hs
    rw [map_mul, hFg, hFg] at he
    exact he.symm
  have heq : dividedGenerator t (f v) ^ m = F (g ε * s ^ α) := by
    rw [map_mul, map_pow, hFg, hratio]
    exact (divided_equations m α hm hα (f ε) t (f u) (f v) hu hv ht).1
  have hint : dividedGenerator t (f v) ∈ normalizedChart F := by
    letI := F.toAlgebra
    change _root_.IsIntegral A _
    apply IsIntegral.of_pow hm
    rw [heq]
    exact isIntegral_algebraMap
  let w : normalizedChart F := ⟨dividedGenerator t (f v), hint⟩
  have hw : w ^ m = StageTwo.integralCoeff F (g ε * s ^ α) := by
    apply Subtype.ext
    exact heq
  refine ⟨w, rfl, hw, ?_⟩
  intro ev
  have he := congrArg ev hw
  simpa only [map_pow, map_mul] using he

end AlgebraicGeometry.RamifiedNormalization.StageFour
