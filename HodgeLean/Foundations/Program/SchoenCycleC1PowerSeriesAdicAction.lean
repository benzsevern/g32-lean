import HodgeLean.Foundations.Program.SchoenCycleC1PowerSeriesAdicExt
import HodgeLean.Foundations.Program.SchoenCycleAdicMapValues
import Mathlib.RingTheory.PowerSeries.Substitution

/-! # Scalar actions under polynomial-adic power series coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- A power series coordinate comparison retaining polynomial values also
intertwines scalar rescaling with the actual induced polynomial adic map. -/
theorem s2e_c1_power_series_adic_scalar_action
    (k : Type*) [CommRing k]
    (E : PowerSeries k ≃ₐ[k]
      AdicCompletion (Ideal.span {(Polynomial.X : Polynomial k)}) (Polynomial k))
    (hE : ∀ p : Polynomial k, E (p : PowerSeries k) = AdicCompletion.of _ _ p)
    (ζ : k)
    (hα : ∀ n : ℕ, ∀ p ∈ (Ideal.span {(Polynomial.X : Polynomial k)}) ^ n,
      Polynomial.aeval (Polynomial.C ζ * Polynomial.X) p ∈
        (Ideal.span {(Polynomial.X : Polynomial k)}) ^ n) :
    (s2e_adic_algebra_map _ _ (Polynomial.aeval (Polynomial.C ζ * Polynomial.X)) hα).comp
      E.toAlgHom = E.toAlgHom.comp (PowerSeries.rescaleAlgHom ζ) := by
  let J : Ideal (Polynomial k) := Ideal.span {Polynomial.X}
  let F := (s2e_adic_algebra_map J J (Polynomial.aeval (Polynomial.C ζ * Polynomial.X)) hα).comp
    E.toAlgHom
  let H := E.toAlgHom.comp (PowerSeries.rescaleAlgHom ζ)
  have hF : F PowerSeries.X = AdicCompletion.of J (Polynomial k) (Polynomial.C ζ * Polynomial.X) := by
    change s2e_adic_algebra_map J J _ hα (E PowerSeries.X) = _
    rw [← Polynomial.coe_X, hE, s2e_adic_algebra_map_of, Polynomial.aeval_X]
  have hr (x : PowerSeries k) : PowerSeries.rescaleAlgHom ζ x = PowerSeries.rescale ζ x := by
    simpa only [RingHom.coe_coe] using DFunLike.congr_fun (PowerSeries.coe_rescaleAlgHom ζ) x
  have hH : H PowerSeries.X = AdicCompletion.of J (Polynomial k) (Polynomial.C ζ * Polynomial.X) := by
    change E (PowerSeries.rescaleAlgHom ζ PowerSeries.X) = _
    rw [hr, PowerSeries.rescale_X, ← Polynomial.coe_C, ← Polynomial.coe_X, ← Polynomial.coe_mul, hE]
  have hx : F PowerSeries.X = H PowerSeries.X := hF.trans hH.symm
  have hmem : F PowerSeries.X ∈ J.map (algebraMap (Polynomial k) (AdicCompletion J (Polynomial k))) := by
    rw [hF]
    apply Ideal.mem_map_of_mem
    exact J.mul_mem_left _ (Ideal.subset_span rfl)
  apply s2e_c1_power_series_adic_algHom_ext J (Submodule.fg_span_singleton _) F H hmem
    (hx ▸ hmem)
  let c : Polynomial k →ₐ[k] PowerSeries k := Polynomial.coeToPowerSeries.algHom k
  have hc (p : Polynomial k) : c p = (p : PowerSeries k) := by
    simp [c]
  have he : F.comp c = H.comp c := by
    apply Polynomial.algHom_ext
    change F (c Polynomial.X) = H (c Polynomial.X)
    rw [hc, Polynomial.coe_X]
    exact hx
  intro p
  have he' := DFunLike.congr_fun he p
  change F (c p) = H (c p) at he'
  rwa [hc] at he'

end HodgeLean.Foundations.Program
