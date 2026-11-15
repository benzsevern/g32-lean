import HodgeLean.Foundations.Program.SchoenCycleAdicMapBijective
import HodgeLean.Foundations.Program.SchoenCycleAdicMapValues
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # One variable power series and actual polynomial adic values -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- One variable power series identify with the polynomial coordinate-adic
ring, retaining the values of the specified polynomial coordinate map. -/
theorem s2e_c1_power_series_polynomial_adic_coordinates
    (k : Type*) [CommRing k] :
    ∃ E : PowerSeries k ≃ₐ[k]
        AdicCompletion (Ideal.span {(Polynomial.X : Polynomial k)}) (Polynomial k),
      ∀ p : MvPolynomial Unit k, E (p : MvPowerSeries Unit k) =
        AdicCompletion.of _ _ (MvPolynomial.uniqueAlgEquiv k Unit p) := by
  let I := MvPolynomial.idealOfVars Unit k
  let J : Ideal (Polynomial k) := Ideal.span {Polynomial.X}
  let e := MvPolynomial.uniqueAlgEquiv k Unit
  have hm : I.map e.toRingHom = J := by
    change (Ideal.span (Set.range MvPolynomial.X)).map e.toRingHom = J
    rw [Ideal.map_span, ← Set.range_comp']
    have he : (fun i : Unit => e.toRingHom (MvPolynomial.X i)) = fun _ => Polynomial.X := by
      funext i
      change e (MvPolynomial.X i) = Polynomial.X
      exact MvPolynomial.eval₂_X _ _ _
    rw [he, Set.range_const]
  have hp (n : ℕ) (p : MvPolynomial Unit k) (h : p ∈ I ^ n) : e p ∈ J ^ n := by
    rw [← hm, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ h
  have hj (n : ℕ) : ∃ F : (MvPolynomial Unit k ⧸ I ^ n) ≃ₐ[k] (Polynomial k ⧸ J ^ n),
      ∀ p, F (Ideal.Quotient.mk (I ^ n) p) = Ideal.Quotient.mk (J ^ n) (e p) := by
    have hn : (I ^ n).map e.toRingHom = J ^ n := by rw [Ideal.map_pow, hm]
    exact ⟨Ideal.quotientEquivAlg _ _ e hn.symm, fun _ => rfl⟩
  let F := AlgEquiv.ofBijective (s2e_adic_algebra_map I J e.toAlgHom hp)
    (s2e_adic_algebra_map_bijective I J e.toAlgHom hp hj)
  let E := ((MvPowerSeries.toAdicCompletionAlgEquiv Unit k).restrictScalars k).trans F
  refine ⟨E, ?_⟩
  intro p
  change F (MvPowerSeries.toAdicCompletion Unit k p) = _
  rw [MvPowerSeries.toAdicCompletion_coe]
  exact s2e_adic_algebra_map_of I J e.toAlgHom hp p

end HodgeLean.Foundations.Program
