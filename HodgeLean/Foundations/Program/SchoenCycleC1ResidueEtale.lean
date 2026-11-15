import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorEquationOfOrders
import HodgeLean.Foundations.Program.SchoenCycleC1PairedClosureHelpers

/-! # Integral normalization from vanishing prime residues -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Vanishing prime residues of a primitive binomial coefficient give an
etale integral closure over a factorial normal base. -/
theorem s2e_c1_integralClosure_etale_of_zero_residues
    {R K L : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [IsIntegrallyClosed R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [Algebra.IsSeparable K L]
    (P : PowerBasis K L) (m : ℕ) (hm : 0 < m)
    (hdim : Module.finrank K L = m)
    (d : Rˣ) (hd : (d : R) = (m : R))
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hz : P.gen ^ m = algebraMap R L a / algebraMap R L b)
    (hv : ∀ p : R, Prime p → Int.ModEq (m : ℤ)
      (((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ)) 0) :
    Algebra.Etale R (integralClosure R L) := by
  have hρ : Function.Injective (algebraMap R L) :=
    (IsScalarTower.algebraMap_eq R K L) ▸
      (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  obtain ⟨ε, A, B, hA, hB, he⟩ := s2v_l1b_divisor_equation_of_orders
    (algebraMap R L) hρ (fun _ : Fin 0 => (1 : R)) (fun _ => 0)
    (fun _ => one_ne_zero) m hm P.gen a b ha hb hz
    (fun p hp => by simpa only [Fin.sum_univ_zero] using hv p hp)
  simp only [Fin.prod_univ_zero, mul_one] at he
  have hAK : algebraMap R K A ≠ 0 := by simpa only [map_zero] using (IsFractionRing.injective R K).ne hA
  have hBK : algebraMap R K B ≠ 0 := by simpa only [map_zero] using (IsFractionRing.injective R K).ne hB
  have hBL : algebraMap R L B ≠ 0 := by simpa only [map_zero] using hρ.ne hB
  have he' : P.gen ^ m = algebraMap K L
      ((algebraMap R K A / algebraMap R K B) ^ m * algebraMap R K (ε : R)) := by
    rw [map_mul, map_pow, map_div₀,
      ← IsScalarTower.algebraMap_apply R K L,
      ← IsScalarTower.algebraMap_apply R K L,
      ← IsScalarTower.algebraMap_apply R K L, div_pow, div_mul_eq_mul_div]
    apply (eq_div_iff (pow_ne_zero m hBL)).mpr
    calc
      _ = algebraMap R L (ε : R) * algebraMap R L A ^ m := he
      _ = _ := by ring
  obtain ⟨P', _, hmin⟩ := s2e_c1_divided_powerBasis P m hm hdim
    (algebraMap R K A / algebraMap R K B) (algebraMap R K (ε : R))
    (div_ne_zero hAK hBK) he'
  exact s2e_c1_kummer_integralClosure_etale_of_generic_minpoly P' m hm ε d hd hmin

end HodgeLean.Foundations.Program
