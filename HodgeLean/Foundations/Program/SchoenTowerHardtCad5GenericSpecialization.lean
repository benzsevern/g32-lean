import HodgeLean.Foundations.Program.SchoenTowerHardtCad5GenericNeighborhoods
import Mathlib.Algebra.MvPolynomial.Equiv

/-! Nonzero specialization above algebraically independent parameter tuples. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_specialization_map {n : ℕ} (K : Subfield ℝ)
    (q : MvPolynomial (Fin (n + 1)) K) (a : Fin n → ℝ) :
    (MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.map K.subtype q)).map (MvPolynomial.eval a) =
      (MvPolynomial.finSuccEquiv K n q).map (MvPolynomial.aeval (R := K) a).toRingHom := by
  induction q using MvPolynomial.induction_on with
  | C c =>
    simp [MvPolynomial.finSuccEquiv_apply]
    rfl
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, Polynomial.map_mul, Polynomial.map_mul, hp]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]

theorem s2v_hardt_cad5_generic_specialization_ne_zero {n : ℕ} (K : Subfield ℝ)
    (q : MvPolynomial (Fin (n + 1)) K) (hq : q ≠ 0) (a : Fin n → ℝ)
    (ha : AlgebraicIndependent K a) :
    (MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.map K.subtype q)).map (MvPolynomial.eval a) ≠ 0 := by
  rw [s2v_hardt_cad5_specialization_map]
  apply (Polynomial.map_ne_zero_iff (algebraicIndependent_iff_injective_aeval.mp ha)).mpr
  exact (map_ne_zero_iff (MvPolynomial.finSuccEquiv K n)
    (MvPolynomial.finSuccEquiv K n).injective).mpr hq

end HodgeLean.Foundations.Program
