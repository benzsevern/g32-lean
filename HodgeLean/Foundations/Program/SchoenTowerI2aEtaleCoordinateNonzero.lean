import HodgeLean.Foundations.Program.SchoenTowerI2aEtalePairReesChart
import Mathlib.RingTheory.Flat.TorsionFree

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every polynomial coordinate stays nonzero in an integral etale coefficient
algebra over a domain, so both selected actual Rees denominators are available.
Source: Mathlib, `Module.Flat.isTorsionFree` and
`Module.isTorsionFree_iff_faithfulSMul`. -/
theorem s2v_i2a_etale_coordinate_ne_zero
    (A : Type) [CommRing A] [IsDomain A] (n : ℕ) (R : Type) [CommRing R] [IsDomain R]
    [Algebra (MvPolynomial (Fin n) A) R] [Algebra.Etale (MvPolynomial (Fin n) A) R]
    (i : Fin n) : algebraMap (MvPolynomial (Fin n) A) R (MvPolynomial.X i) ≠ 0 := by
  let P := MvPolynomial (Fin n) A
  haveI : FaithfulSMul P R := Module.isTorsionFree_iff_faithfulSMul.mp inferInstance
  intro h
  exact MvPolynomial.X_ne_zero i
    (FaithfulSMul.algebraMap_injective P R (h.trans (map_zero _).symm))

end HodgeLean.Foundations.Program
