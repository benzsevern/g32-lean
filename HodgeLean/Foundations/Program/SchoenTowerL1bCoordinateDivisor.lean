import HodgeLean.Foundations.Program.SchoenTowerL1aInsertionHelpers
import Mathlib.RingTheory.MvPolynomial.Basic

/-! Coordinate divisor ideals used in the earlier blowup charts.
HC no distance; AV milestone no distance.
-/

noncomputable section
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- A polynomial coordinate divisor over a domain has a prime section ideal. -/
theorem s2v_l1b_coordinate_ideal_prime {R σ : Type*} [CommRing R] [IsDomain R]
    [DecidableEq σ] (i : σ) :
    (Ideal.span {X i} : Ideal (MvPolynomial σ R)).IsPrime := by
  rw [← s2v_l1a_coordinate_insertion_kernel i]
  exact RingHom.ker_isPrime _

end HodgeLean.Foundations.Program
