import HodgeLean.Foundations.Program.NumeratorJetLeftDefs

/-! # Rational left-eigenvector recursion checks -/

namespace HodgeLean.Foundations.Program
open Matrix

set_option maxHeartbeats 400000 in
/-- The stored left-eigenvector coordinates satisfy the eigenvector recursion. -/
theorem b65e_leftJet_eig : ∀ e : Fin 2, ∀ j : Fin 4, ∀ n : Fin 8, ∀ c : Fin 6,
    b65e_leftEigLhsQ e j n c = b65e_traceQ e * b65e_leftCoordsQ e j n c := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored left-eigenvector coordinates satisfy the normalization. -/
theorem b65e_leftJet_norm : ∀ e : Fin 2, ∀ n : Fin 8, ∀ c : Fin 6,
    ∑ i : Fin 4, b65e_leftCoordsQ e i n c * b65q_uQ e i =
      if n.val = 0 ∧ c = 0 then b65e_traceQ e else 0 := by
  decide +kernel

end HodgeLean.Foundations.Program
