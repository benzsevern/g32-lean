import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCommonPolynomialCoordinates
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPolynomialCoordinateHomeomorph
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPolynomialFormulaTransport
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPolynomialMapGraph

/-! Finite Boolean families acquire one actual coordinate change and nondegenerate height polynomials. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_boolean_family_coordinates {n m : ℕ}
    (b : Fin m → s2v_t11b_Formula (n + 1)) :
    ∃ h : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)),
    ∃ B : Fin m → s2v_t11b_Formula (n + 1),
      (∀ j, (B j).realize = h ⁻¹' (b j).realize) ∧
      (∀ j p, p ∈ (B j).atoms → p ≠ 0 →
        IsUnit (MvPolynomial.finSuccEquiv ℝ n p).leadingCoeff) ∧
      ∃ G H : s2v_t11b_Formula ((n + 1) + (n + 1)),
        (∀ z, z ∈ G.realize ↔ ∃ x : EuclideanSpace ℝ (Fin (n + 1)),
          (∀ i, z (Fin.castAdd (n + 1) i) = x i) ∧
          (∀ i, z (Fin.natAdd (n + 1) i) = h x i)) ∧
        (∀ z, z ∈ H.realize ↔ ∃ x : EuclideanSpace ℝ (Fin (n + 1)),
          (∀ i, z (Fin.castAdd (n + 1) i) = x i) ∧
          (∀ i, z (Fin.natAdd (n + 1) i) = h.symm x i)) := by
  classical
  let S := (Finset.univ.biUnion (fun j => (b j).atoms)).filter (fun p => p ≠ 0)
  obtain ⟨T, hT⟩ := s2v_hardt6rb_common_polynomial_coordinates S
    (fun _ hp => (Finset.mem_filter.mp hp).2)
  obtain ⟨h, hh, hi, heval⟩ := s2v_hardt6rb_polynomial_coordinate_homeomorph T
  choose B hB hAtoms using fun j => s2v_hardt6rb_polynomial_formula_transport T h heval (b j)
  obtain ⟨G, hG⟩ := s2v_hardt6rb_polynomial_map_graph _ h hh
  obtain ⟨H, hH⟩ := s2v_hardt6rb_polynomial_map_graph _ h.symm hi
  refine ⟨h, B, hB, ?_, G, H, hG, hH⟩
  intro j p hp hp0
  rw [hAtoms j] at hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  apply hT
  refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hq⟩, ?_⟩
  intro hq0
  exact hp0 (by rw [hq0, map_zero])

end HodgeLean.Foundations.Program
