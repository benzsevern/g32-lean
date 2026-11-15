import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFiniteConvexCellTriangulation
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbComplexTransport
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPolyhedronFormula

/-! Actual shared convex cell boundaries have Boolean formulas in the prescribed linear coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_convex_cell_boundary_formulas {n : ℕ} {E ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (C : ι → Set E) (D : ι → Finset ι) (rank : ι → ℕ)
    (hD : ∀ i j, j ∈ D i → rank j < rank i)
    (hcompact : ∀ i, IsCompact (C i)) (hconv : ∀ i, Convex ℝ (C i))
    (hne : ∀ i, (C i).Nonempty)
    (hboundary : ∀ i, C i \ intrinsicInterior ℝ (C i) = ⋃ j : D i, C j.val)
    (hsep : ∀ i j, j ≠ i → rank j ≤ rank i → C j ∩ C i ⊆ C i \ intrinsicInterior ℝ (C i)) :
    ∃ F : ι → s2v_t11b_Formula n,
      ∀ i, (F i).realize = e '' (C i \ intrinsicInterior ℝ (C i)) := by
  classical
  obtain ⟨K, _, _, hP⟩ := s2v_hardt6rb_finite_convex_cell_triangulation C D rank hD
    hcompact hconv hne hboundary hsep
  have hR (i : ι) : ∃ R : s2v_t11b_Formula n, R.realize = e '' C i := by
    obtain ⟨P, hPf, hPs, _⟩ := hP i
    obtain ⟨Q, _, hQf, hQs, _⟩ := s2v_hardt6rb_complex_linear_transport P hPf e
    obtain ⟨R, hR⟩ := s2v_hardt6rb_complex_carrier_formula Q hQf
    exact ⟨R, hR.trans (hQs.trans (congrArg (fun S => e '' S) hPs))⟩
  choose R hR using hR
  choose F hF using fun i => s2v_hardt_cad5_finite_union_formula (fun j : D i => R j.val)
  refine ⟨F, ?_⟩
  intro i
  rw [hF, hboundary, Set.image_iUnion]
  exact congrArg (fun Q : D i → Set _ => ⋃ j, Q j) (funext fun j => hR j.val)

end HodgeLean.Foundations.Program
