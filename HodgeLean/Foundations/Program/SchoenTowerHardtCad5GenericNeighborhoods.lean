import HodgeLean.Foundations.Program.SchoenTowerHardtCad5AlgebraicRank
import HodgeLean.Foundations.Program.SchoenTowerT11bBoundary

/-! Local Boolean membership at algebraically independent parameter points. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_generic_mem_interior {n : ℕ} (K : Subfield ℝ)
    (f : s2v_t11b_Formula n)
    (hlift : ∀ p ∈ f.atoms, ∃ q : MvPolynomial (Fin n) K,
      MvPolynomial.map K.subtype q = p)
    (x : EuclideanSpace ℝ (Fin n)) (hxi : AlgebraicIndependent K (fun i => x i))
    (hx : x ∈ f.realize) : x ∈ interior f.realize := by
  by_contra h
  obtain ⟨p, hp, hpn, hpz⟩ := s2v_t11b_boundary_active_atom f x hx h
  obtain ⟨q, hq⟩ := hlift p hp
  have hqa : MvPolynomial.aeval (fun i => x i) q = 0 := by
    change MvPolynomial.eval₂ (algebraMap K ℝ) (fun i => x i) q = 0
    rw [MvPolynomial.eval₂_eq_eval_map]
    change MvPolynomial.eval (fun i => x i) (MvPolynomial.map K.subtype q) = 0
    rw [hq]
    exact hpz
  have hq0 := hxi.eq_zero_of_aeval_eq_zero q hqa
  apply hpn
  rw [← hq, hq0, map_zero]

theorem s2v_hardt_cad5_generic_membership_eventually {n : ℕ} (K : Subfield ℝ)
    (f : s2v_t11b_Formula n)
    (hlift : ∀ p ∈ f.atoms, ∃ q : MvPolynomial (Fin n) K,
      MvPolynomial.map K.subtype q = p)
    (x : EuclideanSpace ℝ (Fin n)) (hxi : AlgebraicIndependent K (fun i => x i)) :
    ∀ᶠ y in nhds x, (y ∈ f.realize ↔ x ∈ f.realize) := by
  by_cases hx : x ∈ f.realize
  · have h := mem_interior_iff_mem_nhds.mp (s2v_hardt_cad5_generic_mem_interior K f hlift x hxi hx)
    filter_upwards [h] with y hy
    exact ⟨fun _ => hx, fun _ => hy⟩
  · have h := mem_interior_iff_mem_nhds.mp
      (s2v_hardt_cad5_generic_mem_interior K (.compl f) hlift x hxi hx)
    filter_upwards [h] with y hy
    exact ⟨fun h => (hy h).elim, fun h => (hx h).elim⟩

end HodgeLean.Foundations.Program
