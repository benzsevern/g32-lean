import HodgeLean.Foundations.Program.SchoenTowerHardtCad5GenericNeighborhoods

/-! Transport of actual polynomial atom coefficients to larger real subfields. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_atom_lifts_mono {n : ℕ} (K L : Subfield ℝ) (hKL : K ≤ L)
    (f : s2v_t11b_Formula n)
    (hlift : ∀ p ∈ f.atoms, ∃ q : MvPolynomial (Fin n) K,
      MvPolynomial.map K.subtype q = p) :
    ∀ p ∈ f.atoms, ∃ q : MvPolynomial (Fin n) L,
      MvPolynomial.map L.subtype q = p := by
  intro p hp
  obtain ⟨q, hq⟩ := hlift p hp
  refine ⟨MvPolynomial.map (Subfield.inclusion hKL) q, ?_⟩
  rw [MvPolynomial.map_map]
  exact hq

end HodgeLean.Foundations.Program
