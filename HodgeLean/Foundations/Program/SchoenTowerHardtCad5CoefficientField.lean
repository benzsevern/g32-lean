import HodgeLean.Foundations.Program.SchoenTowerHardtCad5GenericPoints

/-! One countable real coefficient field for a finite dependent formula family. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_formula_coefficient_field {k : ℕ}
    (n : Fin k → ℕ) (f : (i : Fin k) → s2v_t11b_Formula (n i)) :
    ∃ K : Subfield ℝ, Countable K ∧
      ∀ i p, p ∈ (f i).atoms → ∃ q : MvPolynomial (Fin (n i)) K,
        MvPolynomial.map K.subtype q = p := by
  classical
  let s : Finset ℝ := Finset.univ.biUnion (fun i => (f i).atoms.biUnion fun p => p.coeffs)
  let K : Subfield ℝ := Subfield.closure (s : Set ℝ)
  refine ⟨K, s2v_hardt_cad5_countable_coefficient_field _ s.countable_toSet, ?_⟩
  intro i p hp
  apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
  intro c hc
  have hcs : c ∈ s := Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ i, Finset.mem_biUnion.mpr ⟨p, hp, hc⟩⟩
  exact ⟨⟨c, Subfield.subset_closure hcs⟩, rfl⟩

theorem s2v_hardt_cad5_formula_coefficient_field_fintype {ι : Type*} [Fintype ι]
    (n : ℕ) (f : ι → s2v_t11b_Formula n) :
    ∃ K : Subfield ℝ, Countable K ∧
      ∀ i p, p ∈ (f i).atoms → ∃ q : MvPolynomial (Fin n) K,
        MvPolynomial.map K.subtype q = p := by
  let e := (Fintype.equivFin ι).symm
  obtain ⟨K, hK, hc⟩ := s2v_hardt_cad5_formula_coefficient_field
    (fun _ => n) (fun j => f (e j))
  refine ⟨K, hK, ?_⟩
  intro i
  simpa only [e, Equiv.symm_apply_apply] using hc ((Fintype.equivFin ι) i)

end HodgeLean.Foundations.Program
