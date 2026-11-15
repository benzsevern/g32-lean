import HodgeLean.Foundations.Program.SchoenTowerHardt1Extraction

/-! Finite Boolean partitions into actual connected components. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Component extraction turns a finite preconnected Boolean cover into a disjoint Boolean partition.
Source: Coste, Real Algebraic Sets (2005), Proposition 1.6 and Theorem 1.3, component partition step. -/
theorem s2v_hardt1_boolean_component_partition {n : ℕ} (f : s2v_t11b_Formula n) :
    ∃ m : ℕ, ∃ d : Fin m → s2v_t11b_Formula n,
      (∀ i, IsConnected (d i).realize ∧ (d i).realize ⊆ f.realize) ∧
      (∀ x ∈ f.realize, ∃ i, x ∈ (d i).realize) ∧
      Pairwise (fun i j => Disjoint (d i).realize (d j).realize) := by
  classical
  obtain ⟨k, V, hV, hVcover⟩ := s2v_hardt1_boolean_preconnected_cover n f
  obtain ⟨m, U, hU, hUcover, hdisj, hcomp⟩ := s2v_t11b_formula_finite_component_partition f
  have hform : ∀ i, ∃ d : s2v_t11b_Formula n, d.realize = U i := by
    intro i
    obtain ⟨x, hx⟩ := hcomp i
    obtain ⟨d, hd⟩ := s2v_hardt1_extract_component f V hV hVcover x
    exact ⟨d, hd.trans hx.symm⟩
  choose d hd using hform
  refine ⟨m, d, ?_, ?_, ?_⟩
  · intro i
    rw [hd i]
    exact hU i
  · intro x hx
    obtain ⟨i, hi⟩ := hUcover x hx
    exact ⟨i, (hd i).symm ▸ hi⟩
  · intro i j hij
    rw [hd i, hd j]
    exact hdisj hij

end HodgeLean.Foundations.Program
