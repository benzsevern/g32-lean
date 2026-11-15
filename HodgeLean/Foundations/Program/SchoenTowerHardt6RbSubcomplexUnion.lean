import HodgeLean.Foundations.Program.SchoenTowerHardt6RbComplexAssembly

/-! Finite unions of actual geometric subcomplexes form the prescribed shared boundary complex. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_subcomplex_union {E ι : Type*} [Finite ι]
    [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (A : ι → Geometry.SimplicialComplex ℝ E) (hAK : ∀ i, (A i).faces ⊆ K.faces) :
    ∃ B : Geometry.SimplicialComplex ℝ E,
      B.faces = ⋃ i, (A i).faces ∧ B.faces.Finite ∧
      B.space = ⋃ i, (A i).space ∧ B.faces ⊆ K.faces := by
  obtain ⟨B, hBf, hB, hBs⟩ := s2v_hardt6rb_assemble_complex A
    (fun i => hK.subset (hAK i))
    (fun i j _ _ hs ht => K.inter_subset_convexHull (hAK i hs) (hAK j ht))
  refine ⟨B, hBf, hB, hBs, ?_⟩
  intro s hs
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hBf ▸ hs)
  exact hAK i hi

end HodgeLean.Foundations.Program
