import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGraphProjectionHomeomorph

/-! Construction of continuous simplex-affine interpolation from prescribed vertex heights. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_vertex_interpolation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) (a : E → ℝ) :
    ∃ f : E → ℝ, Continuous (fun x : K.space => f x.val) ∧
      (∀ x ∈ K.vertices, f x = a x) ∧
      (∀ s ∈ K.faces, ∀ w : stdSimplex ℝ s,
        f (∑ i, w.val i • i.val) = ∑ i, w.val i * f i.val) := by
  classical
  obtain ⟨L, hL, hfaces⟩ := s2v_hardt6rb_global_prism_complex K hK a a (fun _ _ => le_rfl)
  obtain ⟨e, he⟩ := s2v_hardt6rb_graph_projection_homeomorph K a L hL hfaces
  let f : E → ℝ := fun x => if hx : x ∈ K.space then (e.symm ⟨x, hx⟩).val.2 else 0
  have hfgraph (p : L.space) : f p.val.1 = p.val.2 := by
    have hbase : p.val.1 ∈ K.space := by simpa only [he p] using (e p).property
    have hpe : e p = ⟨p.val.1, hbase⟩ := Subtype.ext (he p)
    have hinv : e.symm ⟨p.val.1, hbase⟩ = p := by rw [← hpe, e.symm_apply_apply]
    simp only [f, dif_pos hbase, hinv]
  have hfeval (x : K.space) : f x.val = (e.symm x).val.2 := by
    have hbase : (e.symm x).val.1 = x.val := by
      simpa only [e.apply_symm_apply] using (he (e.symm x)).symm
    rw [← hbase]
    exact hfgraph (e.symm x)
  have hfcont : Continuous (fun x : K.space => f x.val) := by
    have heq : (fun x : K.space => f x.val) = fun x => (e.symm x).val.2 := funext hfeval
    rw [heq]
    exact continuous_snd.comp (continuous_subtype_val.comp e.symm.continuous)
  have hfvertex (x : E) (hx : x ∈ K.vertices) : f x = a x := by
    have hr : ({(x, a x)} : Finset (E × ℝ)) ∈ L.faces := by
      apply (hfaces _).mpr
      refine ⟨{x}, hx, ⟨x, by simp⟩, ?_, Finset.singleton_nonempty _⟩
      intro p hp
      have hp' : p = (x, a x) := Finset.mem_singleton.mp hp
      subst p
      exact Or.inl ⟨⟨x, by simp⟩, le_rfl, rfl⟩
    have hp : (x, a x) ∈ L.space := L.subset_space hr (by simp)
    exact hfgraph ⟨(x, a x), hp⟩
  refine ⟨f, hfcont, hfvertex, ?_⟩
  intro s hs w
  have hcarrier := s2v_hardt6rb_global_prism_carrier K a a (fun _ _ => le_rfl) L hfaces
  have hp : ((∑ i, w.val i • i.val), ∑ i, w.val i * a i.val) ∈ L.space := by
    rw [hcarrier]
    exact ⟨s, hs, w, rfl, le_rfl, le_rfl⟩
  calc
    f (∑ i, w.val i • i.val) = ∑ i, w.val i * a i.val := hfgraph ⟨_, hp⟩
    _ = ∑ i, w.val i * f i.val := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hfvertex i.val (K.down_closed hs (Finset.singleton_subset_iff.mpr i.property)
        (Finset.singleton_nonempty _))]

end HodgeLean.Foundations.Program
