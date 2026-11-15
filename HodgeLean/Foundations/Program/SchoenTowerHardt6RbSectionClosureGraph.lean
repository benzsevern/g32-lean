import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBandCoordinates
import HodgeLean.Foundations.Program.SchoenTowerHardt2

/-! Actual Boolean graphs of section extensions whose graphs are the original graph closures. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_section_closure_graph {n : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : closure C → ℝ)
    (hgraph : ∀ a : closure C, ∀ t : ℝ,
      (a.val, t) ∈ closure ((fun x => (x, f x)) '' C) ↔ t = g a)
    (G : s2v_t11b_Formula (n + 1))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : C,
      (∀ i, z i.succ = x.val i) ∧ z 0 = f x.val) :
    ∃ H : s2v_t11b_Formula (n + 1), H.realize = closure G.realize ∧
      ∀ z, z ∈ H.realize ↔ ∃ a : closure C,
        (∀ i, z i.succ = a.val i) ∧ z 0 = g a := by
  obtain ⟨e, he0, hes, _, _⟩ := s2v_hardt6rb_band_coordinate_equiv n
  have hGeq : G.realize = e '' ((fun x => (x, f x)) '' C) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, hheight⟩ := (hG z).mp hz
      refine ⟨(x.val, f x.val), ⟨x.val, x.property, rfl⟩, ?_⟩
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (he0 _).trans hheight.symm
      · exact (hes _ j).trans (hx j).symm
    · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
      exact (hG _).mpr ⟨⟨x, hx⟩, hes _, he0 _⟩
  have hbase : closure ((fun x => (x, f x)) '' C) ⊆ Prod.fst ⁻¹' closure C := by
    apply closure_minimal ?_ (isClosed_closure.preimage continuous_fst)
    rintro p ⟨x, hx, rfl⟩
    exact subset_closure hx
  obtain ⟨H, hH, _⟩ := s2v_hardt2_closure_formula G
  have hHeq : H.realize = e '' closure ((fun x => (x, f x)) '' C) := by
    rw [hH, hGeq]
    exact (e.toHomeomorph.image_closure _).symm
  refine ⟨H, hH, ?_⟩
  intro z
  rw [hHeq]
  constructor
  · rintro ⟨p, hp, rfl⟩
    let a : closure C := ⟨p.1, hbase hp⟩
    exact ⟨a, hes p, (he0 p).trans ((hgraph a p.2).mp hp)⟩
  · rintro ⟨a, ha, ht⟩
    refine ⟨(a.val, g a), (hgraph a (g a)).mpr rfl, ?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (he0 _).trans ht.symm
    · exact (hes _ j).trans (ha j).symm

end HodgeLean.Foundations.Program
