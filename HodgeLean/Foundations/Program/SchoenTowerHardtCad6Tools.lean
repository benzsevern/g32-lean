import HodgeLean.Foundations.Program.SchoenTowerHardtCad5
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Bounds
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Boolean

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad6_cell_subset {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (P : s2v_hardt_cad5_Partition S) (i : Fin P.count) : (P.cell i).realize ⊆ S := by
  intro x hx
  rw [← P.cover]
  exact Set.mem_iUnion.mpr ⟨i, hx⟩

theorem s2v_hardt_cad6_adapt {n k : ℕ} (S : s2v_t11b_Formula n)
    (B : Fin k → s2v_t11b_Formula n) :
    ∃ P : s2v_hardt_cad5_Partition S.realize,
      ∀ i j, (P.cell i).realize ⊆ (B j).realize ∨
        Disjoint (P.cell i).realize (B j).realize := by
  let marks : Fin (k + 1) → s2v_t11b_Formula n := Fin.cases S B
  obtain ⟨m, c, d, e, F, I, hn, hd, hc, hb, hF, hI, ha⟩ :=
    s2v_hardt_cad4_adapted marks
  let R : s2v_hardt_cad5_Partition (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    { count := m, cell := c, dim := d, chart := e, forward := F, inverse := I
      nonempty := hn, disjoint := hd, cover := hc, bound := hb
      forward_eq := hF, inverse_eq := hI }
  obtain ⟨P, p, _, hp, _, _⟩ := s2v_hardt_cad5_select R (Set.subset_univ _)
    (fun i => ha i 0)
  refine ⟨P, fun i j => ?_⟩
  rw [hp i]
  exact ha (p i) j.succ

theorem s2v_hardt_cad6_no_reverse {X : Type*} [TopologicalSpace X]
    {S C T : Set X} (hC : C ⊆ S) (hT : T ⊆ S \ C)
    (ho : IsOpen {x : S | x.val ∈ C}) : Disjoint C (closure T) := by
  obtain ⟨V, hV, he⟩ := isOpen_induced_iff.mp ho
  apply Set.disjoint_left.mpr
  intro x hx hxt
  have hxV : x ∈ V := by
    have : (⟨x, hC hx⟩ : S) ∈ {x : S | x.val ∈ C} := hx
    rwa [← he] at this
  obtain ⟨y, hyV, hyT⟩ := mem_closure_iff.mp hxt V hV hxV
  have hyC : y ∈ C := by
    have : (⟨y, (hT hyT).1⟩ : S) ∈ Subtype.val ⁻¹' V := hyV
    rwa [he] at this
  exact (hT hyT).2 hyC

end HodgeLean.Foundations.Program
