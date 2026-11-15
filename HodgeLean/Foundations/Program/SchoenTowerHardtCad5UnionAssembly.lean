import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Defs
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5FiniteBooleanFamilies

/-! Finite dependent assembly retaining each source cell and its dimension. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_assemble_disjoint_partitions {n : ℕ} {ι : Type*} [Fintype ι]
    (S : ι → Set (EuclideanSpace ℝ (Fin n)))
    (L : (i : ι) → s2v_hardt_cad5_Partition (S i))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) :
    ∃ U : s2v_t11b_Formula n, ∃ P : s2v_hardt_cad5_Partition U.realize,
    ∃ p : Fin P.count ≃ ((i : ι) × Fin (L i).count),
      (∀ j, P.cell j = (L (p j).1).cell (p j).2) ∧
      (∀ j, P.dim j = (L (p j).1).dim (p j).2) ∧ U.realize = ⋃ i, S i := by
  classical
  let T := (i : ι) × Fin (L i).count
  let enum := (Fintype.equivFin T).symm
  let cell (j : Fin (Fintype.card T)) := (L (enum j).1).cell (enum j).2
  obtain ⟨U, hU⟩ := s2v_hardt_cad5_finite_union_formula cell
  have hdisj : Pairwise (fun a b : T =>
      Disjoint ((L a.1).cell a.2).realize ((L b.1).cell b.2).realize) := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    by_cases hij : i = j
    · subst j
      exact (L i).disjoint (fun h => hab (congrArg (Sigma.mk i) h))
    · apply Set.disjoint_left.mpr
      intro x hxi hxj
      have hi : x ∈ S i := by
        have hu : x ∈ ⋃ l, ((L i).cell l).realize := Set.mem_iUnion.mpr ⟨a, hxi⟩
        simpa only [(L i).cover] using hu
      have hj : x ∈ S j := by
        have hu : x ∈ ⋃ l, ((L j).cell l).realize := Set.mem_iUnion.mpr ⟨b, hxj⟩
        simpa only [(L j).cover] using hu
      exact Set.disjoint_left.mp (hS hij) hi hj
  let P : s2v_hardt_cad5_Partition U.realize :=
    { count := Fintype.card T
      cell := cell
      dim := fun j => (L (enum j).1).dim (enum j).2
      chart := fun j => (L (enum j).1).chart (enum j).2
      forward := fun j => (L (enum j).1).forward (enum j).2
      inverse := fun j => (L (enum j).1).inverse (enum j).2
      nonempty := fun j => (L (enum j).1).nonempty (enum j).2
      disjoint := fun _ _ h => hdisj (fun he => h (enum.injective he))
      cover := hU.symm
      bound := fun j => (L (enum j).1).bound (enum j).2
      forward_eq := fun j => (L (enum j).1).forward_eq (enum j).2
      inverse_eq := fun j => (L (enum j).1).inverse_eq (enum j).2 }
  refine ⟨U, P, enum, fun _ => rfl, fun _ => rfl, ?_⟩
  ext x
  rw [hU]
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨(enum j).1, ?_⟩
    have hu : x ∈ ⋃ l, ((L (enum j).1).cell l).realize :=
      Set.mem_iUnion.mpr ⟨(enum j).2, hj⟩
    simpa only [(L (enum j).1).cover] using hu
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have hu : x ∈ ⋃ l, ((L i).cell l).realize := by
      simpa only [(L i).cover] using hi
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hu
    refine Set.mem_iUnion.mpr ⟨(Fintype.equivFin T) ⟨i, l⟩, ?_⟩
    change x ∈ ((L (enum ((Fintype.equivFin T) ⟨i, l⟩)).1).cell
      (enum ((Fintype.equivFin T) ⟨i, l⟩)).2).realize
    have he : enum ((Fintype.equivFin T) ⟨i, l⟩) = ⟨i, l⟩ :=
      (Fintype.equivFin T).symm_apply_apply ⟨i, l⟩
    rw [he]
    exact hl

end HodgeLean.Foundations.Program
