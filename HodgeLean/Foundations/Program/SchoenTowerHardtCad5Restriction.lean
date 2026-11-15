import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Finite

/-! Selection of cells from an adapted finite partition. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_select {n : ℕ}
    {S T : Set (EuclideanSpace ℝ (Fin n))}
    (P : s2v_hardt_cad5_Partition S) (hTS : T ⊆ S)
    (ha : ∀ i, (P.cell i).realize ⊆ T ∨ Disjoint (P.cell i).realize T) :
    ∃ Q : s2v_hardt_cad5_Partition T,
      ∃ parent : Fin Q.count → Fin P.count,
        Function.Injective parent ∧
        (∀ i, Q.cell i = P.cell (parent i)) ∧
        (∀ i, Q.dim i = P.dim (parent i)) ∧ Q.dimension ≤ P.dimension := by
  classical
  let A := {i : Fin P.count // (P.cell i).realize ⊆ T}
  let e := (Fintype.equivFin A).symm
  let p : Fin (Fintype.card A) → Fin P.count := fun i => (e i).val
  have hp : Function.Injective p := Subtype.val_injective.comp e.injective
  have hc : (⋃ i, (P.cell (p i)).realize) = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact (e i).property hi
    · intro hx
      have hxS := hTS hx
      rw [← P.cover] at hxS
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxS
      have hit : (P.cell i).realize ⊆ T := by
        rcases ha i with h | h
        · exact h
        · exact False.elim (Set.disjoint_left.mp h hi hx)
      refine Set.mem_iUnion.mpr ⟨(Fintype.equivFin A) ⟨i, hit⟩, ?_⟩
      simpa [p, e] using hi
  let Q : s2v_hardt_cad5_Partition T :=
    { count := Fintype.card A
      cell := fun i => P.cell (p i)
      dim := fun i => P.dim (p i)
      chart := fun i => P.chart (p i)
      forward := fun i => P.forward (p i)
      inverse := fun i => P.inverse (p i)
      nonempty := fun i => P.nonempty (p i)
      disjoint := fun _ _ h => P.disjoint (fun he => h (hp he))
      cover := hc
      bound := fun i => P.bound (p i)
      forward_eq := fun i => P.forward_eq (p i)
      inverse_eq := fun i => P.inverse_eq (p i) }
  refine ⟨Q, p, hp, fun _ => rfl, fun _ => rfl, ?_⟩
  exact s2v_hardt_cad5_max_le Q.dim P.dimension
    (s2v_hardt_cad5_max_ge_neg_one P.dim)
    (fun i => s2v_hardt_cad5_le_max P.dim (p i))

theorem s2v_hardt_cad5_partition_exists {n : ℕ} (S : s2v_t11b_Formula n) :
    Nonempty (s2v_hardt_cad5_Partition S.realize) := by
  obtain ⟨m, c, d, e, F, I, hn, hd, hc, hb, hF, hI, ha⟩ :=
    s2v_hardt_cad4_adapted (fun _ : Fin 1 => S)
  let P : s2v_hardt_cad5_Partition (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    { count := m, cell := c, dim := d, chart := e, forward := F, inverse := I
      nonempty := hn, disjoint := hd, cover := hc, bound := hb
      forward_eq := hF, inverse_eq := hI }
  obtain ⟨Q, _⟩ := s2v_hardt_cad5_select P (Set.subset_univ S.realize)
    (fun i => ha i 0)
  exact ⟨Q⟩

end HodgeLean.Foundations.Program
