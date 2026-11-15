import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Defs

/-! Relative openness after excluding the ambient limits of the other parents. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_relative_open_in_union {X : Type*} [TopologicalSpace X]
    {m : ℕ} (C : Fin m → Set X) {S U : Set X} (hcover : (⋃ j, C j) = S)
    (i : Fin m) (hsub : U ⊆ C i) (hopen : IsOpen {x : C i | x.val ∈ U})
    (havoid : ∀ j, j ≠ i → Disjoint U (closure (C j))) :
    IsOpen {x : S | x.val ∈ U} := by
  classical
  obtain ⟨O, hO, he⟩ := isOpen_induced_iff.mp hopen
  let D := ⋃ j : {j : Fin m // j ≠ i}, closure (C j.val)
  have hD : IsClosed D := isClosed_iUnion_of_finite (fun _ => isClosed_closure)
  let W := O \ D
  have hW : IsOpen W := hO.inter hD.isOpen_compl
  have hEq : {x : S | x.val ∈ U} = Subtype.val ⁻¹' W := by
    ext x
    constructor
    · intro hx
      have hxO : x.val ∈ O := by
        have ht : (⟨x.val, hsub hx⟩ : C i) ∈ {x : C i | x.val ∈ U} := hx
        rw [← he] at ht
        exact ht
      refine ⟨hxO, ?_⟩
      intro hxD
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxD
      exact Set.disjoint_left.mp (havoid j.val j.property) hx hj
    · intro hxW
      have hxUnion : x.val ∈ ⋃ j, C j := by simpa only [hcover] using x.property
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxUnion
      by_cases hji : j = i
      · subst j
        have ht : (⟨x.val, hj⟩ : C i) ∈ Subtype.val ⁻¹' O := hxW.1
        rw [he] at ht
        exact ht
      · exact (hxW.2 (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, subset_closure hj⟩)).elim
  rw [hEq]
  exact hW.preimage continuous_subtype_val

end HodgeLean.Foundations.Program
