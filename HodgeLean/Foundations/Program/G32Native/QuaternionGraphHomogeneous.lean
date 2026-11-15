import HodgeLean.Foundations.Program.G32Native.QuaternionGraphExpansion

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.QuaternionGraph
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The last graph coefficient is the exterior product of the second frame. -/
theorem graphCoeff_last {n : ℕ} (u v : Fin n → V) :
    graphCoeff (K := K) u v ⟨n, Nat.lt_succ_self n⟩ = exteriorPower.ιMulti K n v := by
  classical
  unfold graphCoeff
  rw [Finset.sum_eq_single (Finset.univ : Finset (Fin n))]
  · simp only [Finset.card_univ, Fintype.card_fin, ite_true, mixedWedge,
      Finset.mem_univ]
  · intro s hs hne
    have hc : s.card ≠ n := by
      intro hc
      exact hne (s.eq_univ_of_card (by simpa using hc))
    simp only [hc, ite_false]
  · simp

/-- Homogeneous combinations of two frames remain in their graph-coefficient span. -/
theorem homogeneousWedge_mem_coeff_span {n : ℕ} (u v : Fin n → V) (a b : K) :
    exteriorPower.ιMulti K n (fun i => a • u i + b • v i) ∈
      Submodule.span K (Set.range (graphCoeff (K := K) u v)) := by
  classical
  by_cases ha : a = 0
  · subst a
    have h := (exteriorPower.ιMulti K n (M := V)).toMultilinearMap.map_smul_univ
      (fun _ => b) v
    simp only [zero_smul, zero_add]
    change (exteriorPower.ιMulti K n).toMultilinearMap (fun i => b • v i) ∈ _
    rw [h]
    apply Submodule.smul_mem
    change exteriorPower.ιMulti K n v ∈ _
    rw [← graphCoeff_last (K := K) u v]
    exact Submodule.subset_span ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩
  · have he : (fun i => a • u i + b • v i) =
        (fun i => a • (u i + (b/a) • v i)) := by
      funext i
      simp only [smul_add, smul_smul]
      congr 1
      congr 1
      field_simp
    rw [he]
    have h := (exteriorPower.ιMulti K n (M := V)).toMultilinearMap.map_smul_univ
      (fun _ => a) (fun i => u i + (b/a) • v i)
    change (exteriorPower.ιMulti K n).toMultilinearMap _ ∈ _
    rw [h]
    apply Submodule.smul_mem
    change graphWedge u v (b/a) ∈ _
    rw [graphWedge_eq_sum_coeff (K := K) u v (b/a)]
    apply Submodule.sum_mem
    intro k hk
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

#print axioms homogeneousWedge_mem_coeff_span
end HodgeLean.Foundations.Program.QuaternionGraph
