import HodgeLean.Foundations.Program.MilneExteriorPresentation

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

theorem m2_diagonal_commutes_of_entries {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (r : ℕ) (u : Module.End K V)
    (F : Module.End K (Fin r → V))
    (h : ∀ i j : Fin r, u ∘ₗ (LinearMap.proj i ∘ₗ F ∘ₗ LinearMap.single K (fun _ : Fin r => V) j) =
      (LinearMap.proj i ∘ₗ F ∘ₗ LinearMap.single K (fun _ : Fin r => V) j) ∘ₗ u) :
    m2_diagonalEnd r u ∘ₗ F = F ∘ₗ m2_diagonalEnd r u := by
  classical
  have hs (v : Fin r → V) : (∑ j : Fin r, Pi.single j (v j)) = v := by
    funext i
    simp only [Finset.sum_apply, Pi.single_apply]
    simp
  apply LinearMap.ext
  intro v
  funext i
  change u (F v i) = F (fun j => u (v j)) i
  calc
    _ = ∑ j : Fin r, u (F (Pi.single j (v j)) i) := by
      conv_lhs => rw [← hs v]
      simp only [map_sum, Finset.sum_apply]
    _ = ∑ j : Fin r, F (Pi.single j (u (v j))) i := by
      apply Finset.sum_congr rfl
      intro j _
      exact LinearMap.congr_fun (h i j) (v j)
    _ = _ := by
      rw [← Finset.sum_apply, ← map_sum, hs]


end HodgeLean.Foundations.Program
