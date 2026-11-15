import HodgeLean.Foundations.Program.G32Native.AbelNormalizedDisc
import HodgeLean.Foundations.Program.SchoenCycleIndexedLiftProjection
import HodgeLean.Foundations.Program.SchoenCycleCanonicalFamily

/-! # Original curve tuples in indexed collision coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.Adapters
open Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- The original ordered curve tuple parametrized separately in every collision block. -/
def collisionCurveTuple (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom]
    {n b : ℕ} (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (z : (Σ a, Fin (m a)) → ℂ) :
    ComplexPoint (g3_power Z n) :=
  s2_lift n (fun i => b3A_disc (p (ι.symm i).1)
    (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) 1) (z (ι.symm i)))

/-- Every indexed projection of the original collision tuple is the specified curve disc. -/
theorem collisionCurveTuple_projection (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom]
    {n b : ℕ} (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (z : (Σ a, Fin (m a)) → ℂ) (a : Fin b) (i : Fin (m a)) :
    Point.map (g3_proj Z n (ι ⟨a, i⟩)) (collisionCurveTuple Z m ι p z) =
      b3A_disc (p a) (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) 1) (z ⟨a, i⟩) := by
  change s2_lift n _ ≫ g3_proj Z n (ι ⟨a, i⟩) = _
  exact s2e_indexed_cluster_lift_projection m ι
    (fun a i => b3A_disc (p a)
      (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) 1) (z ⟨a, i⟩)) a i

/-- The original collision tuple is continuous at the marked root parameter. -/
theorem collisionCurveTuple_continuousAt (Z : Over (Spec ↧ℂ))
    [IsProjective Z.hom] [SmoothOfRelativeDimension 1 Z.hom]
    {n b : ℕ} (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) : ContinuousAt (collisionCurveTuple Z m ι p) 0 := by
  let L : ((Σ a, Fin (m a)) → ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ι.symm i)
  have hc := s2e_curve_tuple_evaluation_continuousAt Z (g3_power Z n) n (𝟙 _)
    (fun i => p (ι.symm i).1) L
  have hsame : (fun z => Point.map (𝟙 (g3_power Z n)) (s2_lift n (fun i =>
      (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p (ι.symm i).1)).symm
        (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p (ι.symm i).1) (p (ι.symm i).1) +
          b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) (L z i))))) =
      collisionCurveTuple Z m ι p := by
    funext z
    change s2_lift n _ = s2_lift n _
    congr 1
    funext i
    change (chartAt (Fin 1 → ℂ) _).symm (_ + b4cov_lineEquiv _ (z (ι.symm i))) =
      (chartAt (Fin 1 → ℂ) _).symm (_ + z (ι.symm i) • b4cov_lineEquiv _ 1)
    rw [← map_smul, smul_eq_mul, mul_one]
    rfl
  rwa [hsame] at hc

/-- At zero root parameter the tuple is exactly its specified marked tuple. -/
theorem collisionCurveTuple_zero (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom]
    {n b : ℕ} (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (x : ComplexPoint (g3_power Z n))
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a) :
    collisionCurveTuple Z m ι p 0 = x := by
  rw [← s2e_lift_coordinates n x]
  unfold collisionCurveTuple
  congr 1
  funext i
  obtain ⟨⟨a, j⟩, rfl⟩ := ι.surjective i
  simpa only [Equiv.symm_apply_apply, Pi.zero_apply, original_disc_zero, Point.map] using (hx a j).symm

#print axioms collisionCurveTuple_projection
#print axioms collisionCurveTuple_continuousAt
#print axioms collisionCurveTuple_zero
end HodgeLean.Foundations.Program.G32Native
