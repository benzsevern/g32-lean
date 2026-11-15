import HodgeLean.Foundations.Program.G32Native.PairedC3NormalizedResidueLift

/-! # Independent evaluations on the actual full differential space -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped Manifold ContDiff Topology BigOperators
namespace HodgeLean.Foundations.Program.G32Native
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Residues at all but the final marked point, as an actual linear map
on the supplied differential space. -/
def pairedC3FullResidueEvaluation (h : Module.finrank ℂ E = 1)
    (n : ℕ) (y : Fin (n + 1) → C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm h q.val) : W →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun i =>
    RiemannRochEichler_residueLinearMap
      ({ toFun := fun q => HurwitzPrymRR_loc h q.val (y i.castSucc)
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } : W →ₗ[ℂ] (ℂ → ℂ)) 0
      (fun q => (hW q).2 (y i.castSucc))

/-- Evaluation at any n of the n+1 marked points is surjective on the
actual normalized full pole space. The remaining residue compensates
their sum, rather than imposing an extra equation on them.
Source: Forster, Lectures on Riemann Surfaces, §18; Schoen, Compositio
Mathematica 65 (1988), Lemma 2.3(i). -/
theorem paired_c3_full_residue_evaluation_surjective (h : Module.finrank ℂ E = 1)
    (n : ℕ) (y : Fin (n + 1) → C) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q, q ∈ W ↔ b4c_IsMeroForm h q ∧
      (∀ p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h q p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc h q p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q ⟨p, u⟩ = 0) :
    Function.Surjective (pairedC3FullResidueEvaluation h n y W
      (fun q => ((hW q.val).mp q.property).1)) := by
  intro a
  let b := Fin.snoc (α := fun _ => ℂ) a (-∑ i, a i)
  have hb : ∑ i, b i = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [b, Fin.snoc_castSucc, Fin.snoc_last, add_neg_cancel]
  obtain ⟨q, hq⟩ := paired_c3_normalized_full_residue_lift h n y hy W hW b hb
  refine ⟨q, ?_⟩
  funext i
  change b4c_res (hE := h) q.val (y i.castSucc) = a i
  exact (hq i.castSucc).trans (Fin.snoc_castSucc _ _ i)

#print axioms pairedC3FullResidueEvaluation
#print axioms paired_c3_full_residue_evaluation_surjective
end HodgeLean.Foundations.Program.G32Native
