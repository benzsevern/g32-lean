import HodgeLean.Foundations.Program.G32Native.PairedC3FullResidueEvaluation

/-! # The kernel of full residue evaluation has no poles -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Adapters HodgeLean.Foundations.Program Filter
open TauCeti.Contour
open scoped Manifold ContDiff Topology BigOperators
namespace HodgeLean.Foundations.Program.G32Native
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Vanishing at n of the n+1 allowed residues forces every residue to
vanish; the last residue is constrained by the residue theorem.
Source: Forster, Lectures on Riemann Surfaces, §18, residue theorem. -/
theorem paired_c3_full_residue_kernel_residue_zero
    (h : Module.finrank ℂ E = 1) (n : ℕ) (y : Fin (n + 1) → C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hm : ∀ q : W, b4c_IsMeroForm h q.val)
    (ha : ∀ q : W, ∀ p ∉ Set.range y,
      AnalyticAt ℂ (HurwitzPrymRR_loc h q.val p) 0)
    (v : W) (hv : pairedC3FullResidueEvaluation h n y W hm v = 0) :
    ∀ p, b4c_res (hE := h) v.val p = 0 := by
  classical
  let q : b4c_MeroForm E C h := ⟨v.val, hm v⟩
  have hcast (j : Fin n) : b4c_res (hE := h) q (y j.castSucc) = 0 :=
    congrFun hv j
  have haway : ∀ p, p ≠ y (Fin.last n) → b4c_res (hE := h) q p = 0 := by
    intro p hp
    by_cases hpy : p ∈ Set.range y
    · obtain ⟨i, rfl⟩ := hpy
      revert hp
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro hp
        exact (hp rfl).elim
      · intro _
        exact hcast j
    · exact residue_eq_zero_of_analyticAt (ha v p hpy)
  have hs : Function.support (b4c_res (hE := h) q) ⊆ ({y (Fin.last n)} : Finset C) := by
    intro p hp
    by_contra hnot
    apply hp
    exact haway p (by simpa only [Finset.mem_coe, Finset.mem_singleton] using hnot)
  have hlast := b4c_residue_sum_aux h q
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_singleton] at hlast
  intro p
  by_cases hp : p = y (Fin.last n)
  · exact hp ▸ hlast
  · exact haway p hp

/-- The residue kernel has at most the dimension of holomorphic forms.
Its meromorphic coefficients have no poles and normalization makes their
germs separate its vectors.
Source: Forster, Lectures on Riemann Surfaces, §§18–19. -/
theorem paired_c3_full_residue_kernel_finrank_le
    (h : Module.finrank ℂ E = 1) (n : ℕ) (y : Fin (n + 1) → C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm h q.val ∧
      (∀ p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h q.val p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc h q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0) :
    Module.finrank ℂ (LinearMap.ker (pairedC3FullResidueEvaluation h n y W
      (fun q => (hW q).1))) ≤ Module.finrank ℂ (b3_HolForm E C) := by
  let ev := pairedC3FullResidueEvaluation h n y W (fun q => (hW q).1)
  let F := W.subtype.comp (LinearMap.ker ev).subtype
  apply RiemannRochEichler_no_poles_finrank_le h F
    (fun v => (hW v.val).1)
  · intro v p
    apply ((hW v.val).1.2 p).meromorphicOrderAt_nonneg_iff.mpr
    apply (RiemannRochEichler_simple_pole_removable
      ((hW v.val).1.2 p) ((hW v.val).2.1 p)).mp
    exact paired_c3_full_residue_kernel_residue_zero h n y W
      (fun q => (hW q).1) (fun q => (hW q).2.2.1) v.val v.property p
  · intro v hv
    apply Subtype.ext
    apply Subtype.ext
    exact RiemannRochEichler_regular_zero_of_zero_germs h v.val.val
      (hW v.val).1.1 (Set.range y) (hW v.val).2.2.1 (hW v.val).2.2.2 hv

#print axioms paired_c3_full_residue_kernel_finrank_le
#print axioms paired_c3_full_residue_kernel_residue_zero
end HodgeLean.Foundations.Program.G32Native
