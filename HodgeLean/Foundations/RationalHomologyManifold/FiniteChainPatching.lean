import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Union

/-! Finite coefficient patching for subdivided singular chains.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Compatible coefficient families on finitely many patches have a finitely supported extension.
HC no distance; AV milestone no distance.
-/
theorem finite_coefficient_patching {ι α M : Type*} [Fintype ι] [Zero M]
    (z : ι → α →₀ M) (hits : ι → α → Prop)
    (hcompat : ∀ i j a, hits i a → hits j a → z i a = z j a) :
    ∃ w : α →₀ M, ∀ i a, hits i a → w a = z i a := by
  classical
  let s := Finset.univ.biUnion (fun i => (z i).support)
  let f (a : α) : M := if h : ∃ i, hits i a then z (Classical.choose h) a else 0
  have hf (a : α) (ha : f a ≠ 0) : a ∈ s := by
    by_cases h : ∃ i, hits i a
    · have hz : z (Classical.choose h) a ≠ 0 := by
        simpa only [f, dif_pos h] using ha
      exact Finset.mem_biUnion.mpr
        ⟨Classical.choose h, Finset.mem_univ _, Finsupp.mem_support_iff.mpr hz⟩
    · exact False.elim (ha (by simp only [f, dif_neg h]))
  refine ⟨Finsupp.onFinset s f hf, ?_⟩
  intro i a hia
  have ha : ∃ j, hits j a := ⟨i, hia⟩
  change f a = z i a
  simp only [f, dif_pos ha]
  exact hcompat _ i a (Classical.choose_spec ha) hia

#print axioms finite_coefficient_patching
end HodgeLean.Foundations.RationalHomologyManifold
