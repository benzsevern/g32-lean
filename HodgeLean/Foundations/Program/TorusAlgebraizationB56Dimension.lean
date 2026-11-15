import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-! # A differentiable map from `ℂⁿ` has no interior in `ℂᵈ` when `n < d`

If `n < d`, a map `E : ℂⁿ → ℂᵈ` differentiable on `B` factors through the coordinate projection
`π : ℂᵈ → ℂⁿ`, and `E '' B` is the image of the null set `(π⁻¹ B) ∩ (ℂⁿ × 0)` under the map
`E ∘ π`, differentiable there. So `E '' B` is null and contains no nonempty open set.
-/

noncomputable section

open MeasureTheory

namespace HodgeLean.Foundations.Program

/-- A differentiable image of an open subset of `ℂⁿ` containing a nonempty open subset of `ℂᵈ`
forces `d ≤ n`.
Source: Mathlib `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` (Sard's lemma for
null sets); Federer, *Geometric Measure Theory*, 3.2.3. -/
theorem b56_le_of_open_subset_image {n d : ℕ} (E : (Fin n → ℂ) → (Fin d → ℂ))
    (B : Set (Fin n → ℂ)) (hE : DifferentiableOn ℂ E B) (O : Set (Fin d → ℂ)) (hO : IsOpen O)
    (hne : O.Nonempty) (hOB : O ⊆ E '' B) : d ≤ n := by
  by_contra hlt
  push_neg at hlt
  let π : (Fin d → ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi fun j ↦ ContinuousLinearMap.proj (Fin.castLE hlt.le j)
  let K : Submodule ℝ (Fin d → ℂ) :=
    { carrier := {v | ∀ i : Fin d, n ≤ i.val → v i = 0}
      add_mem' := fun ha hb i hi ↦ by simp [ha i hi, hb i hi]
      zero_mem' := fun i _ ↦ rfl
      smul_mem' := fun c v hv i hi ↦ by simp [hv i hi] }
  have hK : K ≠ ⊤ := by
    intro h
    have hmem : (fun i : Fin d ↦ if i.val = n then (1 : ℂ) else 0) ∈ K := h ▸ Submodule.mem_top
    have := hmem ⟨n, hlt⟩ le_rfl
    simp at this
  let μ : Measure (Fin d → ℂ) := Measure.addHaar
  have hK0 : μ (K : Set (Fin d → ℂ)) = 0 := Measure.addHaar_submodule μ K hK
  let S : Set (Fin d → ℂ) := π ⁻¹' B ∩ K
  have hS0 : μ S = 0 := measure_mono_null Set.inter_subset_right hK0
  have hdiff : DifferentiableOn ℝ (E ∘ π) S :=
    DifferentiableOn.comp (DifferentiableOn.restrictScalars ℝ hE)
      (π.restrictScalars ℝ).differentiable.differentiableOn (fun w (hw : w ∈ S) ↦ hw.1)
  have himage : E '' B ⊆ (E ∘ π) '' S := by
    rintro _ ⟨w, hw, rfl⟩
    let v : Fin d → ℂ := fun i ↦ if h : i.val < n then w ⟨i.val, h⟩ else 0
    have hπv : π v = w := by
      funext j
      simp [π, v, j.isLt]
    refine ⟨v, ⟨?_, ?_⟩, ?_⟩
    · change π v ∈ B
      rw [hπv]
      exact hw
    · intro i hi
      simp [v, Nat.not_lt.mpr hi]
    · simp [hπv]
  have hnull : μ ((E ∘ π) '' S) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ hdiff hS0
  have hpos : 0 < μ O := hO.measure_pos μ hne
  exact hpos.ne' (measure_mono_null (hOB.trans himage) hnull)

end HodgeLean.Foundations.Program
