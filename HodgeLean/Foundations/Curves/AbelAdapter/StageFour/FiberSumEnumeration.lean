import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.RamifiedFibers

noncomputable section
open Set
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §17, sums over unramified fibers. -/
theorem weightedFiber_sum_of_enumeration {S Y A ι : Type*} [AddCommGroup A] [Fintype ι]
    (w : S → ℤ) (f : S → Y) (y : Y) (hy : (f ⁻¹' {y}).Finite)
    (r : ι → S) (hr : Function.Injective r) (hf : f ⁻¹' {y} = range r)
    (hw : ∀ x, f x = y → w x = 1) (a : S → A) :
    weightedSum a (weightedFiber w f y hy) = ∑ i, a (r i) := by
  classical
  change Finsupp.linearCombination ℤ a (weightedFiber w f y hy) = _
  unfold weightedFiber
  rw [Finsupp.linearCombination_onFinset]
  have hs : ∑ x ∈ hy.toFinset, (if f x = y then w x else 0) • a x =
      ∑ x ∈ hy.toFinset, a x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hfx : f x = y := hy.mem_toFinset.mp hx
    simp [hfx, hw x hfx]
  rw [hs]
  symm
  apply Finset.sum_bij (fun i _ ↦ r i)
  · intro i _
    exact hy.mem_toFinset.mpr (hf ▸ mem_range_self i)
  · intro i _ j _ hij
    exact hr hij
  · intro x hx
    have hx' : x ∈ range r := hf ▸ hy.mem_toFinset.mp hx
    obtain ⟨i, rfl⟩ := hx'
    exact ⟨i, Finset.mem_univ i, rfl⟩
  · intro i _
    rfl

/-- Source: Forster, Lectures on Riemann Surfaces, §17, sums over unramified fibers. -/
theorem weightedFiber_sum_of_weighted_enumeration {S Y A ι : Type*} [AddCommGroup A] [Fintype ι]
    (w : S → ℤ) (f : S → Y) (y : Y) (hy : (f ⁻¹' {y}).Finite)
    (r : ι → S) (hr : Function.Injective r) (hf : f ⁻¹' {y} = range r)
    (a : S → A) :
    weightedSum a (weightedFiber w f y hy) = ∑ i, w (r i) • a (r i) := by
  classical
  change Finsupp.linearCombination ℤ a (weightedFiber w f y hy) = _
  unfold weightedFiber
  rw [Finsupp.linearCombination_onFinset]
  have hs : ∑ x ∈ hy.toFinset, (if f x = y then w x else 0) • a x =
      ∑ x ∈ hy.toFinset, w x • a x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hfx : f x = y := hy.mem_toFinset.mp hx
    simp [hfx]
  rw [hs]
  symm
  apply Finset.sum_bij (fun i _ ↦ r i)
  · intro i _
    exact hy.mem_toFinset.mpr (hf ▸ mem_range_self i)
  · intro i _ j _ hij
    exact hr hij
  · intro x hx
    have hx' : x ∈ range r := hf ▸ hy.mem_toFinset.mp hx
    obtain ⟨i, rfl⟩ := hx'
    exact ⟨i, Finset.mem_univ i, rfl⟩
  · intro i _
    rfl


end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
