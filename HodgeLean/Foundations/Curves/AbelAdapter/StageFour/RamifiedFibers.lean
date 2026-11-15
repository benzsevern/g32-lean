import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.Defs
import HodgeLean.Foundations.Program.RiemannRoch

noncomputable section
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §17, ramified fibers. -/
def weightedFiber {S Y : Type*} (w : S → ℤ) (f : S → Y) (y : Y)
    (hy : (f ⁻¹' {y}).Finite) : S →₀ ℤ := by
  classical
  refine Finsupp.onFinset hy.toFinset (fun x ↦ if f x = y then w x else 0) ?_
  intro x hx
  apply hy.mem_toFinset.mpr
  by_contra h
  exact hx (if_neg h)

theorem weightedFiber_apply {S Y : Type*} [DecidableEq Y] (w : S → ℤ) (f : S → Y) (y : Y)
    (hy : (f ⁻¹' {y}).Finite) (x : S) :
    weightedFiber w f y hy x = if f x = y then w x else 0 := by
  classical
  by_cases h : f x = y <;> simp [weightedFiber, h]


/-- Source: Forster, Lectures on Riemann Surfaces, §17, local multiplicity. -/
def meromorphicMultiplicity {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (f : C → OnePoint ℂ) (x : C) : ℤ :=
  letI := b4cov_sphChartedSpace
  letI := b4cov_sph_isManifold
  (b4_ramIndex E ℂ f x : ℤ)

/-- Source: Forster, Lectures on Riemann Surfaces, §§13, 17. -/
theorem meromorphic_divisor_eq_weightedFibers {E C : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (f : b4c_MeroFun E C)
    (h0 : ((f : C → OnePoint ℂ) ⁻¹' {((0 : ℂ) : OnePoint ℂ)}).Finite)
    (hi : ((f : C → OnePoint ℂ) ⁻¹' {OnePoint.infty}).Finite) :
    b4c_div E f = weightedFiber (meromorphicMultiplicity (E := E) f) f
      ((0 : ℂ) : OnePoint ℂ) h0 -
      weightedFiber (meromorphicMultiplicity (E := E) f) f OnePoint.infty hi := by
  classical
  ext x
  rw [RiemannRochAna_div_apply_of_finite f (b4c_meroFun_orderSupport_finite h f) x,
    Finsupp.sub_apply, weightedFiber_apply, weightedFiber_apply]
  by_cases hz : f x = ((0 : ℂ) : OnePoint ℂ)
  · have hn : f x ≠ OnePoint.infty := by simp [hz]
    simp [b4c_ord, meromorphicMultiplicity, hz, hn]
  · by_cases hn : f x = OnePoint.infty
    · simp [b4c_ord, meromorphicMultiplicity, hz, hn]
    · simp [b4c_ord, meromorphicMultiplicity, hz, hn]



/-- Source: Forster, Lectures on Riemann Surfaces, §13, divisors of constants. -/
theorem meromorphic_divisor_eq_zero_of_constant {E C : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (f : b4c_MeroFun E C) (hf : ∃ x, f x ≠ (0 : ℂ))
    (hc : ∀ x y, f x = f y) : b4c_div E f = 0 := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := f.property.2
  have hord : b4c_ord E f = 0 := by
    funext x
    have hz : f x ≠ (0 : ℂ) := fun hx ↦ ha ((hc a x).trans hx)
    have hi : f x ≠ OnePoint.infty := fun hx ↦ hb ((hc b x).trans hx)
    simp [b4c_ord, hz, hi]
  have hfin : (Function.support (b4c_ord E f)).Finite := by
    rw [hord]
    simp
  ext x
  rw [RiemannRochAna_div_apply_of_finite f hfin x]
  exact congrFun hord x



/-- Source: Forster, Lectures on Riemann Surfaces, §17, ramified fibers of proper maps. -/
def meromorphicFiber {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (f : b4c_MeroFun E C)
    (hnc : ∃ x y, f x ≠ f y) (y : OnePoint ℂ) : C →₀ ℤ := by
  letI := b4cov_sphChartedSpace
  letI := b4cov_sph_isManifold
  exact weightedFiber (meromorphicMultiplicity (E := E) f) f y
    (b4_fiber_finite_aux h (by simp) f f.property.1 hnc y)

/-- Source: Forster, Lectures on Riemann Surfaces, §§13, 17. -/
theorem meromorphic_divisor_eq_fibers {E C : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (f : b4c_MeroFun E C)
    (hnc : ∃ x y, f x ≠ f y) :
    b4c_div E f = meromorphicFiber h f hnc ((0 : ℂ) : OnePoint ℂ) -
      meromorphicFiber h f hnc OnePoint.infty := by
  exact meromorphic_divisor_eq_weightedFibers h f _ _



/-- Source: Forster, Lectures on Riemann Surfaces, §§17, 21, fiber sums. -/
def meromorphicFiberSum {E C A : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] [AddCommGroup A]
    (h : Module.finrank ℂ E = 1) (f : b4c_MeroFun E C)
    (hnc : ∃ x y, f x ≠ f y) (a : C → A) : OnePoint ℂ → A :=
  fun y ↦ weightedSum a (meromorphicFiber h f hnc y)

/-- Source: Forster, Lectures on Riemann Surfaces, §§13, 17, 21. -/
theorem meromorphic_divisor_sum_eq_fiberDifference {E C A : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] [AddCommGroup A]
    (h : Module.finrank ℂ E = 1) (f : b4c_MeroFun E C)
    (hnc : ∃ x y, f x ≠ f y) (a : C → A) :
    weightedSum a (b4c_div E f) =
      meromorphicFiberSum h f hnc a ((0 : ℂ) : OnePoint ℂ) -
      meromorphicFiberSum h f hnc a OnePoint.infty := by
  exact (congrArg (weightedSum a) (meromorphic_divisor_eq_fibers h f hnc)).trans
    ((weightedSum a).map_sub _ _)


end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
