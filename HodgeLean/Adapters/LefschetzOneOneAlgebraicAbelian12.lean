import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian12Proofs

/-! # Local concentration and exclusion of critical hypersurface germs

Implications from analyticity and regular-point data, and from reduced analytic germs.
These primitives isolate local concentration and analytic codimension work.
The two full degree-two endpoints require further constructions.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology TopologicalSpace CategoryTheory AlgebraicTopology.Singular
open AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Adapters

/-- A reduced equation's critical zero germ contains no irreducible hypersurface germ.
Source: `bh10_reduced_factor_derivative` and
`AnalyticDivisorAlgebraic18.spec_hypersurface_nullstellensatz`. -/
theorem bh12_no_critical_hypersurface (n : ℕ) (p : Fin n → ℂ)
    (f g : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hred : Squarefree (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p))
    (hi : IsIrreducibleAt g p) :
    ¬ ∀ᶠ z in 𝓝 p, g z = 0 → f z = 0 ∧ fderiv ℂ f z = 0 :=
  bh12_no_critical_hypersurface_aux n p f g hf hg hred hi

/-- Cofinal neighborhoods of regular-domain points have no supported classes below degree two.
Source: `bh10_equation_chart`, punctured complex-line local purity, and
`ccm5_relativeGerms_injective_of_lowerVanishing` for the subsequent detection step. -/
theorem bh12_regular_local_concentration (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (p : Fin n → ℂ)
    (hp : p ∈ bh8_regularDomain n f) (V : Opens (Fin n → ℂ)) (hpV : p ∈ V) :
    ∃ W : Opens (Fin n → ℂ), p ∈ W ∧ W ≤ V ∧
      (W : Set (Fin n → ℂ)) ⊆ bh8_regularDomain n f ∧
      ∀ j : ℕ, j < 2 → Subsingleton (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W : Set (Fin n → ℂ)) {z | f z = 0}) j) :=
  bh12_regular_local_concentration_aux n f hf p hp V hpV

/-- On an open part of the regular domain, degree-two supported classes are detected by germs.
Source: `bh12_regular_local_concentration` and
`ccm5_relativeGerms_injective_of_lowerVanishing`. -/
theorem bh12_regular_germs_injective (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (U : Opens (Fin n → ℂ))
    (hU : (U : Set (Fin n → ℂ)) ⊆ bh8_regularDomain n f) :
    Function.Injective (fun z : RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set (Fin n → ℂ)) {p | f p = 0}) 2 =>
      fun a : U => supportRelativeCohomologyGerm (TopCat.of (Fin n → ℂ))
        {p | f p = 0} 2 U a.1 a.2 z) :=
  bh12_regular_germs_injective_aux n f hf U hU

open HodgeLean.Foundations.AnalyticDivisorAlgebraic18

example : ¬ ∀ᶠ z : Fin 2 → ℂ in 𝓝 0,
    gaga18_axis z = 0 → gaga18_axis z = 0 ∧ fderiv ℂ gaga18_axis z = 0 := by
  have hf := gaga18_concrete_data.1
  have hu : AnalyticAt ℂ gaga18_unit 0 := by
    unfold gaga18_unit
    exact analyticAt_const.add
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticAt 0)
  exact bh12_no_critical_hypersurface 2 0 gaga18_axis gaga18_axis hf hf
    (gaga18_reduced_unit_data hf (hu.mul hf)).1 gaga18_concrete_data.2.1

example : ∃ W : Opens (Fin 1 → ℂ), (0 : Fin 1 → ℂ) ∈ W ∧ W ≤ ⊤ ∧
    (W : Set (Fin 1 → ℂ)) ⊆ bh8_regularDomain 1 (fun z ↦ z 0) ∧
    ∀ j : ℕ, j < 2 → Subsingleton (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (W : Set (Fin 1 → ℂ)) {z | z 0 = 0}) j) := by
  have hd (p : Fin 1 → ℂ) : fderiv ℂ (fun z : Fin 1 → ℂ ↦ z 0) p ≠ 0 := by
    intro h
    have h' := congrArg (fun L : (Fin 1 → ℂ) →L[ℂ] ℂ ↦ L (fun _ ↦ 1)) h
    change ((fderiv ℂ (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 1 ↦ ℂ) 0) p) (fun _ ↦ 1)) = 0 at h'
    rw [ContinuousLinearMap.fderiv] at h'
    exact one_ne_zero h'
  exact bh12_regular_local_concentration 1 (fun z ↦ z 0)
    (fun p _ ↦ (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt p) 0 (Or.inr (hd 0)) ⊤ (mem_univ _)

example : Function.Injective (fun z : RelativeCohomology ℚ
    (neighborhoodSupportComplementPair (univ : Set (Fin 1 → ℂ)) {p | p 0 = 0}) 2 =>
    fun a : (⊤ : Opens (Fin 1 → ℂ)) => supportRelativeCohomologyGerm
      (TopCat.of (Fin 1 → ℂ)) {p | p 0 = 0} 2 ⊤ a.1 a.2 z) := by
  apply bh12_regular_germs_injective 1 (fun z ↦ z 0)
    (fun p _ ↦ (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt p) ⊤
  intro p _
  right
  intro h
  have h' := congrArg (fun L : (Fin 1 → ℂ) →L[ℂ] ℂ ↦ L (fun _ ↦ 1)) h
  change ((fderiv ℂ (ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : Fin 1 ↦ ℂ) 0) p) (fun _ ↦ 1)) = 0 at h'
  rw [ContinuousLinearMap.fderiv] at h'
  exact one_ne_zero h'

end HodgeLean.Adapters
