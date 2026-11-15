import HodgeLean.Foundations.BundleThom.RestrictedChartLowHomologyHelpers

/-! # Degree-one relative vanishing on actual saturated chart restrictions

The base open is arbitrary and need not be contractible.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- Restricting a positive-rank chart source over any open base subset preserves degree-one relative homology vanishing.
Source: Hatcher, Algebraic Topology, §2.1, relative product homology; Bott–Tu, §6, restricted bundle charts. -/
theorem i1_chartBaseRestrictionRelativeHomologyOne_isZero
    {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (e : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    [e.IsLinear ℂ] (hk : 0 < k) (S : Set B) (hS : IsOpen S) :
    IsZero (RelativeHomology ℚ
      (i1_subsetRelativePair (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ
        (e.source ∩ TotalSpace.proj ⁻¹' S)) 1) := by
  let r := e.restrOpen S hS
  letI : r.IsLinear ℂ := i1_chartRestrOpen_isLinear k E e S hS
  have h := i1_chartRelativeHomologyOne_isZero k E r hk
  rw [i1_chartPair_eq_actualDomain, i1_chartRestrOpen_source] at h
  exact h

/-- Restricting a positive-rank chart source over any open base subset preserves degree-zero relative homology vanishing.
Source: Hatcher, Algebraic Topology, §2.1, relative product homology; Bott–Tu, §6, restricted bundle charts. -/
theorem i1_chartBaseRestrictionRelativeHomologyZero_isZero
    {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (e : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    [e.IsLinear ℂ] (hk : 0 < k) (S : Set B) (hS : IsOpen S) :
    IsZero (RelativeHomology ℚ
      (i1_subsetRelativePair (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ
        (e.source ∩ TotalSpace.proj ⁻¹' S)) 0) := by
  let r := e.restrOpen S hS
  letI : r.IsLinear ℂ := i1_chartRestrOpen_isLinear k E e S hS
  have h := i1_chartRelativeHomologyZero_isZero k E r hk
  rw [i1_chartPair_eq_actualDomain, i1_chartRestrOpen_source] at h
  exact h


end HodgeLean.Foundations.BundleThom
