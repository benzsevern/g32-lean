import HodgeLean.Foundations.QuotientDuality.ProperCycleUnionCycle
import HodgeLean.Foundations.QuotientDuality.ProperCycleAlgebraicCodimension
import HodgeLean.Adapters.NormalConeB4aClassRegularLocus

/-! # An actual common algebraic regular boundary for a finite cycle family -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The regular boundary of all family components, restricted to the actual active algebraic support.
Source: Fulton, Intersection Theory, section 19.1, regular component loci and intersections.
HC no distance; AV milestone no distance. -/
def properCycle_family_regular_boundary
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ) (k : ℕ) : Closeds X.left :=
  a3b4a_classRegularBoundary X.hom (properCycle_unsigned_family γ (fun _ => 1)) k ⊓
    a3b4a_classAlgebraicSupport X.hom (properCycle_unsigned_family γ q)

/-- Every point of the actual family boundary has codimension at least one higher than the component bound.
Source: Fulton, Intersection Theory, section 19.1, codimension of singular remainders and intersections.
HC no distance; AV milestone no distance. -/
lemma properCycle_family_regular_boundary_coheight
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ) (k : ℕ)
    (hcodim : ∀ i ξ, ξ ∈ (γ i).support → (k : ℕ∞) ≤ Order.coheight ξ) :
    ∀ z ∈ properCycle_family_regular_boundary X γ q k,
      ((k + 1 : ℕ) : ℕ∞) ≤ Order.coheight z := by
  intro z hz
  exact a3b4a_classRegularBoundary_coheight X.hom
    (properCycle_unsigned_family γ (fun _ => 1)) k
    (properCycle_unsigned_family_coheight γ (fun _ => 1) k hcodim) z hz.1

/-- The actual common family boundary has dimension at most one below the middle cycle dimension.
Source: EGA IV, 5.6.5, dimension formula; Fulton, Intersection Theory, section 19.1.
HC no distance; AV milestone no distance. -/
lemma properCycle_family_regular_boundary_dimension
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2 * k)
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ)
    (hcodim : ∀ i ξ, ξ ∈ (γ i).support → (k : ℕ∞) ≤ Order.coheight ξ) :
    topologicalKrullDim (properCycle_family_regular_boundary X γ q k) ≤ (k - 1 : ℕ) := by
  have h := properCycle_closed_support_dimension_le_of_coheight X
    (properCycle_family_regular_boundary X γ q k) (k + 1)
    (properCycle_family_regular_boundary_coheight X γ q k hcodim)
  rw [hdim, show 2 * k - (k + 1) = k - 1 by omega] at h
  exact h

/-- Outside the actual common boundary, every active support point lies on one intrinsically smooth component isolated from every representative's other components.
Source: Fulton, Intersection Theory, section 19.1, regular component loci and finite intersections.
HC no distance; AV milestone no distance. -/
lemma properCycle_family_regular_boundary_isolation
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ) (k : ℕ)
    (hcodim : ∀ i ξ, ξ ∈ (γ i).support → (k : ℕ∞) ≤ Order.coheight ξ)
    (x : ComplexPoint X)
    (hxT : x ∈ ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i))
    (hxB : x.underlying ∉ properCycle_family_regular_boundary X γ q k) :
    ∃ (i : I) (ξ : X.left), q i ≠ 0 ∧ ξ ∈ (γ i).support ∧
      Order.coheight ξ = k ∧ x.underlying ∈ closure ({ξ} : Set X.left) ∧
      x.underlying ∉ reducedClosedSingularRemainder X.hom ⟨closure {ξ}, isClosed_closure⟩ ∧
      ∀ j η, η ∈ (γ j).support → η ≠ ξ → x.underlying ∉ closure ({η} : Set X.left) := by
  classical
  let δ := properCycle_unsigned_family γ (fun _ => 1)
  have hδ (η : X.left) : η ∈ δ.support ↔ ∃ i, η ∈ (γ i).support := by
    simpa only [ne_eq, one_ne_zero, not_false_eq_true, true_and] using
      properCycle_unsigned_family_support γ (fun _ => 1) η
  have hxact : x.underlying ∈ a3b4a_classAlgebraicSupport X.hom (properCycle_unsigned_family γ q) := by
    change x ∈ a3b4_cycleSupport X.hom (properCycle_unsigned_family γ q)
    rw [properCycle_unsigned_family_analytic_support]
    exact hxT
  have hxδ : x.underlying ∈ a3b4a_classAlgebraicSupport X.hom δ := by
    obtain ⟨i, _, hxi⟩ := Set.mem_iUnion₂.mp hxT
    obtain ⟨η, hη, hxη⟩ := Set.mem_iUnion₂.mp hxi
    exact Set.mem_iUnion₂.mpr ⟨η, (hδ η).mpr ⟨i, hη⟩, hxη⟩
  have hxreg : x.underlying ∉ a3b4a_classRegularBoundary X.hom δ k :=
    fun hh => hxB ⟨hh, hxact⟩
  obtain ⟨ξ, hξ, hcξ, hxξ, hsm, hother⟩ := a3b4a_classRegularBoundary_unique_component
    X.hom δ k (properCycle_unsigned_family_coheight γ (fun _ => 1) k hcodim)
    x.underlying hxδ hxreg
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxT
  obtain ⟨η, hη, hxη⟩ := Set.mem_iUnion₂.mp hxi
  have he : η = ξ := by
    by_contra hn
    exact hother η ((hδ η).mpr ⟨i, hη⟩) hn hxη
  subst η
  exact ⟨i, ξ, hi, hη, hcξ, hxξ, hsm,
    fun j η hη hn => hother η ((hδ η).mpr ⟨j, hη⟩) hn⟩

end HodgeLean.Foundations.QuotientDuality
