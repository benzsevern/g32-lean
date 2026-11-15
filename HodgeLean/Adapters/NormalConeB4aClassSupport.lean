import HodgeLean.Adapters.NormalConeB4aDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.Analytification
import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.ClosedFiltration

/-! # Finite support filtration for analytic cycle classes

This scaffold uses the actual algebraic support of the cycle. Its analytic
filtration starts at the frozen support and ends at the empty set. To obtain
global vanishing one still needs the normal codimension bound and the local
support comparison on every smooth layer.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- The finite union of the algebraic component supports of a cycle.
Source: Fulton, *Intersection Theory*, second edition, §1.5. -/
def a3b4a_classAlgebraicSupport
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact q]
    (γ : AlgebraicCycle Z ℚ) : Closeds Z := by
  haveI := a3b4_compactSpace q
  exact ⟨⋃ ξ ∈ γ.support, closure {ξ},
    (a3b2_support_finite γ).isClosed_biUnion fun _ _ => isClosed_closure⟩

/-- The frozen cycle support is analytically closed, without projectivity. -/
theorem a3b4a_classSupport_isClosed
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact q]
    (γ : AlgebraicCycle Z ℚ) : IsClosed (a3b4_cycleSupport q γ) :=
  (a3b4a_classAlgebraicSupport q γ).isClosed.preimage
    (ComplexPoint.continuous_underlying_to_zariski (Over.mk q))

/-- Analytification of the canonical reduced smooth filtration of a cycle support.
Source: `AlgebraicGeometry.reducedSmoothClosedFiltration`. -/
def a3b4a_classSupportFiltration
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType q] [QuasiCompact q] (γ : AlgebraicCycle Z ℚ) (k : ℕ) :
    Closeds (ComplexPoint (Over.mk q)) :=
  (reducedSmoothClosedFiltration q (a3b4a_classAlgebraicSupport q γ) k).preimage
    (ComplexPoint.continuous_underlying_to_zariski (Over.mk q))

theorem a3b4a_classSupportFiltration_zero
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType q] [QuasiCompact q] (γ : AlgebraicCycle Z ℚ) :
    (a3b4a_classSupportFiltration q γ 0 : Set (ComplexPoint (Over.mk q))) =
      a3b4_cycleSupport q γ := rfl

theorem a3b4a_classSupportFiltration_antitone
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType q] [QuasiCompact q] (γ : AlgebraicCycle Z ℚ) :
    Antitone (a3b4a_classSupportFiltration q γ) := by
  intro i j hij x hx
  exact reducedSmoothClosedFiltration_antitone q (a3b4a_classAlgebraicSupport q γ) hij hx

/-- The analytic filtration has finitely many nonempty layers. -/
theorem a3b4a_classSupportFiltration_eventually_empty
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType q] [QuasiCompact q] (γ : AlgebraicCycle Z ℚ) :
    ∃ N : ℕ, ∀ k, N ≤ k → a3b4a_classSupportFiltration q γ k = ⊥ := by
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian q
  haveI : CompactSpace Z := a3b4_compactSpace q
  haveI : IsNoetherian Z := {}
  let S := a3b4a_classAlgebraicSupport q γ
  let N := (reducedSmoothStratification q S).length
  have hN : a3b4a_classSupportFiltration q γ N = ⊥ := by
    unfold a3b4a_classSupportFiltration
    rw [show reducedSmoothClosedFiltration q S N = ⊥ from
      reducedSmoothClosedFiltration_length q S]
    rfl
  refine ⟨N, fun k hk => le_bot_iff.mp ?_⟩
  rw [← hN]
  exact a3b4a_classSupportFiltration_antitone q γ hk

/-- The lower bound on component codimensions holds throughout the algebraic support. -/
theorem a3b4a_classAlgebraicSupport_coheight
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact q]
    (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ)
    (z : Z) (hz : z ∈ a3b4a_classAlgebraicSupport q γ) :
    (c : ℕ∞) ≤ Order.coheight z := by
  obtain ⟨ξ, hξ, hzξ⟩ := Set.mem_iUnion₂.mp hz
  exact (hc ξ hξ).trans (Order.coheight_anti
    (Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hzξ)))

/-- Removing every component generic point raises the codimension bound by one.
This applies to a singular boundary once its avoidance of those points is known. -/
theorem a3b4a_classAlgebraicSupport_boundary_coheight
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact q]
    (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ)
    (B : Set Z) (hB : B ⊆ a3b4a_classAlgebraicSupport q γ)
    (hgeneric : ∀ ξ ∈ γ.support, ξ ∉ B) (z : Z) (hz : z ∈ B) :
    ((c + 1 : ℕ) : ℕ∞) ≤ Order.coheight z := by
  obtain ⟨ξ, hξ, hzξ⟩ := Set.mem_iUnion₂.mp (hB hz)
  have hle : z ≤ ξ :=
    Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hzξ)
  have hne : z ≠ ξ := fun h => hgeneric ξ hξ (h ▸ hz)
  have hlt : z < ξ := lt_iff_le_not_ge.mpr ⟨hle, fun hge =>
    hne (((Scheme.le_iff_specializes.mp hge).antisymm
      (Scheme.le_iff_specializes.mp hle)).eq)⟩
  calc
    ((c + 1 : ℕ) : ℕ∞) = (c : ℕ∞) + 1 := by norm_cast
    _ ≤ Order.coheight ξ + 1 := by
      simpa only [add_comm] using add_le_add_right (hc ξ hξ) 1
    _ ≤ Order.coheight z := Order.coheight_add_one_le hlt

end HodgeLean.Adapters
