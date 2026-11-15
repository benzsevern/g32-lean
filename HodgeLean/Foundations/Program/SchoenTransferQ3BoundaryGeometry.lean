import HodgeLean.Foundations.Program.SchoenTransferQ3BadLocus
import HodgeLean.Foundations.Program.SchoenTransferQ3CycleCodimension
import HodgeLean.Adapters.NormalConeB4aClassRegularBoundaryCharts
import HodgeLean.Adapters.NormalConeB4aClassRegularBoundaryCodimension

/-! Adjoin the intrinsic bad preimage to the regular cycle boundary. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters AlgebraicGeometry.SingularCycles
open AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Adjoining a closed set which avoids all surviving generic points preserves
the strict boundary codimension bound and the flattening charts. -/
theorem s4_q3_regular_boundary_with_closed_set
    {X : Scheme.{0}} (s : X ⟶ Spec ↧ℂ) [Smooth s] [QuasiCompact s] [IsSeparated s]
    (γ : AlgebraicCycle X ℚ) (k : ℕ)
    (hc : ∀ p ∈ γ.support, (k : ℕ∞) ≤ Order.coheight p)
    (D : Closeds X) (hD : ∀ p ∈ γ.support, p ∉ D) :
    ∃ B : Closeds X,
      B ≤ a3b4a_classAlgebraicSupport s γ ∧
      a3b4a_classAlgebraicSupport s γ ⊓ D ≤ B ∧
      (∀ p ∈ B, ((k + 1 : ℕ) : ℕ∞) ≤ Order.coheight p) ∧
      ∀ x ∈ a3b4_cycleSupport s γ, x.underlying ∉ B →
        ∃ (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint (Over.mk s))
          ((Fin r → ℂ) × (Fin k → ℂ))),
          x ∈ e.source ∧ a3b4_IsHolChart s e ∧
          ∀ y ∈ e.source, y ∈ a3b4_cycleSupport s γ ↔ (e y).2 = 0 := by
  let A := a3b4a_classAlgebraicSupport s γ
  let R := a3b4a_classRegularBoundary s γ k
  let T := A ⊓ D
  let B := R ⊔ T
  have hR : R ≤ A := a3b4a_classRegularBoundary_le s γ k
  have hT : T ≤ A := inf_le_left
  have hTB : T ≤ B := le_sup_right
  have hRB : R ≤ B := le_sup_left
  refine ⟨B, sup_le hR hT, hTB, ?_, ?_⟩
  · intro p hp
    rcases hp with hp | hp
    · exact a3b4a_classRegularBoundary_coheight s γ k hc p hp
    · exact a3b4a_classAlgebraicSupport_boundary_coheight s γ k hc T hT
        (fun p hp hpt => hD p hp hpt.2) p hp
  · intro x hx hxB
    exact a3b4a_classRegularBoundary_charts s γ k hc x hx (fun h => hxB (hRB h))

/-- The actual weighted inverse cycle has a boundary containing the entire
intrinsic bad preimage, with strict coheight gain and injective restriction. -/
theorem s4_q3_weighted_boundary_geometry
    {X W : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    (q : X ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q)) (hq : IsOpenMap q.left)
    (z : AlgebraicCycle W.left ℚ) (k : ℕ)
    (hz : ∀ x ∈ z.support, Order.coheight x = k ∧
      ∃ U : W.left.Opens, x ∈ U ∧ Smooth (U.ι ≫ W.hom)) :
    let γ := ccm3_flatPullback q.left z
    ∃ B : Closeds X.left,
      B ≤ a3b4a_classAlgebraicSupport X.hom γ ∧
      (∀ p ∈ a3b4a_classAlgebraicSupport X.hom γ,
        q.left p ∈ actualBadLocus W.hom q.left → p ∈ B) ∧
      (∀ p ∈ B, ((k + 1 : ℕ) : ℕ∞) ≤ Order.coheight p) ∧
      (∀ p ∈ γ.support, q.left p ∉ actualBadLocus W.hom q.left) ∧
      (∀ x ∈ a3b4_cycleSupport X.hom γ, x.underlying ∉ B →
        ∃ (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X)
          ((Fin r → ℂ) × (Fin k → ℂ))),
          x ∈ e.source ∧ a3b4_IsHolChart X.hom e ∧
          ∀ y ∈ e.source, y ∈ a3b4_cycleSupport X.hom γ ↔ (e y).2 = 0) ∧
      Function.Injective (relativeCohomologyMap ℚ (2 * k)
        (a3b4_neighborhoodPairMap (Point.underlying ⁻¹' (B : Set X.left))ᶜ
          (a3b4_cycleSupport X.hom γ))) := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  let γ := ccm3_flatPullback q.left z
  have hpure := s4_q3_flatPullback_pure_coheight q hq z k (fun x hx => (hz x hx).1)
  have hc : ∀ p ∈ γ.support, (k : ℕ∞) ≤ Order.coheight p :=
    fun p hp => le_of_eq (hpure p hp).symm
  let D : Closeds X.left := ⟨q.left ⁻¹' actualBadLocus W.hom q.left,
    (actualBadLocus_isClosed W.hom q.left).preimage q.left.continuous⟩
  have hgen := s4_q3_surviving_components_avoid_bad q hqsurj hq z
    (fun x hx => (hz x hx).2)
  obtain ⟨B, hBS, hBD, hBc, hcharts⟩ :=
    s4_q3_regular_boundary_with_closed_set X.hom γ k hc D hgen
  exact ⟨B, hBS, fun p hp hbad => hBD ⟨hp, hbad⟩, hBc, hgen, hcharts,
    (a3b4a_classCycle_restriction_bijective_of_boundary_codimension
      X.hom γ k B hBS hBc).1⟩

end HodgeLean.Foundations.Program
