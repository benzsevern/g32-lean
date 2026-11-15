import HodgeLean.Foundations.Program.G32Native.PointCycleNormalization
import HodgeLean.Foundations.Program.S2P1bc

/-! Smooth-point witnesses for native row T16 with retained initial and final traces. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.QuotientDuality HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.Program.G32Native

/-- A retained normalized trace has a coefficient-one cycle at an actual smooth point. -/
theorem normalized_trace_smooth_point
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (d : ℕ)
    (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d))
    (z : Homology ℚ (TopCat.of (ComplexPoint X)) (2 * d))
    (hz : ∀ x, localOrientation (TopCat.of (ComplexPoint X)) (2 * d) z x = o.generator x)
    (hn : ∀ (x : ComplexPoint X)
      (E : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ)) (hx : x ∈ E.source),
      (∀ j, (f4_analytification X).IsHolFun (fun y : E.source => E y j)) →
      localOrientation (TopCat.of (ComplexPoint X)) (2 * d) z x = localClassOfChart d E x hx) :
    ∃ (U : X.left.Opens) (x : ComplexPoint X),
      Point.underlying x ∈ U ∧ Smooth (U.ι ≫ X.hom) ∧
      ∃ c, a3b4_IsCycleClass X.hom (s2e_componentCycle x ℚ) d c ∧
        orientationIntegral (TopCat.of (ComplexPoint X)) (2 * d) z
          (s2e_classToAbsolute X (s2e_componentCycle x ℚ) d c) = 1 := by
  let U := X.hom.smoothLocus
  let A := openScheme X U
  let j := openInclusion X U
  obtain ⟨a, ha⟩ := X.hom.dense_smoothLocus_of_perfectField.nonempty
  letI : Nonempty U := ⟨⟨a, ha⟩⟩
  letI : Nonempty A.left := inferInstanceAs (Nonempty U)
  letI : LocallyOfFiniteType A.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
  letI : IsIntegral A.left := isIntegral_of_isOpenImmersion U.ι
  letI : Smooth A.hom := X.hom.smooth_restrict_smoothLocus
  letI : IsSeparated A.hom := inferInstanceAs (IsSeparated (U.ι ≫ X.hom))
  letI : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  letI : ConnectedSpace (ComplexPoint A) := ComplexPoint.connectedSpace A
  let y := Classical.choice (inferInstance : Nonempty (ComplexPoint A))
  let x := Point.map j y
  have hx : x.underlying ∈ U := by
    rw [Point.underlying_map]
    exact y.underlying.property
  obtain ⟨c, hc, htrace⟩ := point_cycle_class_trace X d o z hz
    (fun x E hx hh => (hz x).symm.trans (hn x E hx hh)) x
  exact ⟨U, x, hx, X.hom.smooth_restrict_smoothLocus, c, hc, htrace⟩

/-- Native row T16 for the same initial and final orientation integrals retained in T2. -/
theorem selectedTower_native_point_classes
    (W W₀ : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsIntegral W₀.left]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom] [IsSeparated W₀.hom]
    (k : ℕ)
    (or : LocalRationalOrientation (TopCat.of (ComplexPoint W)) (2 * (2 * k)))
    (cr : Homology ℚ (TopCat.of (ComplexPoint W)) (2 * (2 * k)))
    (o₀ : LocalRationalOrientation (TopCat.of (ComplexPoint W₀)) (2 * (2 * k)))
    (c₀ : Homology ℚ (TopCat.of (ComplexPoint W₀)) (2 * (2 * k)))
    (hcr : ∀ x, localOrientation (TopCat.of (ComplexPoint W)) (2 * (2 * k)) cr x = or.generator x)
    (hc₀ : ∀ x, localOrientation (TopCat.of (ComplexPoint W₀)) (2 * (2 * k)) c₀ x = o₀.generator x)
    (hchartr : ∀ (x : ComplexPoint W)
      (E : OpenPartialHomeomorph (ComplexPoint W) (Fin (2 * k) → ℂ)) (hx : x ∈ E.source),
      (∀ j, (f4_analytification W).IsHolFun (fun y : E.source => E y j)) →
      localOrientation (TopCat.of (ComplexPoint W)) (2 * (2 * k)) cr x = localClassOfChart (2 * k) E x hx)
    (hchart₀ : ∀ (x : ComplexPoint W₀)
      (E : OpenPartialHomeomorph (ComplexPoint W₀) (Fin (2 * k) → ℂ)) (hx : x ∈ E.source),
      (∀ j, (f4_analytification W₀).IsHolFun (fun y : E.source => E y j)) →
      localOrientation (TopCat.of (ComplexPoint W₀)) (2 * (2 * k)) c₀ x = localClassOfChart (2 * k) E x hx) :
    let trr := orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (2 * k)) cr
    let tr₀ := orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (2 * k)) c₀
    (∃ (U : W.left.Opens) (x : ComplexPoint W),
      Point.underlying x ∈ U ∧ Smooth (U.ι ≫ W.hom) ∧
      ∃ c, a3b4_IsCycleClass W.hom (s2e_componentCycle x ℚ) (2 * k) c ∧
        trr (s2e_classToAbsolute W (s2e_componentCycle x ℚ) (2 * k) c) = 1) ∧
    (∃ (U : W₀.left.Opens) (x : ComplexPoint W₀),
      Point.underlying x ∈ U ∧ Smooth (U.ι ≫ W₀.hom) ∧
      ∃ c, a3b4_IsCycleClass W₀.hom (s2e_componentCycle x ℚ) (2 * k) c ∧
        tr₀ (s2e_classToAbsolute W₀ (s2e_componentCycle x ℚ) (2 * k) c) = 1) := by
  exact ⟨normalized_trace_smooth_point W (2 * k) or cr hcr hchartr,
    normalized_trace_smooth_point W₀ (2 * k) o₀ c₀ hc₀ hchart₀⟩

#print axioms normalized_trace_smooth_point
#print axioms selectedTower_native_point_classes
end HodgeLean.Foundations.Program.G32Native
