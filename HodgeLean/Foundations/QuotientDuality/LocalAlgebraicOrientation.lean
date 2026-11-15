import HodgeLean.Foundations.QuotientDuality.LocalDeckHomeomorph
import HodgeLean.Foundations.QuotientDuality.LocalHolomorphicOrientation
import HodgeLean.Foundations.QuotientDuality.LocalSmoothLocusCharts
import HodgeLean.Foundations.AnalyticDivisorAlgebraic24Proofs

/-! Algebraic automorphisms preserve complex-normalized local orientations. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem localOrientation_preserved_by_schemeIso
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ) (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d))
    (c : Homology ℚ (TopCat.of (ComplexPoint X)) (2 * d))
    (hc : ∀ x, localOrientation (TopCat.of (ComplexPoint X)) (2 * d) c x = o.generator x)
    (hnorm : ∀ (x : ComplexPoint X)
      (E : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ)) (hx : x ∈ E.source),
      (∀ i, (f4_analytification X).IsHolFun (fun y : E.source => E y i)) →
      o.generator x = localClassOfChart d E x hx)
    (e : X ≅ X) :
    ∀ x, relativeHomologyMap ℚ (2 * d)
      (pointComplementHomeomorphPairMap (Point.isoMapHomeomorph e) x)
      (o.generator x) = o.generator (Point.isoMapHomeomorph e x) := by
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  obtain ⟨z, hz⟩ := X.hom.dense_smoothLocus_of_perfectField.nonempty
  letI : Nonempty X.hom.smoothLocus := ⟨⟨z, hz⟩⟩
  apply localOrientation_preserved_of_dense (TopCat.of (ComplexPoint X)) (2 * d)
    o c hc (Point.isoMapHomeomorph e) (Point.overOpen X.hom.smoothLocus)
    (HodgeLean.Foundations.AnalyticDivisorAlgebraic24.gaga24_dense_overOpen X _)
  intro x hx
  obtain ⟨E, hE, hh⟩ := exists_holomorphic_chart_of_mem_smoothLocus X d o x hx
  exact localOrientation_preserved_at_holomorphic_chart X d o hnorm
    (Point.isoMapHomeomorph e) (f4_map_isHom e.inv) x E hE hh

theorem finite_order_preserves_normalized_orientation
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ) (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d))
    (c : Homology ℚ (TopCat.of (ComplexPoint X)) (2 * d))
    (hc : ∀ x, localOrientation (TopCat.of (ComplexPoint X)) (2 * d) c x = o.generator x)
    (hnorm : ∀ (x : ComplexPoint X)
      (E : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ)) (hx : x ∈ E.source),
      (∀ i, (f4_analytification X).IsHolFun (fun y : E.source => E y i)) →
      o.generator x = localClassOfChart d E x hx)
    (f : X ⟶ X) (m : ℕ) (hm : 0 < m) (hpow : End.of f ^ m = 1) :
    ∃ H : ComplexPoint X ≃ₜ ComplexPoint X,
      (∀ x, H x = Point.map f x) ∧
      ∀ x, relativeHomologyMap ℚ (2 * d) (pointComplementHomeomorphPairMap H x)
        (o.generator x) = o.generator (H x) := by
  letI : IsIso f := (CategoryTheory.isUnit_iff_isIso (End.of f)).mp
    (IsUnit.of_pow_eq_one hpow (Nat.ne_of_gt hm))
  exact ⟨Point.isoMapHomeomorph (asIso f), fun _ => rfl,
    localOrientation_preserved_by_schemeIso X d o c hc hnorm (asIso f)⟩

#print axioms finite_order_preserves_normalized_orientation
#print axioms localOrientation_preserved_by_schemeIso
end HodgeLean.Foundations.QuotientDuality
