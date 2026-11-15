import HodgeLean.Foundations.Program.G32Native.PointCycleSupport
import HodgeLean.Foundations.Program.G32Native.SmoothPointTrace
import HodgeLean.Foundations.Program.SchoenTransferQ3PointCoclassRestriction
import HodgeLean.Foundations.QuotientDuality.LocalTrace
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmert

/-! Native point cycles and the very trace of a specified global orientation. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular AlgebraicGeometry.SingularCycles
open HodgeLean.Adapters HodgeLean.Foundations.QuotientDuality HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.Program.G32Native

/-- The point coclass of a normalized global orientation is a normalized native cycle class. -/
theorem point_cycle_class_trace
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (d : ℕ)
    (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d))
    (z : Homology ℚ (TopCat.of (ComplexPoint X)) (2 * d))
    (hz : ∀ x, localOrientation (TopCat.of (ComplexPoint X)) (2 * d) z x = o.generator x)
    (hn : ∀ (x : ComplexPoint X)
      (F : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ)) (hx : x ∈ F.source),
      (∀ i, (f4_analytification X).IsHolFun (fun y : F.source => F y i)) →
      o.generator x = localClassOfChart d F x hx)
    (x : ComplexPoint X) :
    ∃ c, a3b4_IsCycleClass X.hom (s2e_componentCycle x ℚ) d c ∧
      orientationIntegral (TopCat.of (ComplexPoint X)) (2 * d) z
        (s2e_classToAbsolute X (s2e_componentCycle x ℚ) d c) = 1 := by
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI : T2Space (ComplexPoint (Over.mk X.hom)) := f4_t2Space X
  have hne : o.generator x ≠ 0 := by
    intro h
    have hi := (o.generates x).1
    have he := hi (show LinearMap.toSpanSingleton ℚ _ (o.generator x) (0 : ℚ) =
      LinearMap.toSpanSingleton ℚ _ (o.generator x) (1 : ℚ) by simp [h, LinearMap.toSpanSingleton_apply])
    exact zero_ne_one he
  let v := normalizedRelativeCoclass (o.generator x) hne
  unfold a3b4_IsCycleClass s2e_classToAbsolute s2e_supportedClass
  generalize hs : a3b4_cycleSupport X.hom (s2e_componentCycle x ℚ) = S
  have hsx : S = {x} := hs.symm.trans (point_cycle_support X x)
  clear hs
  subst S
  refine ⟨v, ?_, ?_⟩
  · intro r e hflat y hy hyS he
    have hyx : y = x := Set.mem_singleton_iff.mp hyS
    subst y
    have hr := singleton_chart_tangent_dimension r d e x hy hflat
    subst r
    have he0 : e x = 0 := Prod.ext (Subsingleton.elim _ _)
      ((hflat x hy).mp (Set.mem_singleton x))
    have hhol : ∀ i, (f4_analytification X).IsHolFun
        (fun y : (pointChart e).source => pointChart e y i) := by
      intro i
      exact anrem_isHolFun_restrict (f4_analytification X) (fun y hy => hy.1) (he.2 i)
    have hgen := hn x (pointChart e) ⟨hy, Set.mem_univ _⟩ hhol
    let V := flattenedSupportNeighborhood (Fin 0 → ℂ) d e x hy
    have hVe := flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) d e x hy
    refine ⟨V, hVe, V.isOpen, mem_flattenedSupportNeighborhood (Fin 0 → ℂ) d e x hy, ?_⟩
    rw [point_cycle_multiplicity, one_smul]
    have hv : v = normalizedRelativeCoclass
        (localClassOfChart d (pointChart e) x ⟨hy, Set.mem_univ _⟩)
        (s4_q3_centred_point_class_ne_zero d e x hy he0) := by
      dsimp only [v]
      congr 1
    rw [hv]
    exact s4_q3_point_coclass_restrict_to_normal d e x hy he0
  · apply local_trace_normalization (TopCat.of (ComplexPoint X)) (2 * d) z x v
    rw [hz x]
    simp only [v, relativeCohomologyEquivDualHomology_normalizedRelativeCoclass,
      normalizedDual_apply_self]

#print axioms point_cycle_class_trace
end HodgeLean.Foundations.Program.G32Native
