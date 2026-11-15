import HodgeLean.Foundations.Program.SchoenCycleC2SmoothUniquenessHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ClassPullbackHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2OpenInstances

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Normalized component representatives are unique when the entire component
lies in a smooth ambient scheme neighbourhood. -/
theorem s2e_componentCycle_class_unique_of_smooth_open
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
    (U : W.left.Opens) (hU : Set.range ι.left ⊆ U) (hsm : Smooth (U.ι ≫ W.hom))
    (hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = k)
    (c d : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c)
    (hd : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k d) : c = d := by
  obtain ⟨j, hj, hji, hjc⟩ := s2e_componentCycle_factor_open ι U hU k hcodim
  subst ι
  letI : IsClosedImmersion j.left := hji
  letI : Smooth (ComplexPoint.openScheme W U).hom := hsm
  let i := ComplexPoint.openInclusion W U
  letI : IsOpenImmersion i.left := by
    change IsOpenImmersion U.ι
    infer_instance
  have hf : Topology.IsOpenEmbedding (Point.map i) := ComplexPoint.isOpenEmbedding_map_open W U
  have hcover : a3b4_cycleSupport W.hom (s2e_componentCycle (j ≫ i) ℚ) ⊆
      Set.range (Point.map i) := by
    intro x hx
    have hxU : x ∈ Point.overOpen U :=
      s2e_componentCycle_analytic_support_subset (j ≫ i) U hU hx
    refine ⟨ComplexPoint.asOpenPoint W U x hxU, ?_⟩
    exact congrArg Subtype.val ((ComplexPoint.openEquiv W U).apply_symm_apply ⟨x, hxU⟩)
  have hcharts (r : ℕ)
      (e : OpenPartialHomeomorph (ComplexPoint (ComplexPoint.openScheme W U))
        ((Fin r → ℂ) × (Fin k → ℂ)))
      (he : a3b4_IsHolChart (ComplexPoint.openScheme W U).hom e)
      (z : ComplexPoint (ComplexPoint.openScheme W U)) :
      ∃ E : OpenPartialHomeomorph (ComplexPoint W) ((Fin r → ℂ) × (Fin k → ℂ)),
        a3b4_IsHolChart W.hom E ∧ E.source = Point.map i '' e.source ∧
        ∀ y, E (Point.map i y) = e y := by
    letI : Nonempty (ComplexPoint (ComplexPoint.openScheme W U)) := ⟨z⟩
    exact a3b4a_classHolomorphicChart_openTransport W U r k e he
  let cV := relativeCohomologyMap ℚ (2 * k) (s2e_componentOpenPairMap j i) c
  let dV := relativeCohomologyMap ℚ (2 * k) (s2e_componentOpenPairMap j i) d
  have hcV := s2e_componentCycle_normalized_open_pullback j i hf k hcharts cV c hc rfl
  have hdV := s2e_componentCycle_normalized_open_pullback j i hf k hcharts dV d hd rfl
  have heq : cV = dV := s2e_cycleClass_unique_smooth
    (ComplexPoint.openScheme W U).hom (s2e_componentCycle j ℚ) k
    (fun x hx => by rw [hjc x hx]) cV dV hcV hdV
  exact (s2e_componentOpenPairMap_bijective j i hf hcover k).1 heq

end HodgeLean.Foundations.Program
