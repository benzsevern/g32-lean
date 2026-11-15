import HodgeLean.Foundations.Program.SchoenCycleC2SmoothOpenClassHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ClassDescentHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Normalized component classes extend from a containing smooth open to the
original ambient scheme, retaining their actual supported group. -/
theorem s2e_componentCycle_normalized_class_of_smooth_open
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (U : W.left.Opens) (hU : Set.range ι.left ⊆ U)
    (hsm : Smooth (U.ι ≫ W.hom)) (k : ℕ)
    (hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = k) :
    ∃ c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k,
      a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c := by
  obtain ⟨j, hj, hji, cV, hcV⟩ :=
    s2e_componentCycle_normalized_class_on_open ι U hU hsm k hcodim
  letI : IsClosedImmersion j.left := hji
  let i := ComplexPoint.openInclusion W U
  letI : IsOpenImmersion i.left := by
    change IsOpenImmersion U.ι
    infer_instance
  letI : IsClosedImmersion (j ≫ i).left := by
    change IsClosedImmersion (j ≫ ComplexPoint.openInclusion W U).left
    rw [hj]
    infer_instance
  have hf : Topology.IsOpenEmbedding (Point.map i) := ComplexPoint.isOpenEmbedding_map_open W U
  have hcover : a3b4_cycleSupport W.hom (s2e_componentCycle (j ≫ i) ℚ) ⊆
      Set.range (Point.map i) := by
    intro x hx
    have hxι : x ∈ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) := by
      simpa only [i, hj] using hx
    have hxU : x ∈ Point.overOpen U :=
      s2e_componentCycle_analytic_support_subset ι U hU hxι
    refine ⟨ComplexPoint.asOpenPoint W U x hxU, ?_⟩
    exact congrArg Subtype.val ((ComplexPoint.openEquiv W U).apply_symm_apply ⟨x, hxU⟩)
  obtain ⟨cW, hres⟩ := (s2e_componentOpenPairMap_bijective j i hf hcover k).2 cV
  have hcW := s2e_componentCycle_normalized_open_descent j i hf hcover k cV cW hcV hres
  rw [← hj]
  exact ⟨cW, hcW⟩

end HodgeLean.Foundations.Program
