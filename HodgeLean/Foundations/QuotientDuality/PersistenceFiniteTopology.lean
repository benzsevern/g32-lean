import HodgeLean.Foundations.Program.SchoenCycleC11Sub2Proofs
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Topology.LocalAtTarget
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff

/-! Analytic topology of finite covers used by the retained normalization tower. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Topology
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_finite_point_map_proper
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left] :
    IsProperMap (Point.map f) := by
  let U : Y.left.affineOpens → TopologicalSpace.Opens (ComplexPoint Y) :=
    fun V => ⟨Point.overOpen V.1, Point.isOpen_overOpen V.1⟩
  have hU : TopologicalSpace.IsOpenCover U := by
    change (⨆ V, U V) = ⊤
    apply top_unique
    intro y _
    obtain ⟨V, hV, hy, _⟩ :=
      exists_isAffineOpen_mem_and_subset (x := y.underlying) (U := ⊤) trivial
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hy⟩
  have hclosed : IsClosedMap (Point.map f) :=
    hU.isClosedMap_iff_restrictPreimage.mpr (fun V =>
      (s2e_c11_finite_affine_restriction_proper_aux X Y f V.1 V.2).isClosedMap)
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨Point.continuous_map f, hclosed, ?_⟩
  intro y
  have hinj : Function.Injective (Point.underlying (X := X) (R := ℂ)) := by
    intro z w hzw
    apply Over.OverMorphism.ext
    exact ext_of_apply_closedPoint_eq X.hom (Over.w z) (Over.w w) hzw
  apply Set.Finite.isCompact
  apply ((f.left.finite_preimage_singleton y.underlying).preimage hinj.injOn).subset
  intro z hz
  change f.left z.underlying = y.underlying
  exact congrArg Point.underlying hz

lemma persistence_finite_cover_compactSpace
    (X Y : Over (Spec ↧ℂ)) [IsProjective Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] : CompactSpace (ComplexPoint X) := by
  haveI : LocallyOfFiniteType X.hom := by
    rw [← Over.w f]
    infer_instance
  apply isCompact_univ_iff.mp
  simpa only [Set.preimage_univ] using
    (persistence_finite_point_map_proper X Y f).isCompact_preimage
      (isCompact_univ : IsCompact (Set.univ : Set (ComplexPoint Y)))

lemma persistence_finite_cover_t2Space
    (X Y : Over (Spec ↧ℂ)) [hY : IsProjective Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] : T2Space (ComplexPoint X) := by
  apply ComplexPoint.t2Space_of_pair_mem_affineOpen X
  intro z w
  obtain ⟨U, hzU, hwU, hU⟩ := ProjectiveSpace.Presentation.pair_mem_affineOpen
    (Classical.choice hY.nonempty_presentation) (Point.map f z) (Point.map f w)
  refine ⟨f.left ⁻¹ᵁ U, (Point.mem_overOpen_map_iff f z U).mp hzU,
    (Point.mem_overOpen_map_iff f w U).mp hwU, ?_⟩
  exact (show IsAffineOpen U from hU).preimage f.left

end HodgeLean.Foundations.QuotientDuality
