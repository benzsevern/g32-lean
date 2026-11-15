import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSupportNeighborhood
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cChartHomology
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory Topology Filter AlgebraicTopology.Singular
variable (R : Type) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
theorem b6m_absolute_topHomology_point_detection
    {M E : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (α : Homology R (TopCat.of M) n)
    (hα : ∀ x : M, (relativeHomologyProjection R (pointComplementPair x) n).hom α = 0) :
    α = 0 := by
  let P := TopPair.ofSubset (X := TopCat.of M) (Set.univ : Set M)ᶜ
  haveI : IsEmpty P.snd := by
    change IsEmpty ↥((Set.univ : Set M)ᶜ)
    rw [Set.compl_univ]
    infer_instance
  apply (b6m_relativeHomologyProjection_bijective_of_isEmpty R P n).1
  rw [map_zero]
  apply (b6m_compact_manifold_local_homology R hn (A := Set.univ) isCompact_univ).2
  intro x hx
  rw [b6m_relativeHomologyProjection_support]
  exact hα x

set_option backward.isDefEq.respectTransparency false in
theorem b6m_absolute_topHomology_generated_by_point_generators
    {M E : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (w : Homology R (TopCat.of M) n)
    (hw : ∀ x : M, Function.Bijective (fun r : R =>
      r • (relativeHomologyProjection R (pointComplementPair x) n).hom w)) :
    Function.Bijective (fun r : R => r • w) := by
  classical
  constructor
  · intro a b hab
    let x : M := Classical.choice inferInstance
    apply (hw x).1
    simpa only [map_smul] using congrArg
      (relativeHomologyProjection R (pointComplementPair x) n).hom hab
  · intro α
    choose f hf using fun x : M => (hw x).2
      ((relativeHomologyProjection R (pointComplementPair x) n).hom α)
    have hloc : IsLocallyConstant f := by
      apply (IsLocallyConstant.iff_eventually_eq f).2
      intro x
      have hx : (relativeHomologyProjection R (pointComplementPair x) n).hom
          (α - f x • w) = 0 := by
        rw [map_sub, map_smul]
        exact sub_eq_zero.mpr (hf x).symm
      obtain ⟨W, hW, hxW, hzero⟩ := b6m_absoluteClass_vanishes_near_point R n _ x hx
      filter_upwards [hW.mem_nhds hxW] with y hy
      apply (hw y).1
      rw [hf y]
      have hz := hzero y hy
      simpa only [map_sub, map_smul, sub_eq_zero] using hz
    obtain ⟨r, hr⟩ := hloc.exists_eq_const
    refine ⟨r, ?_⟩
    apply sub_eq_zero.mp
    apply b6m_absolute_topHomology_point_detection R hn
    intro x
    rw [map_sub, map_smul]
    have hfx : f x = r := congrFun hr x
    rw [← hfx]
    exact sub_eq_zero.mpr (hf x)

end HodgeLean.Foundations.Program
