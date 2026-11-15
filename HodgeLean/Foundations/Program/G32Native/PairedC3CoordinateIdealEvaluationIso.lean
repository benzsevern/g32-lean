import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateIdealEvaluationGenerator
import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateIdealRegular
import HodgeLean.Foundations.Program.G32Native.PairedC3FrameSectionMaps

/-! # The negative line as the actual coordinate hyperplane ideal -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace HodgeLean.Foundations.Program.G32Native
attribute [local instance] MvPolynomial.gradedAlgebra
open Scheme.Modules HodgeLean.Foundations.Curves.Picard.LineBundles

/-- The original evaluation into the actual coordinate ideal is an
isomorphism on each original affine chart.
Source: Hartshorne, Algebraic Geometry, II.5, the ideal of a hyperplane. -/
theorem paired_c3_coordinate_ideal_evaluation_chart_isIso (k : ℕ) (i j : Fin (k + 1)) :
    IsIso ((Scheme.Modules.pullback (paired_nativeHyperplaneChartOpen k i).1.ι).map
      (pairedC3CoordinateIdealEvaluation k j)) := by
  let U := paired_nativeHyperplaneChartOpen k i
  let I := pairedC3CoordinateHyperplaneIdeal k j
  let M := pairedC3NegativeLine k
  let N := Conormal.idealModule I.subschemeι
  let f : M ⟶ N := pairedC3CoordinateIdealEvaluation k j
  have he : U.1 = ProjSpace.standardOpen ℂ k i := paired_nativeHyperplaneChartOpen_eq k i
  let s : Γ(M, U.1) := M.presheaf.map (homOfLE he.le).op (pairedC3CoordinateDualGenerator k i)
  let t : Γ(N, U.1) := pairedC3CoordinateIdealChartSection k i j
  have hs : IsFrameOn s U.1 :=
    ((paired_c3_coordinate_dual_generator_frame k i).map (homOfLE he.le)).mono he.le
  have hft : f.app U.1 s = t := by
    have hn := PresheafOfModules.naturality_apply f.val (homOfLE he.le).op
      (pairedC3CoordinateDualGenerator k i)
    change f.app U.1 s = N.presheaf.map (homOfLE he.le).op
      (f.app (ProjSpace.standardOpen ℂ k i) (pairedC3CoordinateDualGenerator k i)) at hn
    rw [paired_c3_coordinate_ideal_evaluation_generator] at hn
    refine hn.trans ?_
    change N.presheaf.map (homOfLE he.le).op
      (N.presheaf.map (homOfLE he.ge).op t) = t
    rw [← CategoryTheory.comp_apply, ← N.presheaf.map_comp]
    exact congrArg (fun g => g t) (N.presheaf.map_id _)
  haveI : IsIso (localSectionHom M U.1 s) := paired_c3_local_section_hom_isIso M U.1 s hs
  let eI := idealLocalGeneratorIso I U
    ((paired_nativeHyperplaneChartEquiv k i).symm (ProjSpace.ratio ℂ k i j))
    (paired_c3_coordinate_ideal_generator_regular k i j)
    (paired_c3_coordinate_ideal_principal k i j)
  haveI : IsIso (localSectionHom N U.1 t) := by
    change IsIso eI.inv
    infer_instance
  have hc : localSectionHom M U.1 s ≫ (restrictFunctor U.1.ι).map f =
      localSectionHom N U.1 t := by
    rw [paired_c3_local_section_hom_naturality, hft]
  haveI : IsIso (localSectionHom M U.1 s ≫ (restrictFunctor U.1.ι).map f) := by
    rw [hc]
    infer_instance
  have hf : IsIso ((restrictFunctor U.1.ι).map f) :=
    IsIso.of_isIso_comp_left (localSectionHom M U.1 s) _
  exact (NatIso.isIso_map_iff (restrictFunctorIsoPullback U.1.ι) f).mp hf

/-- The actual negative-line evaluation identifies it with the coordinate
hyperplane ideal globally, retaining its original inclusion arrow.
Source: Hartshorne, Algebraic Geometry, II.5, the hyperplane ideal sheaf. -/
theorem paired_c3_coordinate_ideal_evaluation_isIso (k : ℕ) (j : Fin (k + 1)) :
    IsIso (pairedC3CoordinateIdealEvaluation k j) := by
  apply Scheme.Modules.Hom.isIso_of_forall_exists_isIso_pullback_map
  intro x
  have hx : x ∈ (⨆ i : ULift (Fin (k + 1)), ProjSpace.standardOpen ℂ k i.down) := by
    change x ∈ ⨆ i, (ProjSpace.stdCover ℂ k).U i
    rw [(ProjSpace.stdCover ℂ k).iSup_eq_top]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨(paired_nativeHyperplaneChartOpen k i.down).1, ?_,
    paired_c3_coordinate_ideal_evaluation_chart_isIso k i.down j⟩
  rw [paired_nativeHyperplaneChartOpen_eq]
  exact hi

end HodgeLean.Foundations.Program.G32Native
