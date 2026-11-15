import HodgeLean.Foundations.TubularEuler.ZeroRankLocalChartsHelpers

/-! # The actual normal map in transverse rank zero

The map is the given immersion after the original normal projection.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry Topology Bundle
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

variable {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
variable [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
variable (ι : Q ⟶ W) [IsClosedImmersion ι.left]
variable {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
variable (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
variable [SmoothOfRelativeDimension 0 Q.hom]
variable [SmoothOfRelativeDimension 0 (v ≫ W.hom)]
private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin 0 → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j 0

def zeroRankLocalNormalMap : LocalNormalMap ι 0 v j hj := by
  letI : LocallyOfFiniteType Q.hom := by
    rw [← Over.w ι]
    infer_instance
  letI : QuasiCompact Q.hom := by
    rw [← Over.w ι]
    infer_instance
  letI : IsSeparated Q.hom := by
    rw [← Over.w ι]
    infer_instance
  let s := i1_smoothLift ι v j hj
  let I : Over.mk (v ≫ W.hom) ⟶ W := Over.homMk v rfl
  have hsI : s ≫ I = ι := Over.OverMorphism.ext hj
  letI (x : ComplexPoint Q) : Subsingleton (i1_normalFibre j x) :=
    normalFibre_subsingleton_of_rank_zero j (v ≫ W.hom) (Over.w s) x
  let P := zeroRankNormalProjectionHomeomorph j (v ≫ W.hom) (Over.w s)
  let f : TotalSpace (Fin 0 → ℂ) (i1_normalFibre j) → ComplexPoint W :=
    fun z => Point.map ι z.proj
  have hf : IsOpenEmbedding f :=
    (zeroRankImmersion_points_isOpenEmbedding ι v j hj).comp P.isOpenEmbedding
  let L (x : ComplexPoint Q) :=
    letI : Nonempty (TotalSpace (Fin 0 → ℂ) (i1_normalFibre j)) :=
      ⟨zeroSection (Fin 0 → ℂ) (i1_normalFibre j) x⟩
    hf.toOpenPartialHomeomorph f
  have hL (x : ComplexPoint Q) (z : TotalSpace (Fin 0 → ℂ) (i1_normalFibre j)) :
      L x z = f z := by
    letI : Nonempty (TotalSpace (Fin 0 → ℂ) (i1_normalFibre j)) :=
      ⟨zeroSection (Fin 0 → ℂ) (i1_normalFibre j) x⟩
    exact congrFun (hf.toOpenPartialHomeomorph_apply f) z
  have hLs (x : ComplexPoint Q) : (L x).source = Set.univ := by
    letI : Nonempty (TotalSpace (Fin 0 → ℂ) (i1_normalFibre j)) :=
      ⟨zeroSection (Fin 0 → ℂ) (i1_normalFibre j) x⟩
    exact hf.toOpenPartialHomeomorph_source f
  refine {
    domain := ⊤
    map := ⟨fun z => Point.map s z.val.proj,
      (Point.continuous_map s).comp ((i1_normalProjection_continuous j 0).comp
        continuous_subtype_val)⟩
    contains_zero := fun _ => Set.mem_univ _
    map_zero := fun _ _ => rfl
    localInverse := L
    local_zero := ?_
    local_domain := fun _ _ _ => Set.mem_univ _
    local_map := ?_
    local_support := ?_
    localCharts := ?_ }
  · intro x
    rw [hLs x]
    exact Set.mem_univ _
  · intro x z hz
    rw [hL x z]
    change Point.map ι z.proj = Point.map I (Point.map s z.proj)
    rw [← Point.map_comp_apply, hsI]
  · intro x z hz
    rw [hL x z]
    have hsupp : Point.map ι z.proj ∈ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) := by
      rw [s2e_componentCycle_analytic_support]
      exact ⟨z.proj.underlying, rfl⟩
    exact iff_of_true hsupp (Subsingleton.elim _ _)
  · intro x z hz
    exact zeroRankLocalCharts ι v j hj (L x) (fun y _ => hL x y) z hz

#print axioms zeroRankLocalNormalMap

end HodgeLean.Foundations.TubularEuler
