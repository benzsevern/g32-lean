import HodgeLean.Foundations.TubularEuler.ZeroRankNormalMapHelpers
import HodgeLean.Foundations.TubularEuler.TransferDefs
import HodgeLean.Foundations.TubularEuler.NormalTubeSmoothHelpers
import HodgeLean.Foundations.TubularEuler.TransportNormalizationHelpers

/-! # Smooth geometric tubes and local oriented restriction

The geometric construction uses compact injectivity of a normal exponential
map, after local inverses along its zero section. The class comparison
compares the supplied cycle class in actual
holomorphic coordinates with the complex transverse derivative.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle AlgebraicTopology.Singular
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

variable {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
variable [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
variable (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
variable {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
variable (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
variable [SmoothOfRelativeDimension k Q.hom]
variable [SmoothOfRelativeDimension (k + k) (v ≫ W.hom)]
variable [CompactSpace (ComplexPoint Q)] [T2Space (ComplexPoint Q)]

private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

/-- Shrinking the given local normal map around a compact zero section gives a radial tube.
The resulting map is a restriction of the supplied map, rather than a new map.
Source: Lee, Introduction to Smooth Manifolds, second edition, proof of Theorem 6.24,
compact shrinking and injectivity.
HC no distance; AV milestone no distance. -/
theorem compact_normal_map_shrinking_aux (n : LocalNormalMap ι k v j hj) :
    ∃ t : SmoothNormalTube ι k v j hj,
      ∃ hsub : (t.source : Set (TotalSpace (Fin k → ℂ) (i1_normalFibre j))) ⊆
        (n.domain : Set (TotalSpace (Fin k → ℂ) (i1_normalFibre j))),
        ∀ z : t.source, (t.map z).val = n.map ⟨z.val, hsub z.property⟩ := by
  obtain ⟨R, hsub, hzero, hrad, hcover, hinj⟩ :=
    localNormalMap_injective_radial_domain ι k v j hj n
  let t := normalTubeOfRestriction ι k v j hj n R hsub hzero hrad hcover hinj
  have hmap : ∀ z : t.source, (t.map z).val = n.map ⟨z.val, hsub z.property⟩ := by
    intro z
    rfl
  exact ⟨smoothNormalTubeOfRestriction ι k v j hj n t hsub hmap hcover, hsub, hmap⟩

example (n : LocalNormalMap ι k v j hj) (x : ComplexPoint Q) :
    zeroSection (Fin k → ℂ) (i1_normalFibre j) x ∈ n.domain := n.contains_zero x

example (n : LocalNormalMap ι k v j hj) (t : SmoothNormalTube ι k v j hj)
    (hsub : (t.source : Set (TotalSpace (Fin k → ℂ) (i1_normalFibre j))) ⊆
        (n.domain : Set (TotalSpace (Fin k → ℂ) (i1_normalFibre j))))
    (hmap : ∀ z : t.source, (t.map z).val = n.map ⟨z.val, hsub z.property⟩)
    (x : ComplexPoint Q) :
    n.map ⟨zeroSection (Fin k → ℂ) (i1_normalFibre j) x,
      hsub (t.contains_zero x)⟩ = Point.map (i1_smoothLift ι v j hj) x := by
  exact (hmap ⟨zeroSection (Fin k → ℂ) (i1_normalFibre j) x,
    t.contains_zero x⟩).symm.trans (t.map_zero x _)

/-- The transported supplied class has the standard complex normalization in every normal chart.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6;
Milnor–Stasheff, Characteristic Classes, §§10–11; Fulton, Intersection Theory, §6.3.
HC no distance; AV milestone no distance. -/
theorem transported_chart_normalization_aux (t : SmoothNormalTube ι k v j hj)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c)
    (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) (i1_normalFibre j)))
    (he : e.IsLinear ℂ) :
    let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
    letI := N.fiberBundle
    letI := N.vectorBundle
    relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k (i1_normalFibre j) e)
      (transportedClass ι k v j hj t.toNormalTube c) =
        i1_chartOrientation k (i1_normalFibre j) e := by
  let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  letI := N.fiberBundle
  letI := N.vectorBundle
  rw [transportedClass_eq_normalThom_of_transverse_charts ι k v j hj t c hc]
  exact Classical.choose_spec (i1_bundleThom_exists_unique k (i1_normalFibre j)).exists e he

/-- Thom uniqueness identifies the actual transported class with the independent Thom class.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, uniqueness;
checked `BundleThom.i1_bundleThom_exists_unique`.
HC no distance; AV milestone no distance. -/
theorem transported_eq_thom_aux (t : SmoothNormalTube ι k v j hj)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c) :
    transportedClass ι k v j hj t.toNormalTube c = normalThom ι k v j hj := by
  let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  letI := N.fiberBundle
  letI := N.vectorBundle
  change transportedClass ι k v j hj t.toNormalTube c = i1_bundleThom k (i1_normalFibre j)
  apply (i1_bundleThom_exists_unique k (i1_normalFibre j)).unique
  · exact transported_chart_normalization_aux ι k v j hj t c hc
  · exact Classical.choose_spec (i1_bundleThom_exists_unique k (i1_normalFibre j)).exists

example (t : SmoothNormalTube ι k v j hj) (z : t.source)
    (hz : z.1.2 ≠ 0) :
    i1_tubularAmbientMap v j k t.source t.target t.map z ∉
      a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) :=
  fun h => hz ((t.support z).mp h)

example (t : NormalTube ι k v j hj)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k) :
    relativeCohomologyMap ℚ (2 * k)
      (i1_neighbourhoodInclusion k (i1_normalFibre j) t.source)
      (transportedClass ι k v j hj t c) =
    relativeCohomologyMap ℚ (2 * k) (tubePairMap ι k v j hj t) c := by
  let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  letI := N.fiberBundle
  letI := N.vectorBundle
  exact (LinearEquiv.ofBijective
    (relativeCohomologyMap ℚ (2 * k) (i1_neighbourhoodInclusion k (i1_normalFibre j) t.source))
    (i1_neighbourhoodInclusion_relativeCohomology_bijective k (i1_normalFibre j)
      t.source t.contains_zero (2 * k))).apply_symm_apply _

example (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) (i1_normalFibre j)))
    (he : e.IsLinear ℂ) :
    let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
    letI := N.fiberBundle
    letI := N.vectorBundle
    relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k (i1_normalFibre j) e)
      (i1_bundleThom k (i1_normalFibre j)) = i1_chartOrientation k (i1_normalFibre j) e  := by
  let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  letI := N.fiberBundle
  letI := N.vectorBundle
  exact Classical.choose_spec (i1_bundleThom_exists_unique k (i1_normalFibre j)).exists e he

end HodgeLean.Foundations.TubularEuler
