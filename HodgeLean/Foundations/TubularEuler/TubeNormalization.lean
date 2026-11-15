import HodgeLean.Foundations.TubularEuler.MetricTubeHelpers

/-! # Public smooth tubular transport

The selected geometric tube transports the supplied class to the independently
normalized Thom class without changing either original target signature.
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

/-- The transported supplied class has the standard complex normalization in every normal chart.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6;
Milnor–Stasheff, Characteristic Classes, §§10–11; Fulton, Intersection Theory, §6.3.
HC no distance; AV milestone no distance. -/
theorem transported_chart_normalization (t : SmoothNormalTube ι k v j hj)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c)
    (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) (i1_normalFibre j)))
    (he : e.IsLinear ℂ) :
    let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
    letI := N.fiberBundle
    letI := N.vectorBundle
    relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k (i1_normalFibre j) e)
      (transportedClass ι k v j hj t.toNormalTube c) =
        i1_chartOrientation k (i1_normalFibre j) e :=
  transported_chart_normalization_aux ι k v j hj t c hc e he

/-- Thom uniqueness identifies the actual transported class with the independent Thom class.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, uniqueness;
checked `BundleThom.i1_bundleThom_exists_unique`.
HC no distance; AV milestone no distance. -/
theorem transported_eq_thom (t : SmoothNormalTube ι k v j hj)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c) :
    transportedClass ι k v j hj t.toNormalTube c = normalThom ι k v j hj :=
  transported_eq_thom_aux ι k v j hj t c hc

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
