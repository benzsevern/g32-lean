import HodgeLean.Foundations.TubularEuler.TubeDefs
import HodgeLean.Foundations.TubularEuler.CompactInjectivityHelpers
import HodgeLean.Foundations.TubularEuler.RadialShrinkingHelpers

/-! # Injective radial domains for the supplied normal map

Every restriction stays inside the original local-inverse cover.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle Topology
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

theorem localNormalMap_injective_neighbourhood (n : LocalNormalMap ι k v j hj) :
    ∃ U : Opens (TotalSpace (Fin k → ℂ) (i1_normalFibre j)),
      ∃ hsub : (U : Set (TotalSpace (Fin k → ℂ) (i1_normalFibre j))) ⊆
        (n.domain : Set (TotalSpace (Fin k → ℂ) (i1_normalFibre j))),
      (∀ x, zeroSection (Fin k → ℂ) (i1_normalFibre j) x ∈ U) ∧
      (∀ z ∈ U, ∃ x, z ∈ (n.localInverse x).source) ∧
      Function.Injective (fun z : U =>
        Point.map (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)
          (n.map ⟨z.val, hsub z.property⟩)) := by
  let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  letI := N.fiberBundle
  letI := N.vectorBundle
  letI : T2Space (ComplexPoint W) := HodgeLean.Foundations.Analytic.f4_t2Space W
  let z : C(ComplexPoint Q, n.domain) :=
    ⟨fun x => ⟨zeroSection (Fin k → ℂ) (i1_normalFibre j) x, n.contains_zero x⟩,
      (Bundle.Trivialization.continuous_zeroSection ℂ).subtype_mk n.contains_zero⟩
  let f : C(n.domain, ComplexPoint W) :=
    (Point.continuousMap (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)).comp n.map
  have hzero (x : ComplexPoint Q) : f (z x) = Point.map ι x := by
    change Point.map (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)
      (n.map ⟨zeroSection (Fin k → ℂ) (i1_normalFibre j) x, n.contains_zero x⟩) = _
    rw [n.map_zero]
    apply Over.OverMorphism.ext
    change (x.left ≫ j) ≫ v = x.left ≫ ι.left
    rw [Category.assoc, hj]
  letI : Mono ι := Over.mono_of_mono_left ι
  have hz : Function.Injective (f ∘ z) := by
    intro x y h
    apply ComplexPoint.map_injective_of_mono ι
    exact (hzero x).symm.trans (h.trans (hzero y))
  exact compact_partial_homeomorph_shrinking n.domain z f hz n.localInverse
    n.local_zero n.local_domain n.local_map

theorem localNormalMap_injective_radial_domain (n : LocalNormalMap ι k v j hj) :
    ∃ R : Opens (TotalSpace (Fin k → ℂ) (i1_normalFibre j)),
      ∃ hsub : (R : Set (TotalSpace (Fin k → ℂ) (i1_normalFibre j))) ⊆
        (n.domain : Set (TotalSpace (Fin k → ℂ) (i1_normalFibre j))),
      (∀ x, zeroSection (Fin k → ℂ) (i1_normalFibre j) x ∈ R) ∧
      (∀ z : R, ∀ a : ℝ, a ∈ Set.Icc 0 1 →
        (⟨z.val.proj, (a : ℂ) • z.val.2⟩ : TotalSpace (Fin k → ℂ) (i1_normalFibre j)) ∈ R) ∧
      (∀ z ∈ R, ∃ x, z ∈ (n.localInverse x).source) ∧
      Function.Injective (fun z : R =>
        Point.map (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)
          (n.map ⟨z.val, hsub z.property⟩)) := by
  let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  letI := N.fiberBundle
  letI := N.vectorBundle
  obtain ⟨U, hsub, hz, hcover, hinj⟩ := localNormalMap_injective_neighbourhood ι k v j hj n
  obtain ⟨R, hRU, hzero, hrad⟩ := bundle_radial_shrinking (i1_normalFibre j) U hz
  let hsubR : (R : Set (TotalSpace (Fin k → ℂ) (i1_normalFibre j))) ⊆ n.domain :=
    fun _ h => hsub (hRU h)
  refine ⟨R, hsubR, hzero, hrad, fun z hz => hcover z (hRU hz), ?_⟩
  intro z w h
  have hh := @hinj ⟨z.val, hRU z.property⟩ ⟨w.val, hRU w.property⟩ h
  exact Subtype.ext (congrArg (fun u : U => u.val) hh)

#print axioms localNormalMap_injective_radial_domain
#print axioms localNormalMap_injective_neighbourhood

end HodgeLean.Foundations.TubularEuler
