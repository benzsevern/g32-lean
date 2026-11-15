import HodgeLean.Foundations.TubularEuler.TubeDefs
import HodgeLean.Foundations.BundleThom.NormalNeighbourhoodExcisionHelpers

/-! # Actual supported class transported through a tube

Relative excision inverts the actual normal neighbourhood inclusion. The class
is transported from the supplied immersion class before comparison with Thom.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle AlgebraicTopology.Singular
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

/-- Inverse of the actual restriction to a neighbourhood of the zero section.
Source: Hatcher, Algebraic Topology, §2.2, relative excision.
HC no distance; AV milestone no distance. -/
def neighbourhoodExtension {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (U : Opens (TotalSpace (Fin k → ℂ) E))
    (hU : ∀ b, zeroSection (Fin k → ℂ) E b ∈ U) :
    RelativeCohomology ℚ (i1_neighbourhoodPair k E U) (2 * k) ≃ₗ[ℚ]
      i1_supportedClass k E :=
  (LinearEquiv.ofBijective
    (relativeCohomologyMap ℚ (2 * k) (i1_neighbourhoodInclusion k E U))
    (i1_neighbourhoodInclusion_relativeCohomology_bijective k E U hU (2 * k))).symm

example {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (U : Opens (TotalSpace (Fin k → ℂ) E))
    (hU : ∀ b, zeroSection (Fin k → ℂ) E b ∈ U) (u : i1_supportedClass k E) :
    neighbourhoodExtension k E U hU
      (relativeCohomologyMap ℚ (2 * k) (i1_neighbourhoodInclusion k E U) u) = u :=
  LinearEquiv.symm_apply_apply _ _

/-- Transport a supplied relative class through the actual neighbourhood pair map and excision.
Source: Hatcher, Algebraic Topology, §2.2; Bott–Tu, §6.
HC no distance; AV milestone no distance. -/
def transportThroughPair {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (U : Opens (TotalSpace (Fin k → ℂ) E))
    (hU : ∀ b, zeroSection (Fin k → ℂ) E b ∈ U) {X : TopPair}
    (f : i1_neighbourhoodPair k E U ⟶ X) (c : RelativeCohomology ℚ X (2 * k)) :
    i1_supportedClass k E :=
  neighbourhoodExtension k E U hU (relativeCohomologyMap ℚ (2 * k) f c)

example {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (U : Opens (TotalSpace (Fin k → ℂ) E))
    (hU : ∀ b, zeroSection (Fin k → ℂ) E b ∈ U) {X : TopPair}
    (f : i1_neighbourhoodPair k E U ⟶ X) (c : RelativeCohomology ℚ X (2 * k)) :
    relativeCohomologyMap ℚ (2 * k) (i1_neighbourhoodInclusion k E U)
      (transportThroughPair k E U hU f c) = relativeCohomologyMap ℚ (2 * k) f c :=
  (LinearEquiv.ofBijective _
    (i1_neighbourhoodInclusion_relativeCohomology_bijective k E U hU (2 * k))).apply_symm_apply _

variable {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
variable [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
variable (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
variable {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
variable (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
variable [SmoothOfRelativeDimension k Q.hom]
variable [SmoothOfRelativeDimension (k + k) (v ≫ W.hom)]

private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

/-- The actual support-complement pair map of the original tube.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6; Hatcher, §2.1.
HC no distance; AV milestone no distance. -/
def tubePairMap (t : NormalTube ι k v j hj) :=
  i1_neighbourhoodPairMap k (i1_normalFibre j) t.source
    (X := TopCat.of (ComplexPoint W))
    (a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ))
    (i1_tubularAmbientMap v j k t.source t.target t.map)
    (fun z hz hmem => hz ((t.support z).mp hmem))

/-- Pull back the supplied cycle class and extend by the actual excision inverse.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6; Hatcher, §2.2.
HC no distance; AV milestone no distance. -/
def transportedClass (t : NormalTube ι k v j hj)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k) :
    i1_supportedClass k (i1_normalFibre j) := by
  let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  letI := N.fiberBundle
  letI := N.vectorBundle
  exact transportThroughPair k (i1_normalFibre j) t.source t.contains_zero
    (tubePairMap ι k v j hj t) c

/-- The independent Thom class on the selected atlas of the actual normal.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6.
HC no distance; AV milestone no distance. -/
def normalThom [CompactSpace (ComplexPoint Q)] [T2Space (ComplexPoint Q)] :
    i1_supportedClass k (i1_normalFibre j) := by
  let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  letI := N.fiberBundle
  letI := N.vectorBundle
  exact i1_bundleThom k (i1_normalFibre j)

example [CompactSpace (ComplexPoint Q)] [T2Space (ComplexPoint Q)] :
    let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
    letI := N.fiberBundle
    letI := N.vectorBundle
    normalThom ι k v j hj = i1_bundleThom k (i1_normalFibre j) := rfl

/-- The retraction of the ambient tube onto the original submanifold.
Source: Lee, Introduction to Smooth Manifolds, second edition, Theorem 6.24.
HC no distance; AV milestone no distance. -/
def tubeRetraction (t : NormalTube ι k v j hj) : C(t.target, ComplexPoint Q) := by
  let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  letI := N.fiberBundle
  letI := N.vectorBundle
  exact ⟨fun y => (t.map.symm y).1.proj,
    (FiberBundle.continuous_proj (Fin k → ℂ) (i1_normalFibre j)).comp
      (continuous_subtype_val.comp t.map.symm.continuous)⟩

example (t : NormalTube ι k v j hj) (z : t.source) :
    (tubePairMap ι k v j hj t).right z =
      i1_tubularAmbientMap v j k t.source t.target t.map z := rfl

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

example (t : NormalTube ι k v j hj) (z : t.source) :
    tubeRetraction ι k v j hj t (t.map z) = z.1.proj := by
  change (t.map.symm (t.map z)).1.proj = z.1.proj
  rw [t.map.symm_apply_apply]

end HodgeLean.Foundations.TubularEuler
