import HodgeLean.Foundations.BundleThom.NeighbourhoodDefs
import HodgeLean.Foundations.BundleThom.Topology
import HodgeLean.Foundations.Program.SchoenCycleC2ExcisionHelpers

/-! # Actual relative excision on normal bundle neighbourhoods

The neighbourhood contains every point of the prescribed zero support.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory TopologicalSpace Bundle AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Restriction to any actual open neighbourhood of the entire zero section is bijective on rational relative cohomology in every degree.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, relative excision around a closed support. -/
theorem i1_neighbourhoodInclusion_relativeCohomology_bijective
    {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (U : Opens (TotalSpace (Fin k → ℂ) E))
    (hU : ∀ b, zeroSection (Fin k → ℂ) E b ∈ U) (n : ℕ) :
    Function.Bijective (relativeCohomologyMap ℚ n (i1_neighbourhoodInclusion k E U)) := by
  apply HodgeLean.Foundations.Program.s2e_supportedCohomology_excision U.isOpen
    (i1_zeroSupport_isClosed k E)
  intro z hz
  have he : z = zeroSection (Fin k → ℂ) E z.proj := by
    cases z with
    | mk b v =>
      change v = 0 at hz
      subst v
      rfl
  rw [he]
  exact hU _

end HodgeLean.Foundations.BundleThom
