import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelLocalization
import HodgeLean.Foundations.Program.SchoenCycleC2EmbeddingExcisionHelpers

/-! # Excision at the actual projective normal section zero -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The distinguished projective zero is a closed support in the actual quotient topology. -/
theorem isClosed_normalProjectiveBase (k : ℕ) :
    IsClosed ({normalProjectiveBase k} :
      Set (Projectivization ℂ (ℂ × (Fin k → ℂ)))) := by
  have he : ({normalProjectiveBase k} : Set _) =
      (projectiveNormalSectionVector k) ⁻¹' {0} := by
    ext p
    exact (projectiveNormalSectionVector_zero_iff k p).symm
  rw [he]
  exact isClosed_singleton.preimage (continuous_projectiveNormalSectionVector k)

#print axioms isClosed_normalProjectiveBase
/-- The specified affine normal chart is an open embedding in the actual projective quotient. -/
theorem isOpenEmbedding_normalProjectiveChart (k : ℕ) :
    Topology.IsOpenEmbedding (normalProjectiveChart k) := by
  exact (isOpen_normalProjectiveChart_range k).isOpenEmbedding_subtypeVal.comp
    (normalProjectiveChartHomeomorph k).isOpenEmbedding

#print axioms isOpenEmbedding_normalProjectiveChart
/-- Restriction to the specified affine chart is bijective on the actual projective point-supported groups. -/
theorem normalProjectiveChartPair_cohomology_bijective (k n : ℕ) :
    Function.Bijective (relativeCohomologyMap ℚ n (normalProjectiveChartPair k)) := by
  let f : TopCat.of (Fin k → ℂ) ⟶
      TopCat.of (Projectivization ℂ (ℂ × (Fin k → ℂ))) :=
    TopCat.ofHom ⟨normalProjectiveChart k, continuous_normalProjectiveChart k⟩
  have hS : ({normalProjectiveBase k} : Set _) ⊆ Set.range f := by
    intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    exact ⟨0, rfl⟩
  have hST : ∀ z, f z ∈ ({normalProjectiveBase k} : Set _) ↔
      z ∈ ({0} : Set (Fin k → ℂ)) := normalProjectiveChart_eq_base_iff k
  have hb := HodgeLean.Foundations.Program.s2e_openEmbedding_supportPairMap_bijective
    f (isOpenEmbedding_normalProjectiveChart k) {0} {normalProjectiveBase k}
      (isClosed_normalProjectiveBase k) hS hST n
  exact hb

#print axioms normalProjectiveChartPair_cohomology_bijective
end HodgeLean.Foundations.Program.G32Native.EulerModel
