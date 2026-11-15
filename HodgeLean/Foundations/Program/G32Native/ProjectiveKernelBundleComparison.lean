import HodgeLean.Foundations.BundleThom.AnalyticNormal
import HodgeLean.Foundations.BundleThom.ImmersionDefs
import HodgeLean.Foundations.BundleThom.LowRankThomExistenceHelpers
import HodgeLean.Foundations.BundleThom.NeighbourhoodDefs
import HodgeLean.Foundations.BundleThom.Proofs
import HodgeLean.Foundations.BundleThom.Thom
import HodgeLean.Foundations.BundleThom.ZeroRankThomUniquenessHelpers
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelGlobalEuler

/-! # Linear topological identifications with the projective kernel family -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace Bundle
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native
open EulerModel

/-- An actual bundle identification, retaining its base and every complex-linear fibre map.
Source: Fulton, Intersection Theory, §3.2, dual bundles; Bott–Tu, §6, bundle maps. -/
structure ProjectiveKernelBundleComparison
    {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)] where
  base : B ≃ₜ Projectivization ℂ (ℂ × (Fin k → ℂ))
  fibre : ∀ b, E b ≃ₗ[ℂ] projectiveNormalKernel k (base b)
  total : TotalSpace (Fin k → ℂ) E ≃ₜ ProjectiveNormalTotalSpace k
  base_eq : ∀ z, (total z).val.1 = base z.proj
  vector_eq : ∀ z, (total z).val.2 = (fibre z.proj z.2).val

namespace ProjectiveKernelBundleComparison
variable {B : Type} [TopologicalSpace B] {k : ℕ} {E : B → Type}
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    (D : ProjectiveKernelBundleComparison k E)

/-- Complex-linear fibre transport preserves exactly the zero section. -/
theorem zero_iff (z : TotalSpace (Fin k → ℂ) E) :
    (D.total z).val.2 = 0 ↔ z.2 = 0 := by
  rw [D.vector_eq]
  change (D.fibre z.proj z.2).val = (0 : projectiveNormalKernel k (D.base z.proj)).val ↔ _
  rw [Subtype.val_inj, (D.fibre z.proj).map_eq_zero_iff]

/-- The specified total-space homeomorphism restricts to the actual punctured pairs. -/
def pairMap : TopPair.ofSubset (X := i1_totalSpace k E) (i1_zeroSupport k E)ᶜ ⟶
    TopPair.ofSubset (X := TopCat.of (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0}ᶜ :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨D.total, D.total.continuous⟩)
    (fun z hz => fun h => hz ((D.zero_iff z).mp h))

/-- The same map retains the literal zero-section square. -/
theorem zeroSection [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E] (x : B) :
    TopPair.Hom.fst D.pairMap (i1_zeroSection k E x) =
      projectiveNormalZeroSection k (D.base x) := by
  apply Subtype.ext
  apply Prod.ext
  · exact D.base_eq ⟨x, 0⟩
  · change (D.total ⟨x, 0⟩).val.2 = 0
    rw [D.vector_eq]
    exact congrArg Subtype.val ((D.fibre x).map_zero)

end ProjectiveKernelBundleComparison

#print axioms ProjectiveKernelBundleComparison.zero_iff
#print axioms ProjectiveKernelBundleComparison.zeroSection
end HodgeLean.Foundations.Program.G32Native
