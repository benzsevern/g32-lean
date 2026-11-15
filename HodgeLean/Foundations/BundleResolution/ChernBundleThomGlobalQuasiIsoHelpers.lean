import HodgeLean.Foundations.BundleResolution.ChernBundleThomDomainQuasiIsoHelpers
import HodgeLean.Foundations.BundleResolution.ChernFiniteCoverCapQuasiIsoHelpers
import HodgeLean.Foundations.BundleThom.ChartDomainGluingHelpers

/-! # Actual global Thom cap from the finite linear chart cover

Compactness supplies actual linear charts. The normalized selected cocycle
has the checked comparison on every open domain inside each chart.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex Bundle TopologicalSpace AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {k : ℕ} (E : I1ComplexBundle B k)

theorem i1_bundleThomCocycle_global_cap_quasiIso [Nonempty B] :
    QuasiIso (i1_globalEvenCapExtendedMap (i1_totalSpace k E.fibre) (TopCat.of B)
      (TopCat.ofHom (i1_complexBundleTotalProjection E)) (i1_zeroSupport k E.fibre)ᶜ k
      (i1_bundleThomCocycle E)) := by
  classical
  obtain ⟨s, hcover⟩ := i1_bundle_finite_chartSource_cover k E.fibre
  have hs : s.Nonempty := by
    obtain ⟨b, hb, _⟩ := hcover (zeroSection (Fin k → ℂ) E.fibre (Classical.arbitrary B))
    exact ⟨b, hb⟩
  let A : B → Set (TopCat.of B) := fun b => (trivializationAt (Fin k → ℂ) E.fibre b).baseSet
  have hbase : (⋃ b ∈ s, A b) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro b
    obtain ⟨a, ha, hz⟩ := hcover (⟨b, 0⟩ : TotalSpace (Fin k → ℂ) E.fibre)
    exact Set.mem_iUnion₂.mpr
      ⟨a, ha, (trivializationAt (Fin k → ℂ) E.fibre a).mem_source.mp hz⟩
  exact i1_globalEvenCapExtendedMap_quasiIso_of_finite_cover
    (i1_totalSpace k E.fibre) (TopCat.of B) (TopCat.ofHom (i1_complexBundleTotalProjection E))
    (i1_zeroSupport k E.fibre)ᶜ k (i1_bundleThomCocycle E) A
    (fun b => (trivializationAt (Fin k → ℂ) E.fibre b).open_baseSet)
    (fun b T hT hsub => i1_bundleThomCocycle_domain_open_quasiIso E
      (trivializationAt (Fin k → ℂ) E.fibre b) T hT hsub) s hs hbase

end HodgeLean.Foundations.BundleResolution
