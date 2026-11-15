import HodgeLean.Foundations.TubularEuler.NormalTubeConstructionHelpers
import HodgeLean.Foundations.TubularEuler.PartialHomeomorphOverlapHelpers
import HodgeLean.Adapters.NormalConeB4aGysinBridge2PrescribedChart

/-! # Smooth charts on a literal normal-map restriction

The ambient chart is restricted to the shared image of a local inverse.
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

private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

theorem normalTube_ambient_agrees_local
    (n : LocalNormalMap ι k v j hj) (t : NormalTube ι k v j hj)
    (hsub : (t.source : Set (TotalSpace (Fin k → ℂ) (i1_normalFibre j))) ⊆ n.domain)
    (hmap : ∀ z : t.source, (t.map z).val = n.map ⟨z.val, hsub z.property⟩)
    (x : ComplexPoint Q) (z : TotalSpace (Fin k → ℂ) (i1_normalFibre j))
    (hz : z ∈ t.source) (hL : z ∈ (n.localInverse x).source) :
    t.ambient z = n.localInverse x z := by
  rw [t.ambient_map ⟨z, hz⟩]
  change Point.map (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)
    ((t.map ⟨z, hz⟩).val) = _
  rw [hmap]
  exact (n.local_map x z hL).symm

variable [SmoothOfRelativeDimension k Q.hom]
variable [SmoothOfRelativeDimension (k + k) (v ≫ W.hom)]

def smoothNormalTubeOfRestriction
    (n : LocalNormalMap ι k v j hj) (t : NormalTube ι k v j hj)
    (hsub : (t.source : Set (TotalSpace (Fin k → ℂ) (i1_normalFibre j))) ⊆ n.domain)
    (hmap : ∀ z : t.source, (t.map z).val = n.map ⟨z.val, hsub z.property⟩)
    (hcover : ∀ z ∈ t.source, ∃ x, z ∈ (n.localInverse x).source) :
    SmoothNormalTube ι k v j hj := by
  let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  letI := N.fiberBundle
  letI := N.vectorBundle
  refine { t with localCharts := ?_ }
  intro z hz
  obtain ⟨x, hx⟩ := hcover z hz
  obtain ⟨b, e, a, hb, he, ha, hzb, hze, hza, hsupp, hcz, hcf, hcg, D, hD⟩ :=
    n.localCharts x z hx
  letI : e.IsLinear ℂ := he
  let P := e.toOpenPartialHomeomorph.trans
    (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
  let L := n.localInverse x
  let H := partialHomeomorphOverlap t.ambient L
  let a' := a.restrOpen H H.isOpen
  let c := tubeCoordinates ι k v j hj t b e a'
  let c' := (P.symm.trans L).trans a
  have hAL : Set.EqOn t.ambient L (t.ambient.source ∩ L.source) := by
    intro u hu
    have huT : u ∈ t.source := by
      change u ∈ (t.source : Set (TotalSpace (Fin k → ℂ) (i1_normalFibre j)))
      rw [← t.ambient_source]
      exact hu.1
    exact normalTube_ambient_agrees_local ι k v j hj n t hsub hmap x u huT hu.2
  have hcompat : c.source ⊆ c'.source ∧ Set.EqOn c c' c.source :=
    partialHomeomorph_restricted_coordinates P t.ambient L a hAL
  have hAz : t.ambient z = L z :=
    normalTube_ambient_agrees_local ι k v j hj n t hsub hmap x z hz hx
  have hzA : z ∈ t.ambient.source := t.ambient_source.symm ▸ hz
  have hzH : t.ambient z ∈ H := ⟨z, ⟨hx, hzA⟩, hAz.symm⟩
  have hza' : t.ambient z ∈ a'.source := ⟨hAz.symm ▸ hza, hzH⟩
  have heBase : z.proj ∈ e.baseSet := e.mem_source.mp hze
  have heZero : zeroSection (Fin k → ℂ) (i1_normalFibre j) z.proj ∈ e.source :=
    e.mem_source.mpr heBase
  have hPzeroSource : zeroSection (Fin k → ℂ) (i1_normalFibre j) z.proj ∈ P.source := by
    change zeroSection (Fin k → ℂ) (i1_normalFibre j) z.proj ∈ e.source ∧
      e (zeroSection (Fin k → ℂ) (i1_normalFibre j) z.proj) ∈
        (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ))).source
    refine ⟨heZero, ?_⟩
    rw [e.zeroSection ℂ heBase]
    exact ⟨hzb, Set.mem_univ _⟩
  have hPzero : P (zeroSection (Fin k → ℂ) (i1_normalFibre j) z.proj) =
      (b z.proj, (0 : Fin k → ℂ)) := by
    change (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
      (e (zeroSection (Fin k → ℂ) (i1_normalFibre j) z.proj)) = _
    rw [e.zeroSection ℂ heBase]
    rfl
  have hPinv : P.symm (b z.proj, (0 : Fin k → ℂ)) =
      zeroSection (Fin k → ℂ) (i1_normalFibre j) z.proj := by
    rw [← hPzero]
    exact P.left_inv hPzeroSource
  change ((b z.proj, (0 : Fin k → ℂ)) ∈ P.target ∧
    P.symm (b z.proj, (0 : Fin k → ℂ)) ∈ L.source) ∧
    L (P.symm (b z.proj, (0 : Fin k → ℂ))) ∈ a.source at hcz
  rw [hPinv] at hcz
  have htZero : zeroSection (Fin k → ℂ) (i1_normalFibre j) z.proj ∈ t.source :=
    t.contains_zero z.proj
  have htZeroA : zeroSection (Fin k → ℂ) (i1_normalFibre j) z.proj ∈ t.ambient.source :=
    t.ambient_source.symm ▸ htZero
  have hAzero : t.ambient (zeroSection (Fin k → ℂ) (i1_normalFibre j) z.proj) =
      L (zeroSection (Fin k → ℂ) (i1_normalFibre j) z.proj) :=
    normalTube_ambient_agrees_local ι k v j hj n t hsub hmap x _ htZero hcz.1.2
  have hZero : (b z.proj, (0 : Fin k → ℂ)) ∈ c.source := by
    change ((b z.proj, (0 : Fin k → ℂ)) ∈ P.target ∧
      P.symm (b z.proj, (0 : Fin k → ℂ)) ∈ t.ambient.source) ∧
      t.ambient (P.symm (b z.proj, (0 : Fin k → ℂ))) ∈ a'.source
    rw [hPinv]
    exact ⟨⟨hcz.1.1, htZeroA⟩, ⟨hAzero.symm ▸ hcz.2,
      ⟨zeroSection (Fin k → ℂ) (i1_normalFibre j) z.proj,
        ⟨hcz.1.2, htZeroA⟩, hAzero.symm⟩⟩⟩
  have hsmooth : ContDiffOn ℝ ⊤ c c.source ∧ ContDiffOn ℝ ⊤ c.symm c.target :=
    partialHomeomorph_contDiffOn_of_compatible c c' hcompat.1 hcompat.2 hcf hcg
  refine ⟨b, e, a', hb, he, a3b4g_isHolChart_restrOpen a ha (H : Set (ComplexPoint W)) H.isOpen,
    hzb, hze, hza', ?_, hZero, hsmooth.1, hsmooth.2, D, ?_⟩
  · intro y hy
    exact hsupp y hy.1
  · exact partialHomeomorph_fibre_derivative_of_compatible c c' hcompat.2
      (b z.proj) hZero D.toContinuousLinearMap hD

#print axioms smoothNormalTubeOfRestriction
#print axioms normalTube_ambient_agrees_local

end HodgeLean.Foundations.TubularEuler
