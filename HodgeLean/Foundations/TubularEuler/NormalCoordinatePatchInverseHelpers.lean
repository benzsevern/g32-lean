import HodgeLean.Foundations.TubularEuler.NormalCoordinatePatchDefs
import HodgeLean.Foundations.TubularEuler.NormalLocalChartTransportHelpers

/-! # Inverses from primitive coordinates of the supplied normal map

The inverse coordinate map is constructed by the analytic inverse function theorem.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Bundle
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

variable {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
variable [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
variable [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
variable {ι : Q ⟶ W} [IsClosedImmersion ι.left] {k : ℕ}
variable {V : Scheme} {v : V ⟶ W.left} [IsOpenImmersion v]
variable {j : Q.left ⟶ V} [IsClosedImmersion j]
private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

variable {U : Opens (TotalSpace (Fin k → ℂ) (i1_normalFibre j))}
variable {m : C(U, ComplexPoint (Over.mk (v ≫ W.hom)))} {x : ComplexPoint Q}
namespace NormalCoordinatePatch
variable (p : NormalCoordinatePatch ι k v j U m x)

def coordinateInverse : OpenPartialHomeomorph ((Fin k → ℂ) × (Fin k → ℂ))
    ((Fin k → ℂ) × (Fin k → ℂ)) :=
  Classical.choose (analytic_complex_normal_inverse_on_source p.modelMap p.modelSource
    p.modelSource.isOpen p.model_analytic p.model_fix p.model_transverse
    (p.baseChart x) p.model_mem)

theorem coordinateInverse_spec :
    (p.baseChart x, (0 : Fin k → ℂ)) ∈ p.coordinateInverse.source ∧
    p.coordinateInverse.source ⊆ p.modelSource ∧
    (p.coordinateInverse : ((Fin k → ℂ) × (Fin k → ℂ)) →
      ((Fin k → ℂ) × (Fin k → ℂ))) = p.modelMap ∧
    ContDiffOn ℝ ⊤ p.coordinateInverse p.coordinateInverse.source ∧
    ContDiffOn ℝ ⊤ p.coordinateInverse.symm p.coordinateInverse.target ∧
    (∀ q ∈ p.coordinateInverse.source, (p.coordinateInverse q).2 = 0 ↔ q.2 = 0) ∧
    (∀ q ∈ p.coordinateInverse.source, (q.1, (0 : Fin k → ℂ)) ∈ p.coordinateInverse.source) ∧
    ∀ q ∈ p.coordinateInverse.source, ∃ A : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ),
      HasFDerivAt (fun w : Fin k → ℂ => (p.coordinateInverse (q.1, w)).2)
        A.toContinuousLinearMap 0 :=
  Classical.choose_spec (analytic_complex_normal_inverse_on_source p.modelMap p.modelSource
    p.modelSource.isOpen p.model_analytic p.model_fix p.model_transverse
    (p.baseChart x) p.model_mem)

def frameProduct : OpenPartialHomeomorph (TotalSpace (Fin k → ℂ) (i1_normalFibre j))
    ((Fin k → ℂ) × (Fin k → ℂ)) :=
  p.frame.toOpenPartialHomeomorph.trans
    (p.baseChart.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))

def localInverse : OpenPartialHomeomorph (TotalSpace (Fin k → ℂ) (i1_normalFibre j))
    (ComplexPoint W) :=
  (p.frameProduct.trans p.coordinateInverse).trans p.ambientChart.symm

theorem coordinateInverse_target : p.coordinateInverse.target ⊆ p.ambientChart.target := by
  intro y hy
  have hq := p.coordinateInverse.map_target hy
  have hD := p.coordinateInverse_spec.2.1 hq
  have h := p.model_target hD
  rw [← p.coordinateInverse_spec.2.2.1, p.coordinateInverse.right_inv hy] at h
  exact h

theorem localInverse_zero :
    zeroSection (Fin k → ℂ) (i1_normalFibre j) x ∈ p.localInverse.source := by
  letI := p.frame_linear
  let z0 := zeroSection (Fin k → ℂ) (i1_normalFibre j) x
  have hb : x ∈ p.frame.baseSet := p.frame.mem_source.mp p.frame_mem
  have hf0 : p.frame z0 = (x, (0 : Fin k → ℂ)) := by
    apply Prod.ext
    · exact p.frame.coe_fst' (x := z0) hb
    · exact (p.frame.linearEquivAt ℂ x hb).map_zero
  have hzP : z0 ∈ p.frameProduct.source := by
    refine ⟨p.frame_mem, ?_⟩
    change p.frame z0 ∈ (p.baseChart.prod (OpenPartialHomeomorph.refl (Fin k → ℂ))).source
    rw [hf0]
    exact ⟨p.base_mem, Set.mem_univ _⟩
  have hP0 : p.frameProduct z0 = (p.baseChart x, (0 : Fin k → ℂ)) := by
    change (p.baseChart.prod (OpenPartialHomeomorph.refl (Fin k → ℂ))) (p.frame z0) = _
    rw [hf0]
    rfl
  change (z0 ∈ p.frameProduct.source ∧ p.frameProduct z0 ∈ p.coordinateInverse.source) ∧
    p.coordinateInverse (p.frameProduct z0) ∈ p.ambientChart.target
  rw [hP0]
  exact ⟨⟨hzP, p.coordinateInverse_spec.1⟩,
    p.coordinateInverse_target (p.coordinateInverse.map_source p.coordinateInverse_spec.1)⟩

theorem localInverse_domain
    (z : TotalSpace (Fin k → ℂ) (i1_normalFibre j)) (hz : z ∈ p.localInverse.source) :
    z ∈ U := by
  have hzP : z ∈ p.frameProduct.source := hz.1.1
  have hzc : p.frameProduct z ∈ p.coordinateInverse.source := hz.1.2
  have hD := p.coordinateInverse_spec.2.1 hzc
  have h := p.map_domain (p.frameProduct z) hD
  change p.frameProduct.symm (p.frameProduct z) ∈ U at h
  rwa [p.frameProduct.left_inv hzP] at h

theorem localInverse_map
    (z : TotalSpace (Fin k → ℂ) (i1_normalFibre j)) (hz : z ∈ p.localInverse.source) :
    p.localInverse z =
      Point.map (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)
        (m ⟨z, p.localInverse_domain z hz⟩) := by
  have hzP : z ∈ p.frameProduct.source := hz.1.1
  have hzc : p.frameProduct z ∈ p.coordinateInverse.source := hz.1.2
  have hD := p.coordinateInverse_spec.2.1 hzc
  calc
    p.localInverse z = p.ambientChart.symm (p.modelMap (p.frameProduct z)) :=
      congrArg p.ambientChart.symm (congrFun p.coordinateInverse_spec.2.2.1 (p.frameProduct z))
    _ = Point.map (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)
        (m ⟨p.frameProduct.symm (p.frameProduct z), p.map_domain (p.frameProduct z) hD⟩) :=
      p.map_agreement (p.frameProduct z) hD
    _ = _ := congrArg
      (fun w : U => Point.map (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W) (m w))
      (Subtype.ext (p.frameProduct.left_inv hzP))

theorem localInverse_geometry
    (z : TotalSpace (Fin k → ℂ) (i1_normalFibre j)) (hz : z ∈ p.localInverse.source) :
    z.proj ∈ p.baseChart.source ∧ z ∈ p.frame.source ∧
    p.localInverse z ∈ p.ambientChart.source ∧
    zeroSection (Fin k → ℂ) (i1_normalFibre j) z.proj ∈ p.localInverse.source ∧
    (p.localInverse z ∈ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) ↔ z.2 = 0) ∧
    let C := (p.frameProduct.symm.trans p.localInverse).trans p.ambientChart
    (p.baseChart z.proj, (0 : Fin k → ℂ)) ∈ C.source ∧
    ContDiffOn ℝ ⊤ C C.source ∧ ContDiffOn ℝ ⊤ C.symm C.target ∧
    ∃ A : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ),
      HasFDerivAt (fun w : Fin k → ℂ => (C (p.baseChart z.proj, w)).2)
        A.toContinuousLinearMap 0 := by
  letI := p.frame_linear
  obtain ⟨_, hsub, _, hcf, hcg, hs, hzero, hder⟩ := p.coordinateInverse_spec
  exact normal_local_inverse_chart_transport k (i1_normalFibre j)
    p.frame p.baseChart p.ambientChart p.coordinateInverse
    (fun _ hq => p.frame_target (hsub hq)) p.coordinateInverse_target
    hzero hs hcf hcg hder (a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ)) p.support z hz

#print axioms coordinateInverse
#print axioms coordinateInverse_spec
#print axioms frameProduct
#print axioms localInverse
#print axioms coordinateInverse_target
#print axioms localInverse_zero
#print axioms localInverse_domain
#print axioms localInverse_map
#print axioms localInverse_geometry

end NormalCoordinatePatch
end HodgeLean.Foundations.TubularEuler
