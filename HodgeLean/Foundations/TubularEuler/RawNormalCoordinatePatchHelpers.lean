import HodgeLean.Foundations.TubularEuler.RawNormalCoordinateHelpers
import HodgeLean.Foundations.TubularEuler.NormalCoordinatePatchDefs

/-! # Primitive normal patches from regularity of a raw ambient map

The model domain and all map agreement clauses are constructed from the original map.
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
variable (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
variable {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
variable (j : Q.left ⟶ V) [IsClosedImmersion j]
private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

/-- Regular raw normal coordinates give the primitive data before inverse construction.
Source: Mathlib, `isOpen_analyticAt` and `AnalyticOnNhd.contDiffOn_of_completeSpace`;
Lee, Introduction to Smooth Manifolds, second edition, proof of Theorem 6.24.
HC no distance; AV milestone no distance. -/
theorem normal_coordinate_patch_of_raw_map
    (U : Opens (TotalSpace (Fin k → ℂ) (i1_normalFibre j)))
    (f : TotalSpace (Fin k → ℂ) (i1_normalFibre j) →
      ComplexPoint (Over.mk (v ≫ W.hom))) (hf : ContinuousOn f U)
    (hU : ∀ y, zeroSection (Fin k → ℂ) (i1_normalFibre j) y ∈ U)
    (hzero : ∀ y,
      Point.map (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)
        (f (zeroSection (Fin k → ℂ) (i1_normalFibre j) y)) = Point.map ι y)
    (x : ComplexPoint Q)
    (b : OpenPartialHomeomorph (ComplexPoint Q) (Fin k → ℂ))
    (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) (i1_normalFibre j)))
    (a : OpenPartialHomeomorph (ComplexPoint W) ((Fin k → ℂ) × (Fin k → ℂ)))
    (hbhol : a3b4_IsHolChart Q.hom (b.trans
      ((Homeomorph.prodUnique (Fin k → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph)))
    (he : e.IsLinear ℂ) (hahol : a3b4_IsHolChart W.hom a)
    (hxb : x ∈ b.source)
    (hxe : zeroSection (Fin k → ℂ) (i1_normalFibre j) x ∈ e.source)
    (hmatch : ∀ y ∈ b.source, Point.map ι y ∈ a.source ∧
      a (Point.map ι y) = (b y, (0 : Fin k → ℂ)))
    (hsupport : ∀ y ∈ a.source,
      y ∈ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) ↔ (a y).2 = 0)
    (hanalytic :
      let P := e.toOpenPartialHomeomorph.trans
        (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
      AnalyticAt ℝ (fun q => a (Point.map
        (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W) (f (P.symm q)))) (b x, 0))
    (htransverse :
      let P := e.toOpenPartialHomeomorph.trans
        (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
      let g := fun q => Point.map
        (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W) (f (P.symm q))
      ∀ q, (q, (0 : Fin k → ℂ)) ∈ P.target →
        P.symm (q, 0) ∈ U → g (q, 0) ∈ a.source →
        ∃ A : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ),
          HasFDerivAt (fun w : Fin k → ℂ => (a (g (q, w))).2)
            A.toContinuousLinearMap 0) :
    Nonempty (NormalCoordinatePatch ι k v j U ⟨fun z => f z.val, hf.domRestrict⟩ x) := by
  letI := he
  let P := e.toOpenPartialHomeomorph.trans
    (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
  let g := fun z => Point.map
    (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W) (f z)
  let M := fun q => a (g (P.symm q))
  let z0 := zeroSection (Fin k → ℂ) (i1_normalFibre j) x
  have hzP : z0 ∈ P.source := by
    refine ⟨hxe, ?_⟩
    change e z0 ∈ (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ))).source
    rw [linearFrame_zeroSection k (i1_normalFibre j) e x (e.mem_source.mp hxe)]
    exact ⟨hxb, Set.mem_univ _⟩
  have hP0 : P z0 = (b x, (0 : Fin k → ℂ)) := by
    change (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ))) (e z0) = _
    rw [linearFrame_zeroSection k (i1_normalFibre j) e x (e.mem_source.mp hxe)]
    rfl
  have hg : ContinuousOn g U :=
    (Point.continuous_map (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)).comp_continuousOn hf
  obtain ⟨D, hxD, hDP, hDU, hDa⟩ := raw_map_coordinate_domain P a U g hg z0 hzP
    (hU x) (by rw [show g z0 = Point.map ι x from hzero x]; exact (hmatch x hxb).1)
  let S : Opens ((Fin k → ℂ) × (Fin k → ℂ)) :=
    ⟨(D : Set _) ∩ {q | AnalyticAt ℝ M q}, D.isOpen.inter (isOpen_analyticAt ℝ M)⟩
  refine ⟨{
    baseChart := b
    frame := e
    ambientChart := a
    base_hol := hbhol
    frame_linear := he
    ambient_hol := hahol
    base_mem := hxb
    frame_mem := hxe
    support := hsupport
    modelSource := S
    modelMap := M
    model_mem := ?_
    model_analytic := ?_
    model_fix := ?_
    model_transverse := ?_
    model_target := ?_
    frame_target := ?_
    map_domain := ?_
    map_agreement := ?_ }⟩
  · exact ⟨hP0 ▸ hxD, hanalytic⟩
  · exact (show AnalyticOnNhd ℝ M S from fun _ h => h.2).contDiffOn_of_completeSpace
  · intro q hq
    exact raw_normal_coordinates_fix_zero k (i1_normalFibre j) e b a
      (Point.map ι) g hzero (fun y hy => (hmatch y hy).2) q (hDP hq.1)
  · intro q hq
    exact htransverse q (hDP hq.1) (hDU hq.1) (hDa hq.1)
  · intro q hq
    exact a.map_source (hDa hq.1)
  · intro q hq
    exact hDP hq.1
  · intro q hq
    exact hDU hq.1
  · intro q hq
    exact a.left_inv (hDa hq.1)

#print axioms normal_coordinate_patch_of_raw_map

end HodgeLean.Foundations.TubularEuler
