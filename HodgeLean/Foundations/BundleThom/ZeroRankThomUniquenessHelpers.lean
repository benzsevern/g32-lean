import HodgeLean.Foundations.BundleThom.ZeroRankThomHelpers
import HodgeLean.Foundations.BundleThom.RelativeDegreeZeroDetectionHelpers

/-! # Uniqueness of the actual zero-rank normalized bundle class

Actual chart inclusions cover the total space and detect degree-zero relative coclasses.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
variable [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin 0 → ℂ) E)]
variable [FiberBundle (Fin 0 → ℂ) E] [VectorBundle ℂ (Fin 0 → ℂ) E]

/-- The selected actual chart inclusions detect supported coclasses of a rank-zero complex bundle.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6; Hatcher, §3.1, degree-zero detection. -/
theorem i1_zeroRankClass_ext (u v : i1_supportedClass 0 E)
    (h : ∀ b : B, relativeCohomologyMap ℚ 0
      (i1_chartInclusion 0 E (trivializationAt (Fin 0 → ℂ) E b)) u =
      relativeCohomologyMap ℚ 0
        (i1_chartInclusion 0 E (trivializationAt (Fin 0 → ℂ) E b)) v) : u = v := by
  apply i1_relativeCohomologyZero_ext_of_cover (i1_zeroRankComplement_isEmpty E)
    (fun b => i1_chartPair 0 E (trivializationAt (Fin 0 → ℂ) E b))
    (fun b => i1_chartInclusion 0 E (trivializationAt (Fin 0 → ℂ) E b)) _ u v h
  intro z
  refine ⟨z.proj, ⟨z, ?_⟩, rfl⟩
  exact (trivializationAt (Fin 0 → ℂ) E z.proj).mem_source.mpr
    (FiberBundle.mem_baseSet_trivializationAt _ _ _)

/-- Existence and uniqueness of the actual normalized zero-rank complex bundle coclass.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, zero-rank Thom normalization. -/
theorem i1_zeroRankThom_exists_unique :
    ∃! u : i1_supportedClass 0 E,
      ∀ (e : Trivialization (Fin 0 → ℂ)
        (TotalSpace.proj : TotalSpace (Fin 0 → ℂ) E → B)) (he : e.IsLinear ℂ),
        relativeCohomologyMap ℚ 0 (i1_chartInclusion 0 E e) u =
          i1_chartOrientation 0 E e := by
  refine ⟨i1_zeroRankThom E, ?_, ?_⟩
  · intro e he
    exact i1_zeroRankThom_chart E e
  · intro u hu
    apply i1_zeroRankClass_ext E u (i1_zeroRankThom E)
    intro b
    rw [hu _ (inferInstance), i1_zeroRankThom_chart E]

end HodgeLean.Foundations.BundleThom
