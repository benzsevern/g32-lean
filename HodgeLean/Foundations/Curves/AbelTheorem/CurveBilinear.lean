import HodgeLean.Foundations.Curves.AbelTheorem.NormalizedFrame
import HodgeLean.Foundations.Curves.AbelTheorem.NormalizedPositive

noncomputable section
open HodgeLean.Foundations.Program
open Module Manifold
open scoped ContDiff BigOperators TensorProduct
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

def complexPeriodFunctional :
    (ℂ ⊗[ℤ] b3_periodLattice E C) →ₗ[ℂ] Dual ℂ (b3_HolForm E C) :=
  b3A_toDual.comp ((b3_cplxPeriod E C).codRestrict (b3_linearDual E C)
    b3A_cplxPeriod_mem_linearDual)

theorem complex_period_functional_kernel :
    (complexPeriodFunctional (E := E) (C := C)).ker = b3_periodF E C := by
  ext v
  change complexPeriodFunctional v = 0 ↔ b3_cplxPeriod E C v = 0
  constructor
  · intro hv
    funext θ
    exact LinearMap.congr_fun hv θ
  · intro hv
    ext θ
    exact congrFun hv θ

theorem frame_period_evaluation {D : C →₀ ℤ} (F : PeriodFrame (E := E) D)
    (i : Fin F.genus ⊕ Fin F.genus) (θ : b3_HolForm E C) :
    complexPeriodFunctional ((1 : ℂ) ⊗ₜ[ℤ] F.latticeBasis i) θ =
      loopIntegral (Sum.elim F.a F.b i) θ := by
  rcases i with i | i
  · rw [F.a_basis]
    change (1 : ℂ) * loopIntegral (F.a i) θ = loopIntegral (F.a i) θ
    exact one_mul _
  · rw [F.b_basis]
    change (1 : ℂ) * loopIntegral (F.b i) θ = loopIntegral (F.b i) θ
    exact one_mul _

theorem frame_matrix_symmetric (h : finrank ℂ E = 1) {D : C →₀ ℤ}
    (F : PeriodFrame (E := E) D) (i j : Fin F.genus) :
    loopIntegral (F.b i) (F.forms j) = loopIntegral (F.b j) (F.forms i) := by
  have hR : b2_IsRiemannForm (b3_periodLattice E C)
      (complexPeriodFunctional (E := E) (C := C)).ker F.intersection := by
    rw [complex_period_functional_kernel]
    exact b3_intersectionForm_isRiemannForm h F.intersection F.intersection_spec
  have hn (i j : Fin F.genus) :
      complexPeriodFunctional ((1 : ℂ) ⊗ₜ[ℤ] F.latticeBasis (.inl i)) (F.forms j) =
        if i = j then 1 else 0 :=
    (frame_period_evaluation F (.inl i) (F.forms j)).trans (F.normalized i j)
  have he := normalized_matrix_symmetric F.latticeBasis F.intersection
    complexPeriodFunctional F.forms hR F.ab F.aa F.bb hn i j
  simpa only [frame_period_evaluation, Sum.elim_inr] using he

theorem frame_matrix_positive (h : finrank ℂ E = 1) {D : C →₀ ℤ}
    (F : PeriodFrame (E := E) D) (z : Fin F.genus → ℂ) (hz : z ≠ 0) :
    0 < (∑ i, ∑ j, star (z i) * loopIntegral (F.b i) (F.forms j) * z j).im := by
  have hR : b2_IsRiemannForm (b3_periodLattice E C)
      (complexPeriodFunctional (E := E) (C := C)).ker F.intersection := by
    rw [complex_period_functional_kernel]
    exact b3_intersectionForm_isRiemannForm h F.intersection F.intersection_spec
  have hn (i j : Fin F.genus) :
      complexPeriodFunctional ((1 : ℂ) ⊗ₜ[ℤ] F.latticeBasis (.inl i)) (F.forms j) =
        if i = j then 1 else 0 :=
    (frame_period_evaluation F (.inl i) (F.forms j)).trans (F.normalized i j)
  have he := normalized_matrix_positive F.latticeBasis F.intersection
    complexPeriodFunctional F.forms hR F.ab F.aa F.bb hn z hz
  simpa only [frame_period_evaluation, Sum.elim_inr] using he

end HodgeLean.Foundations.Curves.AbelTheorem
