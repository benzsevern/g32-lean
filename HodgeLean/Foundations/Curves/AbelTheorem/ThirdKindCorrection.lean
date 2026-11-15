import HodgeLean.Foundations.Curves.AbelTheorem.Normalization
import HodgeLean.Foundations.Curves.AbelTheorem.LatticeEvaluation

noncomputable section
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open Module Manifold Filter Topology
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

theorem subtract_holomorphic_simple_poles (h : finrank ℂ E = 1)
    (D : C →₀ ℤ) (w : b4c_MeroForm E C h) (u : b3_HolForm E C)
    (ho : ∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0) :
    ∃ v : b4c_MeroForm E C h,
      ((v : TangentBundle 𝓘(ℂ, E) C → ℂ) =
        (w : TangentBundle 𝓘(ℂ, E) C → ℂ) - (u : TangentBundle 𝓘(ℂ, E) C → ℂ)) ∧
      (∀ x, b4c_res (hE := h) v x = b4c_res (hE := h) w x) ∧
      (∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h v x) 0) ∧
      ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h v x) 0 := by
  obtain ⟨hm, hr⟩ := RiemannRochEichler_sub_holForm h w u
  let v : b4c_MeroForm E C h := ⟨fun t => w t - u.val t, hm⟩
  have hloc (x : C) : HurwitzPrymRR_loc h v x =
      HurwitzPrymRR_loc h w x - HurwitzPrymRR_loc h u x := rfl
  refine ⟨v, rfl, hr, fun x => ?_, fun x hx => ?_⟩
  · rw [hloc, sub_eq_add_neg]
    have hu := (RiemannRochEichler_loc_analytic h u x).neg
    have hn : (-1 : WithTop ℤ) ≤ 0 := by
      change ((-1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ)
      exact_mod_cast (show (-1 : ℤ) ≤ 0 by omega)
    exact (le_min (ho x) (hn.trans hu.meromorphicOrderAt_nonneg)).trans
      (meromorphicOrderAt_add (w.property.2 x) hu.meromorphicAt)
  · rw [hloc]
    exact (ha x hx).sub (RiemannRochEichler_loc_analytic h u x)

def frameCorrectionForm {D : C →₀ ℤ} (F : PeriodFrame (E := E) D)
    (ell : b3_periodLattice E C) : b3_HolForm E C :=
  (2 * Real.pi * Complex.I) • ∑ i : Fin F.genus,
    ((F.latticeBasis.repr ell (.inr i) : ℤ) : ℂ) • F.forms i

theorem frame_correction_form_coe {D : C →₀ ℤ} (F : PeriodFrame (E := E) D)
    (ell : b3_periodLattice E C) :
    (frameCorrectionForm F ell : TangentBundle 𝓘(ℂ, E) C → ℂ) =
      (2 * Real.pi * Complex.I) • ∑ i : Fin F.genus,
        ((F.latticeBasis.repr ell (.inr i) : ℤ) : ℂ) •
          (F.forms i : TangentBundle 𝓘(ℂ, E) C → ℂ) := by
  simp only [frameCorrectionForm, Submodule.coe_smul, Submodule.coe_sum]

theorem frame_correction_period {D : C →₀ ℤ} (F : PeriodFrame (E := E) D)
    (ell : b3_periodLattice E C) (γ : b3_SmoothLoop E C) :
    loopIntegral γ (frameCorrectionForm F ell) =
      (2 * Real.pi * Complex.I) * ∑ i : Fin F.genus,
        ((F.latticeBasis.repr ell (.inr i) : ℤ) : ℂ) * loopIntegral γ (F.forms i) := by
  classical
  let L : b3_HolForm E C →ₗ[ℂ] ℂ := b3A_toDual
    ⟨b3_pathPeriod E C γ.val, b3A_pathPeriod_linear γ.val γ.property.2⟩
  change L (frameCorrectionForm F ell) = _
  simp only [frameCorrectionForm, map_smul, map_sum, smul_eq_mul]
  rfl

theorem frame_correction_a_period {D : C →₀ ℤ} (F : PeriodFrame (E := E) D)
    (ell : b3_periodLattice E C) (i : Fin F.genus) :
    loopIntegral (F.a i) (frameCorrectionForm F ell) =
      (2 * Real.pi * Complex.I) * ((F.latticeBasis.repr ell (.inr i) : ℤ) : ℂ) := by
  classical
  rw [frame_correction_period]
  simp only [F.normalized, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

theorem frame_correction_b_period (h : finrank ℂ E = 1) {D : C →₀ ℤ}
    (F : PeriodFrame (E := E) D) (ell : b3_periodLattice E C) (i : Fin F.genus) :
    loopIntegral (F.b i) (frameCorrectionForm F ell) =
      (2 * Real.pi * Complex.I) *
        (ell.val (F.forms i) - (F.latticeBasis.repr ell (.inl i) : ℂ)) := by
  classical
  rw [frame_correction_period]
  congr 1
  rw [frame_lattice_evaluation F ell i, add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro j hj
  rw [frame_matrix_symmetric h F i j]

end HodgeLean.Foundations.Curves.AbelTheorem
