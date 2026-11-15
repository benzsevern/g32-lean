import HodgeLean.Foundations.Curves.AbelTheorem.FrameDualPeriods
import HodgeLean.Foundations.Curves.AbelTheorem.FrameClosedPeriods

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory Module
open scoped Topology ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem primitive_of_frame_dual_remainder (h : finrank ℂ E = 1) {D : C →₀ ℤ}
    (F : PeriodFrame (E := E) D)
    (η : Fin F.genus ⊕ Fin F.genus → C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hη : ∀ s, b3Forms_IsSmooth (η s))
    (hdual : ∀ s, ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ,
      b3Forms_IsSmooth α → b3Forms_d α = 0 →
        b3Forms_integral (b3Rest_b h) (b3Forms_wedgeForm α (η s)) =
          b3Forms_lineIntegral α (Sum.elim F.a F.b s).val 0 1)
    (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) (hα : b3Forms_IsSmooth α) (hd : b3Forms_d α = 0) :
    ∃ f : C → ℝ, b3Forms_IsSmooth (b3Forms_fun (E := E) f) ∧
      b3Forms_d (b3Forms_fun (E := E) f) = α + ∑ s,
        Sum.elim (fun i => -b3Forms_lineIntegral α (F.b i).val 0 1)
          (fun i => b3Forms_lineIntegral α (F.a i).val 0 1) s • η s := by
  classical
  let ζ (s : Fin F.genus ⊕ Fin F.genus) : b3Forms_closed E C 0 :=
    ⟨⟨η s, hη s⟩, by
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      exact b3Rest2_d_eq_zero_of_dual h (Sum.elim F.a F.b s).property.2
        (Sum.elim F.a F.b s).property.1 (hη s) (hdual s)⟩
  let ζ0 : b3Forms_closed E C 0 := ⟨⟨α, hα⟩, by
    apply LinearMap.mem_ker.mpr
    exact Subtype.ext hd⟩
  let c : Fin F.genus ⊕ Fin F.genus → ℝ := Sum.elim
    (fun i => -b3Forms_lineIntegral α (F.b i).val 0 1)
    (fun i => b3Forms_lineIntegral α (F.a i).val 0 1)
  let ψ : b3Forms_closed E C 0 := ζ0 + ∑ s, c s • ζ s
  have heq : ψ.val.val = α + ∑ s, c s • η s := by
    simp only [ψ, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul_of_tower, ζ, ζ0]
  have hsum : b3Forms_IsSmooth (∑ s, c s • η s) :=
    (b3Forms_Ω E C 1).sum_mem fun s _ => (hη s).smul _
  have heval (γ : b3_SmoothLoop E C) : b3Forms_lineIntegral ψ.val.val γ.val 0 1 =
      b3Forms_lineIntegral α γ.val 0 1 + ∑ s, c s * b3Forms_lineIntegral (η s) γ.val 0 1 := by
    rw [heq, b3Forms_lineIntegral_add hα hsum γ.property.2,
      b3Rest2_lineIntegral_sum _ (fun s _ => (hη s).smul _) γ.property.2]
    simp only [b3Forms_lineIntegral_smul]
  obtain ⟨haa, hab, hba, hbb⟩ := frame_dual_periods h F η hη hdual
  have hpa : ∀ i, b3Forms_lineIntegral ψ.val.val (F.a i).val 0 1 = 0 := by
    intro i
    rw [heval, Fintype.sum_sum_type]
    simp [c, haa, hba, mul_ite, Finset.sum_ite_eq']
  have hpb : ∀ i, b3Forms_lineIntegral ψ.val.val (F.b i).val 0 1 = 0 := by
    intro i
    rw [heval, Fintype.sum_sum_type]
    simp [c, hab, hbb, mul_ite, Finset.sum_ite_eq']
  obtain ⟨f, hf, hdf⟩ := closed_form_primitive_of_frame_periods_zero h F ψ.val.val
    ψ.val.property (b3Forms_closed_d_eq_zero ψ) hpa hpb
  exact ⟨f, hf, hdf.trans heq⟩

end HodgeLean.Foundations.Curves.AbelTheorem
