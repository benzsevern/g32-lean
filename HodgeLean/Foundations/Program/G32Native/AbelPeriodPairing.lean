import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.PeriodBasisCoordinates

/-! # Ordered form coordinates and literal period evaluation -/
noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open scoped Manifold ContDiff TensorProduct BigOperators
namespace HodgeLean.Foundations.Program.G32Native
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [Module.Finite ℤ (b3_periodLattice E C)]

/-- Linear coordinates leave the original form evaluation on the period quotient unchanged. -/
theorem periodLinear_coord_eq_dual (h : Module.finrank ℂ E = 1)
    (θ : b3_HolForm E C) (w : b3Rest2_QJ E C) :
    periodLinear θ (b2_coord (b3Rest2_QJ E C) w) = periodQuotientDualEquiv h w θ := by
  change (b3_periodF E C).liftQ (b3_cplxPeriod E C) le_rfl
    ((b2_coord (b3Rest2_QJ E C)).symm (b2_coord (b3Rest2_QJ E C) w)) θ = _
  rw [LinearEquiv.symm_apply_apply]
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (b3_periodF E C) w
  exact (periodQuotientDualEquiv_mk h u θ).symm

/-- Arbitrary retained form coefficients use the ordered coordinate pairing on the original period quotient. -/
theorem periodLinear_basis_pairing (h : Module.finrank ℂ E = 1)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℂ (b3_HolForm E C)) (a v : ι → ℂ) :
    periodLinear (b.equivFun.symm a)
      (b2_coord (b3Rest2_QJ E C) ((quotientBasisEquiv h b).symm v)) = ∑ i, a i * v i := by
  rw [periodLinear_coord_eq_dual h, b.equivFun_symm_apply, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (periodLinear_coord_eq_dual h (b i) _).symm.trans (periodLinear_basis_coord h b v i)

#print axioms periodLinear_coord_eq_dual
#print axioms periodLinear_basis_pairing
end HodgeLean.Foundations.Program.G32Native
