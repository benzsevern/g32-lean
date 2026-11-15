import HodgeLean.Foundations.Curves.AbelTheorem.AbelBaseTranslation

noncomputable section
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open Manifold
open scoped ContDiff BigOperators TensorProduct
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Source: Miranda, Algebraic Curves and Riemann Surfaces, VIII.2, path changes modulo the period lattice. -/
theorem integral_lattice_of_divisor_path_difference (h : Module.finrank ℂ E = 1)
    (D : C →₀ ℤ) (hdeg : b4c_deg D = 0) (p q : C)
    (paths other : C → ℝ → C)
    (hp : ∀ x, b3A_IsGoodPath (E := E) (paths x) p x)
    (hq : ∀ x, b3A_IsGoodPath (E := E) (other x) q x) :
    ∃ ell : b3_periodLattice E C, ∀ θ : b3_HolForm E C,
      divisorIntegral (E := E) D other θ - divisorIntegral (E := E) D paths θ = ell.val θ := by
  classical
  have ha := (b3_exists_abelJacobi (E := E) (C := C) h p).choose_spec
  have hb := (b3_exists_abelJacobi (E := E) (C := C) h q).choose_spec
  choose u hu hju using fun x => ha.2 (paths x) (hp x).1
  choose v hv hjv using fun x => hb.2 (other x) (hq x).1
  have hju' (x : C) : b3A_jacMk (u x) = analyticAbel h p x := by
    have hx := hju x
    rw [(hp x).apply_one, (hp x).apply_zero, ha.1, sub_zero] at hx
    exact hx.symm
  have hjv' (x : C) : b3A_jacMk (v x) = analyticAbel h q x := by
    have hx := hjv x
    rw [(hq x).apply_one, (hq x).apply_zero, hb.1, sub_zero] at hx
    exact hx.symm
  let t := weightedSum v D - weightedSum u D
  have ht : b3A_jacMk t = 0 := by
    change b3A_jacMk (D.sum (fun x n => n • v x) - D.sum (fun x n => n • u x)) = 0
    rw [map_sub, map_finsuppSum, map_finsuppSum]
    simp only [map_zsmul, hju', hjv']
    change weightedSum (analyticAbel h q) D - weightedSum (analyticAbel h p) D = 0
    rw [abel_divisor_sum_base_independent h p q D hdeg, sub_self]
  obtain ⟨ell, hell⟩ := (QuotientAddGroup.eq_zero_iff _).mp ht
  have heq : (Submodule.Quotient.mk ((1 : ℂ) ⊗ₜ[ℤ] ell) :
      (ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) = Submodule.Quotient.mk t := hell
  have hker := (Submodule.Quotient.eq (b3_periodF E C)).mp heq
  change b3_cplxPeriod E C ((1 : ℂ) ⊗ₜ[ℤ] ell - t) = 0 at hker
  have htper : b3_cplxPeriod E C t = ell.val := by
    rw [map_sub] at hker
    change (1 : ℂ) • ell.val - b3_cplxPeriod E C t = 0 at hker
    simpa only [one_smul] using (sub_eq_zero.mp hker).symm
  refine ⟨ell, fun θ => ?_⟩
  rw [← htper]
  change _ = b3_cplxPeriod E C (D.sum (fun x n => n • v x) - D.sum (fun x n => n • u x)) θ
  rw [map_sub, map_finsuppSum, map_finsuppSum]
  simp only [map_zsmul, hu, hv, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
    zsmul_eq_mul]
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply]
  rfl

end HodgeLean.Foundations.Curves.AbelTheorem
