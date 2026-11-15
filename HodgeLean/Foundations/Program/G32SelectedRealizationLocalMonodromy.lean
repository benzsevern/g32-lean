import HodgeLean.Foundations.Program.G32SelectedRealizationStabilizerPeriod
import HodgeLean.Foundations.Program.G32SelectedRealizationSubgroupRotation
import HodgeLean.Papers.PapersSupplyProofs

noncomputable section
open Manifold HodgeLean.Papers
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem g32y_local_monodromy_rotGen {E C G : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (H : Subgroup G) (x : C) (g : G) (hg : b4_IsRotGen E x g) (a : G) :
    b4_IsRotGen E (a⁻¹ • x)
      (⟨a⁻¹ * g ^ Function.minimalPeriod (g • ·) (a : G ⧸ H) * a,
        conj_pow_minimalPeriod_mem H g a⟩ : H) := by
  let l := Function.minimalPeriod (g • ·) (a : G ⧸ H)
  let k := a⁻¹ * g * a
  have hk : b4_IsRotGen E (a⁻¹ • x) k := by
    simpa only [inv_inv] using RiemannRochTop_rotGen_conjugate hG x a⁻¹ g hg
  have hp : k ^ l = a⁻¹ * g ^ l * a := by
    simpa only [MulAut.conj_apply, inv_inv] using (map_pow (MulAut.conj a⁻¹) g l).symm
  have hm : k ^ l ∈ H := by
    rw [hp]
    exact conj_pow_minimalPeriod_mem H g a
  have ho : orderOf k = orderOf g := by
    simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj a⁻¹).orderOf_eq g
  have hcard : orderOf k = l * Nat.card (MulAction.stabilizer H (a⁻¹ • x)) :=
    ho.trans (g32y_stabilizer_period_card H x g (RiemannRochTop_rotGen_zpowers x g hg).symm a)
  have hl : 0 < l := by
    have hn : 0 < l * Nat.card (MulAction.stabilizer H (a⁻¹ • x)) := by
      rw [← hcard]
      exact orderOf_pos k
    by_contra h
    have h0 : l = 0 := by omega
    rw [h0, zero_mul] at hn
    omega
  have hrot := g32y_subgroup_rotGen_power hE hG H (a⁻¹ • x) k hk l hl hm hcard
  have he : (⟨k ^ l, hm⟩ : H) =
      ⟨a⁻¹ * g ^ Function.minimalPeriod (g • ·) (a : G ⧸ H) * a,
        conj_pow_minimalPeriod_mem H g a⟩ := Subtype.ext hp
  rw [he] at hrot
  exact hrot

end HodgeLean.Foundations.Program
