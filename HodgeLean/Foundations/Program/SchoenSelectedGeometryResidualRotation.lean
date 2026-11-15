import HodgeLean.Foundations.Program.SchoenSelectedGeometryRamifiedMultiplier
import HodgeLean.Foundations.Program.SchoenSelectedGeometryRotationPower
import HodgeLean.Foundations.Program.SchoenSelectedGeometryMonodromy

noncomputable section
set_option maxHeartbeats 400000
open Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- Positive rotation generators descend through a normal subgroup quotient. -/
theorem s0_residual_rotation
    {C H : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Group H] [Finite H] [MulAction H C] [FaithfulSMul H C]
    (hH : ∀ h : H, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : C ↦ h • z))
    (K : Subgroup H) [K.Normal]
    [ChartedSpace ℂ (rsq_Quot K C)] [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot K C)]
    (hq : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (rsq_proj K C))
    (hA : ∀ a : H ⧸ K, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun z : rsq_Quot K C ↦ a • z))
    (x : C) (r : H) (hr : b4_IsRotGen ℂ x r) :
    b4_IsRotGen ℂ (rsq_proj K C x) (QuotientGroup.mk r : H ⧸ K) := by
  letI : T2Space (rsq_Quot K C) := rsq_t2Space (Module.finrank_self ℂ)
    (fun k : K ↦ (hH k).continuous)
  have hgen := RiemannRochTop_rotGen_zpowers x r hr
  have hord : orderOf (QuotientGroup.mk r : H ⧸ K) =
      Nat.card (MulAction.stabilizer (H ⧸ K) (rsq_proj K C x)) := by
    rw [s0_residual_stabilizer_eq_image, ← hgen, MonoidHom.map_zpowers, Nat.card_zpowers]
    rfl
  refine ⟨?_, hord, ?_⟩
  · change rsq_proj K C (r • x) = rsq_proj K C x
    rw [hr.1]
  · intro v
    have hn := b4cov_nonconst_of_galois (Module.finrank_self ℂ)
      (rsq_proj K C) (rsq_proj_isGaloisCover K C) x
    have hm := s0_ramified_action_multiplier hH hA (rsq_proj K C) hq hn x r
      (QuotientGroup.mk r) hr.1 (fun z ↦ rfl)
    have he := b4cov_ramIndex_galois (Module.finrank_self ℂ) (Module.finrank_self ℂ)
      (fun k : K ↦ hH k) (rsq_proj K C) hq (rsq_proj_isGaloisCover K C) x
    have hl := b4cov_lam_eq_of_apply (Module.finrank_self ℂ) x r _ hr.2.2
    rw [he, hl, hr.2.1, ← rsq_card_stabilizer_quotient K x] at hm
    rw [s0_positive_rotation_power _ _ Nat.card_pos.ne' Nat.card_pos.ne'] at hm
    change b4cov_der ℂ (rsq_proj K C x) (QuotientGroup.mk r) v = _
    rw [b4cov_der_apply (Module.finrank_self ℂ), hm, hord]

#print axioms s0_residual_rotation
end HodgeLean.Foundations.Program
