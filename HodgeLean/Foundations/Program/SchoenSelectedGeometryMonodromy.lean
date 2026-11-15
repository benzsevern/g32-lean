import HodgeLean.Foundations.Program.RiemannSurfaceQuotient

noncomputable section
open scoped Manifold ContDiff
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s0_residual_stabilizer_eq_image
    {H X : Type} [Group H] [MulAction H X]
    (K : Subgroup H) [K.Normal] (x : X) :
    MulAction.stabilizer (H ⧸ K) (rsq_proj K X x) =
      (MulAction.stabilizer H x).map (QuotientGroup.mk' K) := by
  ext a
  constructor
  · intro ha
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective a
    change a • rsq_proj K X x = rsq_proj K X x at ha
    rw [← hh, rsq_quotAction_mk] at ha
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact ha)
    refine ⟨(k : H)⁻¹ * h, ?_, ?_⟩
    · change ((k : H)⁻¹ * h) • x = x
      rw [mul_smul, ← hk]
      simp only [Subgroup.smul_def, inv_smul_smul]
    · change (((k : H)⁻¹ * h : H) : H ⧸ K) = a
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        (QuotientGroup.eq_one_iff (k : H)).mpr k.property, inv_one, one_mul, hh]
  · rintro ⟨h, hh, rfl⟩
    change rsq_proj K X (h • x) = rsq_proj K X x
    rw [hh]

#print axioms s0_residual_stabilizer_eq_image

theorem s0_residual_stabilizer_trivial_iff
    {H X : Type} [Group H] [MulAction H X]
    (K : Subgroup H) [K.Normal] (x : X) :
    MulAction.stabilizer (H ⧸ K) (rsq_proj K X x) = ⊥ ↔
      MulAction.stabilizer H x ≤ K := by
  rw [s0_residual_stabilizer_eq_image, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

#print axioms s0_residual_stabilizer_trivial_iff

theorem s0_residual_branch_iff_character
    {H X A : Type} [Group H] [Group A] [MulAction H X]
    (χ : H →* A) (x : X) (r : H)
    (hr : MulAction.stabilizer H x = Subgroup.zpowers r) :
    MulAction.stabilizer (H ⧸ χ.ker) (rsq_proj χ.ker X x) ≠ ⊥ ↔ χ r ≠ 1 := by
  rw [ne_eq, s0_residual_stabilizer_trivial_iff, hr, Subgroup.zpowers_le]
  rfl

#print axioms s0_residual_branch_iff_character

theorem s0_residual_stabilizer_order
    {H X A : Type} [Group H] [Group A] [MulAction H X]
    (χ : H →* A) (hχ : Function.Surjective χ) (x : X) (r : H)
    (hr : MulAction.stabilizer H x = Subgroup.zpowers r) :
    Nat.card (MulAction.stabilizer (H ⧸ χ.ker) (rsq_proj χ.ker X x)) = orderOf (χ r) := by
  rw [s0_residual_stabilizer_eq_image, hr, MonoidHom.map_zpowers, Nat.card_zpowers]
  exact (QuotientGroup.quotientKerEquivOfSurjective χ hχ).orderOf_eq
    (QuotientGroup.mk r) |>.symm

#print axioms s0_residual_stabilizer_order

theorem s0_rotation_residual_stabilizer
    {H C A : Type} [Group H] [Finite H] [Group A] [MulAction H C]
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    (χ : H →* A) (hχ : Function.Surjective χ) (x : C) (r : H)
    (hr : b4_IsRotGen ℂ x r) :
    Nat.card (MulAction.stabilizer (H ⧸ χ.ker) (rsq_proj χ.ker C x)) = orderOf (χ r) ∧
      (MulAction.stabilizer (H ⧸ χ.ker) (rsq_proj χ.ker C x) ≠ ⊥ ↔ χ r ≠ 1) := by
  have hgen := (RiemannRochTop_rotGen_zpowers x r hr).symm
  exact ⟨s0_residual_stabilizer_order χ hχ x r hgen,
    s0_residual_branch_iff_character χ x r hgen⟩

#print axioms s0_rotation_residual_stabilizer

end HodgeLean.Foundations.Program
