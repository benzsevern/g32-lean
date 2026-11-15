import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.PowerProjectionFibres

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Every nonzero fibre of the weighted power projection has all labels and exactly the power-degree roots on each label. -/
def weightedPowerNonzeroFibreEquiv
    (g n : ℕ) (hn : 0 < n) (k : ZMod g → ℂ) (hk : ∀ j, k j ≠ 0)
    (b : ℂ) (hb : b ≠ 0) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ n) :
    {z : ZMod g × ℂ // k z.1 * z.2 ^ n = b} ≃ (ZMod g × ZMod n) := by
  choose κ hκ using fun j : ZMod g => IsAlgClosed.exists_pow_nat_eq (b / k j) hn
  have hκ0 (j : ZMod g) : κ j ≠ 0 := by
    intro hz
    have he := hκ j
    rw [hz, zero_pow (Nat.ne_of_gt hn)] at he
    exact div_ne_zero hb (hk j) he.symm
  let H (j : ZMod g) := binomialRootHomeomorph n hn (κ j) ζ (hκ0 j) hζ
  have hpow (z : {z : ZMod g × ℂ // k z.1 * z.2 ^ n = b}) :
      z.val.2 ^ n = κ z.val.1 ^ n := by
    rw [hκ]
    apply (eq_div_iff (hk z.val.1)).mpr
    rw [mul_comm]
    exact z.property
  let f : {z : ZMod g × ℂ // k z.1 * z.2 ^ n = b} → ZMod g × ZMod n :=
    fun z => (z.val.1, H z.val.1 ⟨z.val.2, hpow z⟩)
  let inv : ZMod g × ZMod n → {z : ZMod g × ℂ // k z.1 * z.2 ^ n = b} :=
    fun z => ⟨(z.1, ((H z.1).symm z.2).val), by
      change k z.1 * ((H z.1).symm z.2).val ^ n = b
      rw [((H z.1).symm z.2).property, hκ, mul_comm, div_mul_cancel₀ _ (hk z.1)]⟩
  refine { toFun := f, invFun := inv, left_inv := ?_, right_inv := ?_ }
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    exact congrArg Subtype.val ((H z.val.1).symm_apply_apply ⟨z.val.2, hpow z⟩)
  · intro z
    apply Prod.ext
    · rfl
    exact (H z.1).apply_symm_apply z.2

end AlgebraicGeometry.RamifiedNormalization.StageFour
