import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- A primitive complex root supplies a cyclic unit-valued character with that generator value. -/
theorem s2v_l1b_divisor_character_of_primitive_root
    {m : ℕ} (hm : m ≠ 0) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) :
    ∃ χ : Multiplicative (ZMod m) →* ℂˣ,
      (χ (.ofAdd (1 : ZMod m)) : ℂ) = ζ := by
  let ζu : ℂˣ := Units.mk0 ζ (hζ.ne_zero hm)
  have hζu : IsPrimitiveRoot ζu m := IsPrimitiveRoot.coe_units_iff.mp hζ
  let E := hζu.zmodEquivZPowers
  let χ : Multiplicative (ZMod m) →* ℂˣ :=
    (Subgroup.zpowers ζu).subtype.comp
      (AddMonoidHom.toMultiplicativeLeft E.toAddMonoidHom)
  refine ⟨χ, ?_⟩
  change (((E (1 : ZMod m)).toMul : ℂˣ) : ℂ) = ζ
  have H : E (1 : ZMod m) = Additive.ofMul (⟨ζu, (1 : ℤ), by simp⟩ : Subgroup.zpowers ζu) := by
    simpa only [Nat.cast_one, pow_one] using hζu.zmodEquivZPowers_apply_coe_nat 1
  rw [H]
  rfl

end HodgeLean.Foundations.Program
