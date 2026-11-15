import HodgeLean.Foundations.Program.G32Native.PELIntegralOperators

noncomputable section
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- Rationalize an integral functional without changing its values.
Source: Birkenhake–Lange, Complex Abelian Varieties, §1.3 (dual lattices). -/
def integralDualInclusion (Λ : Type) [AddCommGroup Λ] :
    (Λ →ₗ[ℤ] ℤ) →ₗ[ℤ] b2b_dual Λ where
  toFun f := (Int.castAddHom ℚ).toIntLinearMap.comp f
  map_add' _ _ := by ext; simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' _ _ := by ext; simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

/-- The integer-period condition is exactly the image of the integral dual.
This uses integer values on every lattice vector, without choosing a basis.
Source: Birkenhake–Lange, Complex Abelian Varieties, §1.3 (dual lattices). -/
theorem integralDual_range (Λ : Type) [AddCommGroup Λ] :
    (integralDualInclusion Λ).range = integralDual Λ := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩ x
    exact ⟨g x, rfl⟩
  · intro hf
    let g : Λ → ℤ := fun x => (hf x).choose
    have hg (x : Λ) : (g x : ℚ) = f x := (hf x).choose_spec.symm
    let G : Λ →ₗ[ℤ] ℤ :=
      { toFun := g
        map_add' := fun x y => by
          apply Int.cast_injective (α := ℚ)
          rw [Int.cast_add, hg, hg, hg, map_add]
        map_smul' := fun a x => by
          apply Int.cast_injective (α := ℚ)
          change (g (a • x) : ℚ) = ((a * g x : ℤ) : ℚ)
          rw [Int.cast_mul, hg, hg, map_smul, zsmul_eq_mul] }
    refine ⟨G, ?_⟩
    ext x
    exact hg x

/-- Rationalization is injective on the integral dual.
Source: Birkenhake–Lange, Complex Abelian Varieties, §1.3. -/
theorem integralDualInclusion_injective (Λ : Type) [AddCommGroup Λ] :
    Function.Injective (integralDualInclusion Λ) := by
  intro f g h
  ext x
  have hx := LinearMap.congr_fun h x
  exact Int.cast_injective (α := ℚ) hx

#print axioms integralDualInclusion
#print axioms integralDual_range
#print axioms integralDualInclusion_injective
end HodgeLean.Foundations.Program.GeneralTypeIII
