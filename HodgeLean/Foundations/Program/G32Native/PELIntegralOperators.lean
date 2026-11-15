import HodgeLean.Foundations.Program.G32Native.PELIntegralDual

noncomputable section
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- Pullback by an integral homology operator preserves the original integral dual.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§1.2–1.3. -/
theorem integralDual_comp {Λ : Type} [AddCommGroup Λ]
    (T : Λ →ₗ[ℤ] Λ) {f : b2b_dual Λ} (hf : f ∈ integralDual Λ) :
    f.comp T ∈ integralDual Λ := by
  intro x
  exact hf (T x)

/-- Integer-valued rational functionals separate a finite free lattice.
Source: Birkenhake–Lange, Complex Abelian Varieties, §1.3 (dual lattices). -/
theorem integralDual_separates {Λ : Type} [AddCommGroup Λ]
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Λ) {x y : Λ}
    (h : ∀ f ∈ integralDual Λ, f x = f y) : x = y := by
  apply b.repr.injective
  ext i
  let f : b2b_dual Λ := (Int.castAddHom ℚ).toIntLinearMap.comp (b.coord i)
  have hf : f ∈ integralDual Λ := fun z => ⟨b.coord i z, rfl⟩
  have hi := h f hf
  change ((b.repr x i : ℤ) : ℚ) = ((b.repr y i : ℤ) : ℚ) at hi
  exact_mod_cast hi

#print axioms integralDual_comp
#print axioms integralDual_separates
end HodgeLean.Foundations.Program.GeneralTypeIII
