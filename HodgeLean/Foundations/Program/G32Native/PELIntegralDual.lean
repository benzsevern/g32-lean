import HodgeLean.Foundations.Program.G32Native.WeilMarkedRationalComparison

noncomputable section
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The integral dual inside the rational dual, using the original lattice.
Source: Birkenhake–Lange, Complex Abelian Varieties, §1.3 (dual lattices). -/
def integralDual (Λ : Type) [AddCommGroup Λ] : Submodule ℤ (b2b_dual Λ) where
  carrier := {f | ∀ x, ∃ z : ℤ, f x = (z : ℚ)}
  zero_mem' := fun _ => ⟨0, rfl⟩
  add_mem' := by
    intro f g hf hg x
    obtain ⟨a, ha⟩ := hf x
    obtain ⟨b, hb⟩ := hg x
    exact ⟨a + b, by simp only [LinearMap.add_apply, ha, hb, Int.cast_add]⟩
  smul_mem' := by
    intro a f hf x
    obtain ⟨b, hb⟩ := hf x
    exact ⟨a * b, by simp only [LinearMap.smul_apply, hb, zsmul_eq_mul, Int.cast_mul]⟩

/-- An integral marking transports the entire integral dual, with no denominator
clearing or replacement by a commensurable lattice.
Source: Birkenhake–Lange, Complex Abelian Varieties, §1.3 (dual lattices). -/
theorem integralDual_precomp {Λ M : Type} [AddCommGroup Λ] [AddCommGroup M]
    (e : Λ ≃+ M) (f : b2b_dual Λ) :
    (f.comp e.symm.toIntLinearEquiv.toLinearMap) ∈ integralDual M ↔
      f ∈ integralDual Λ := by
  constructor
  · intro h x
    have hx := h (e x)
    change ∃ z : ℤ, f (e.symm (e x)) = (z : ℚ) at hx
    simpa only [AddEquiv.symm_apply_apply] using hx
  · intro h x
    exact h (e.symm x)

#print axioms integralDual
#print axioms integralDual_precomp
end HodgeLean.Foundations.Program.GeneralTypeIII
