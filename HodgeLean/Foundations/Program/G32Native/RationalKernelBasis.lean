import HodgeLean.Foundations.Program.G32Native.CyclotomicSpan
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Rational coefficient bases retaining the prescribed finite orbit -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped TensorProduct BigOperators
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.G32Native.TowerOrbit

/-- A rational basis of the kernel retains coefficients in the supplied finite spanning family. -/
theorem rational_kernel_basis
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (T : Module.End ℚ V) (m : ℕ) (hm : 0 < m) (s : Fin m → V)
    (hrank : Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval T (Polynomial.cyclotomic m ℚ))) = Nat.totient m)
    (hspan : LinearMap.ker (Polynomial.aeval T (Polynomial.cyclotomic m ℚ)) ≤
      Submodule.span ℚ (Set.range s)) :
    ∃ (a : Fin (Nat.totient m) → Fin m → ℚ) (v : Fin (Nat.totient m) → V),
      LinearIndependent ℚ v ∧
      Submodule.span ℚ (Set.range v) = LinearMap.ker
        (Polynomial.aeval T (Polynomial.cyclotomic m ℚ)) ∧
      (∀ j, v j = ∑ t, a j t • s t) ∧
      ∀ (ζ : ℂ), IsPrimitiveRoot ζ m → ∀ u : ℂ ⊗[ℚ] V,
        T.baseChange ℂ u = ζ • u →
        ∃ b : Fin (Nat.totient m) → ℂ,
          u = ∑ j, b j • TensorProduct.tmul ℚ (1 : ℂ) (v j) := by
  classical
  let K := LinearMap.ker (Polynomial.aeval T (Polynomial.cyclotomic m ℚ))
  let B := Module.finBasisOfFinrankEq ℚ K hrank
  let v : Fin (Nat.totient m) → V := fun j => B j
  have hvlin : LinearIndependent ℚ v := B.linearIndependent.map' K.subtype (LinearMap.ker_eq_bot.mpr K.subtype_injective)
  have hvspan : Submodule.span ℚ (Set.range v) = K := by
    have he := congrArg (Submodule.map K.subtype) B.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at he
    simpa only [← Set.range_comp, v, Function.comp_def, Submodule.subtype_apply] using he
  have hcoeff (j : Fin (Nat.totient m)) : ∃ a : Fin m → ℚ, v j = ∑ t, a t • s t := by
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp
      (hspan (B j).property)
    exact ⟨a, ha.symm⟩
  choose a ha using hcoeff
  refine ⟨a, v, hvlin, hvspan, ha, ?_⟩
  intro ζ hζ u hu
  have hKu : u ∈ K.baseChange ℂ := by
    change u ∈ (isotypic T m).baseChange ℂ
    rw [baseChange_isotypic T hm]
    exact Submodule.mem_iSup_of_mem ζ
      (Submodule.mem_iSup_of_mem ((mem_primitiveRoots hm).mpr hζ)
        (Module.End.mem_eigenspace_iff.mpr hu))
  rw [← hvspan, Submodule.baseChange_span, ← Set.range_comp] at hKu
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hKu
  exact ⟨b, hb.symm⟩

#print axioms rational_kernel_basis
end HodgeLean.Foundations.Program.G32Native.TowerOrbit
