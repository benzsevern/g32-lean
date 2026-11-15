import HodgeLean.Foundations.CyclicAction
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # A dimension criterion for rational cyclotomic spanning -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.G32Native.TowerOrbit

/-- Independent primitive eigenvectors and the upper rank bound exhaust the rational kernel. -/
theorem cyclotomic_kernel_rank_and_span
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (T : Module.End ℚ V) (m : ℕ) (hm : 0 < m) (R : Submodule ℚ V)
    (hbound : Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval T (Polynomial.cyclotomic m ℚ))) ≤ Nat.totient m)
    (w : {ζ : ℂ // ζ ∈ primitiveRoots m ℂ} → ℂ ⊗[ℚ] V)
    (hw : ∀ ζ, T.baseChange ℂ (w ζ) = ζ.val • w ζ)
    (hne : ∀ ζ, w ζ ≠ 0) (hmem : ∀ ζ, w ζ ∈ R.baseChange ℂ) :
    Module.finrank ℚ (LinearMap.ker (Polynomial.aeval T (Polynomial.cyclotomic m ℚ))) = Nat.totient m ∧
      LinearMap.ker (Polynomial.aeval T (Polynomial.cyclotomic m ℚ)) ≤ R := by
  classical
  let K := LinearMap.ker (Polynomial.aeval T (Polynomial.cyclotomic m ℚ))
  let S := Submodule.span ℂ (Set.range w)
  have heig (ζ : {ζ : ℂ // ζ ∈ primitiveRoots m ℂ}) :
      Module.End.HasEigenvector (T.baseChange ℂ) ζ.val (w ζ) := by
    refine Module.End.hasEigenvector_iff.mpr ⟨?_, hne ζ⟩
    exact (Module.End.mem_eigenspace_iff (f := T.baseChange ℂ) (μ := ζ.val)).mpr (hw ζ)
  have hi : LinearIndependent ℂ w :=
    Module.End.eigenvectors_linearIndependent' (T.baseChange ℂ)
      (fun ζ : {ζ : ℂ // ζ ∈ primitiveRoots m ℂ} => ζ.val) Subtype.val_injective w heig
  have hdimS : Module.finrank ℂ S = Nat.totient m := by
    rw [finrank_span_eq_card hi]
    simp only [Fintype.card_coe]
    exact (Complex.isPrimitiveRoot_exp m hm.ne').card_primitiveRoots
  have hS : S ≤ K.baseChange ℂ := by
    change S ≤ (isotypic T m).baseChange ℂ
    rw [baseChange_isotypic T hm]
    apply Submodule.span_le.mpr
    rintro _ ⟨ζ, rfl⟩
    exact Submodule.mem_iSup_of_mem ζ.val
      (Submodule.mem_iSup_of_mem ζ.property ((Module.End.mem_eigenspace_iff (f := T.baseChange ℂ) (μ := ζ.val)).mpr (hw ζ)))
  have hdimK : Module.finrank ℂ (K.baseChange ℂ) = Module.finrank ℚ K := by
    have hiK : Function.Injective (K.subtype.baseChange ℂ) :=
      Module.Flat.lTensor_preserves_injective_linearMap K.subtype K.subtype_injective
    rw [Submodule.baseChange, LinearMap.finrank_range_of_inj hiK, Module.finrank_baseChange]
  have hrank : Module.finrank ℚ K = Nat.totient m := by
    apply le_antisymm hbound
    rw [← hdimK, ← hdimS]
    exact Submodule.finrank_mono hS
  have heq : S = K.baseChange ℂ := Submodule.eq_of_le_of_finrank_eq hS (by rw [hdimS, hdimK, hrank])
  refine ⟨hrank, ?_⟩
  apply (Submodule.baseChange_le_iff (A := ℂ)).mp
  rw [← heq]
  exact Submodule.span_le.mpr (fun _ ⟨ζ, he⟩ => he ▸ hmem ζ)

#print axioms cyclotomic_kernel_rank_and_span
end HodgeLean.Foundations.Program.G32Native.TowerOrbit
