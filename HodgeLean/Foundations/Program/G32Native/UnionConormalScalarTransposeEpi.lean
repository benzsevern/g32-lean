import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Epimorphy and scalar-extension transposition along quotient maps -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- Along a surjective ring map, an epic scalar-extension arrow has epic transpose. -/
lemma unionConormal_scalarTranspose_epi
    (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (M : ModuleCat R) (N : ModuleCat S)
    (v : (ModuleCat.extendScalars φ).obj M ⟶ N) [Epi v] :
    Epi ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _ v) := by
  let S₀ := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)
  let w := (ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N v
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro y
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective v).mp inferInstance y
  change ∃ m : M, w.hom m = v.hom z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, w.hom.map_zero.trans v.hom.map_zero.symm⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, (w.hom.map_add a b).trans
      ((congrArg₂ (· + ·) ha hb).trans (v.hom.map_add x y).symm)⟩
  | tmul s m =>
    obtain ⟨r, hr⟩ := hφ s
    refine ⟨r • m, ?_⟩
    change v.hom ((show S₀ from (1 : S)) ⊗ₜ[R] (r • m)) = v.hom (s ⊗ₜ[R] m)
    congr 1
    rw [TensorProduct.tmul_smul]
    change (show S₀ from φ r * 1) ⊗ₜ[R] m = s ⊗ₜ[R] m
    exact congrArg (fun z : S₀ => z ⊗ₜ[R] m) ((mul_one (φ r)).trans hr)

#print axioms unionConormal_scalarTranspose_epi
end HodgeLean.Foundations.Program.G32Native
