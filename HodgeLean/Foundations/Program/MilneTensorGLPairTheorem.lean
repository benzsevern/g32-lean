import HodgeLean.Foundations.Program.MilneTensorGLPairGeneration

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem m1b_products_reindex {U : Type*} [AddCommGroup U] [Module ℂ U]
    (Q : Submodule ℂ (⨂[ℂ]^2 U)) {k n : ℕ} (e : Fin k ≃ Fin n)
    (t : ⨂[ℂ]^k U) (ht : t ∈ m1b_products Q k) :
    PiTensorProduct.reindex ℂ (fun _ => U) e t ∈ m1b_products Q n := by
  have h : k = n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  exact m1b_products_perm Q k e t ht

theorem m1b_gl_colored_insert (n k : ℕ) (s : Finset (Fin n))
    (e : Fin k ≃ {i // i ∈ s}) (d : Fin k ≃ {i // i ∉ s})
    (t : SchurWeyl.MixedTensor ℂ W (Fin k) (Fin k)) :
    let u := (m1b_glPairSlots k).symm.trans
      ((Equiv.sumCongr e d).trans (Equiv.sumCompl (· ∈ s)))
    InvariantsExterior.coloredWordIn s (InvariantsExterior.mixedReindex e d t) =
      PiTensorProduct.reindex ℂ (fun _ => W × Module.Dual ℂ W) u (m1b_glPairIn k t) := by
  classical
  dsimp only
  suffices h : (InvariantsExterior.coloredWordIn s).comp
      (InvariantsExterior.mixedReindex (K := ℂ) (W := W) e d).toLinearMap =
      (PiTensorProduct.reindex ℂ (fun _ => W × Module.Dual ℂ W)
        ((m1b_glPairSlots k).symm.trans
          ((Equiv.sumCongr e d).trans (Equiv.sumCompl (· ∈ s))))).toLinearMap.comp
        (m1b_glPairIn k) from LinearMap.congr_fun h t
  apply TensorProduct.ext
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro φ
  change InvariantsExterior.coloredWordIn s
      (InvariantsExterior.mixedReindex e d ((⨂ₜ[ℂ] i, v i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, φ i))) =
    PiTensorProduct.reindex ℂ (fun _ => W × Module.Dual ℂ W)
      ((m1b_glPairSlots k).symm.trans
        ((Equiv.sumCongr e d).trans (Equiv.sumCompl (· ∈ s))))
      (m1b_glPairIn k ((⨂ₜ[ℂ] i, v i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, φ i)))
  simp only [InvariantsExterior.mixedReindex, TensorProduct.congr_tmul,
    PiTensorProduct.reindex_tprod, InvariantsExterior.coloredWordIn,
    LinearMap.comp_apply, InvariantsExterior.orderedWordIn, TensorProduct.map_tmul,
    PiTensorProduct.map_tprod, LinearEquiv.coe_coe, PiTensorProduct.tmulEquiv_apply,
    m1b_glPairIn_tprod, PiTensorProduct.reindex_tprod]
  congr 1
  funext i
  cases h : (Equiv.sumCompl (· ∈ s)).symm i <;> simp [h]

theorem m1b_vectorDual_generation (n : ℕ) :
    m1b_fixed (Set.range (m1b_vectorDualAction (W := W))) n =
      m1b_products (m1b_fixed (Set.range (m1b_vectorDualAction (W := W))) 2) n := by
  classical
  apply le_antisymm
  · intro t ht
    rw [← InvariantsExterior.sum_coloredWordIn_out t]
    apply Submodule.sum_mem
    intro s _
    let ι := {i : Fin n // i ∈ s}
    let κ := {i : Fin n // i ∉ s}
    have hw := m1b_gl_colored_fixed n t ht s
    by_cases hcard : Fintype.card ι = Fintype.card κ
    · let k := Fintype.card ι
      let e : Fin k ≃ ι := (Fintype.equivFin ι).symm
      let d : Fin k ≃ κ := (finCongr hcard).trans (Fintype.equivFin κ).symm
      let E := InvariantsExterior.mixedReindex (K := ℂ) (W := W) e d
      let z := E.symm (InvariantsExterior.coloredWordOut s t)
      have hz : z ∈ (SchurWeyl.mixedRep ℂ W (Fin k) (Fin k)).invariants := by
        intro g
        apply E.injective
        change E (SchurWeyl.mixedRep ℂ W (Fin k) (Fin k) g z) = E z
        rw [m1b_glMixedReindex_action, E.apply_symm_apply]
        exact hw g
      have hp := m1b_glPairIn_invariant_products k z hz
      have hins := m1b_gl_colored_insert n k s e d z
      dsimp only at hins
      rw [show InvariantsExterior.mixedReindex e d z =
        InvariantsExterior.coloredWordOut s t from E.apply_symm_apply _] at hins
      rw [hins]
      exact m1b_products_reindex _ _ _ hp
    · have hz : InvariantsExterior.coloredWordOut s t = 0 := by
        rw [SchurWeyl.invariants_mixedRep_eq_bot hcard] at hw
        exact hw
      rw [hz, map_zero]
      exact Submodule.zero_mem _
  · exact m1b_products_le_fixed _ n

theorem m1b_vectorDual_copies_generation (r n : ℕ) :
    m1b_fixed (m1b_copies r '' Set.range (m1b_vectorDualAction (W := W))) n =
      m1b_products (m1b_fixed
        (m1b_copies r '' Set.range (m1b_vectorDualAction (W := W))) 2) n :=
  m1b_copies_generation _ r n (m1b_vectorDual_generation n)

end HodgeLean.Foundations.Program
