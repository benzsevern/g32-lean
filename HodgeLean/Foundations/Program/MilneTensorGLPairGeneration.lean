import HodgeLean.Foundations.Program.MilneTensorGLPairProducts
import HodgeLean.Foundations.Program.MilneTensorCopyGeneration

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem m1b_glPairIn_invariant_products (k : ℕ)
    (t : SchurWeyl.MixedTensor ℂ W (Fin k) (Fin k))
    (ht : t ∈ (SchurWeyl.mixedRep ℂ W (Fin k) (Fin k)).invariants) :
    m1b_glPairIn k t ∈
      m1b_products (m1b_fixed (Set.range (m1b_vectorDualAction (W := W))) 2) (k * 2) := by
  rw [SchurWeyl.invariants_mixedRep_eq_span_contraction] at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨π, rfl⟩ := ht
    exact m1b_glPairIn_contraction_products k π
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ihx => rw [map_smul]; exact Submodule.smul_mem _ c ihx

theorem m1b_glMixedReindex_action {ι κ ι' κ' : Type*}
    [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (e : ι ≃ ι') (d : κ ≃ κ') (g : LinearMap.GeneralLinearGroup ℂ W)
    (t : SchurWeyl.MixedTensor ℂ W ι κ) :
    InvariantsExterior.mixedReindex e d (SchurWeyl.mixedRep ℂ W ι κ g t) =
      SchurWeyl.mixedRep ℂ W ι' κ' g (InvariantsExterior.mixedReindex e d t) := by
  classical
  suffices h : (InvariantsExterior.mixedReindex (K := ℂ) (W := W) e d).toLinearMap.comp
      (SchurWeyl.mixedRep ℂ W ι κ g) =
      (SchurWeyl.mixedRep ℂ W ι' κ' g).comp
        (InvariantsExterior.mixedReindex e d).toLinearMap from LinearMap.congr_fun h t
  apply TensorProduct.ext
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro φ
  change InvariantsExterior.mixedReindex e d
      (SchurWeyl.mixedRep ℂ W ι κ g ((⨂ₜ[ℂ] i, v i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, φ i))) =
    SchurWeyl.mixedRep ℂ W ι' κ' g
      (InvariantsExterior.mixedReindex e d ((⨂ₜ[ℂ] i, v i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, φ i)))
  simp only [SchurWeyl.mixedRep_tmul_tprod, InvariantsExterior.mixedReindex,
    TensorProduct.congr_tmul, PiTensorProduct.reindex_tprod]

theorem m1b_gl_colored_fixed (n : ℕ) (t : ⨂[ℂ]^n (W × Module.Dual ℂ W))
    (ht : t ∈ m1b_fixed (Set.range (m1b_vectorDualAction (W := W))) n)
    (s : Finset (Fin n)) :
    InvariantsExterior.coloredWordOut s t ∈
      (SchurWeyl.mixedRep ℂ W {i // i ∈ s} {i // i ∉ s}).invariants := by
  classical
  intro g
  have h : SchurWeyl.tensorPow (Fin n) (m1b_vectorDualAction g) t = t := by
    have hfixed : ∀ u ∈ Set.range (m1b_vectorDualAction (W := W)),
        SchurWeyl.tensorPow (Fin n) u t = t := by
      simpa only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
        LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] using ht
    exact hfixed _ ⟨g, rfl⟩
  change TensorProduct.map _ _ (InvariantsExterior.coloredWordOut s t) = _
  rw [← m1b_coloredWordOut_tensorPow]
  exact congrArg (InvariantsExterior.coloredWordOut s) h

end HodgeLean.Foundations.Program
