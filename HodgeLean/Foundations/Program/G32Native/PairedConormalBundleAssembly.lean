import HodgeLean.Foundations.Program.G32Native.PairedConormalBundleRecovery
import HodgeLean.Foundations.Program.G32Native.ProjectiveKernelBundleComparison

/-! # Assemble the actual projective kernel bundle from continuous linear observations -/

noncomputable section
set_option maxHeartbeats 200000
open Bundle Topology
namespace HodgeLean.Foundations.Program.G32Native
open EulerModel

/-- The continuous forward fibre identification determines the entire bundle
homeomorphism; inverse continuity follows from linear recovery in bundle charts. -/
def projectiveKernelBundleComparisonOfContinuousFibres
    {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (e : B ≃ₜ Projectivization ℂ (ℂ × (Fin k → ℂ)))
    (φ : ∀ b, E b ≃ₗ[ℂ] projectiveNormalKernel k (e b))
    (hφ : Continuous (fun z : TotalSpace (Fin k → ℂ) E => (φ z.proj z.2).val)) :
    ProjectiveKernelBundleComparison k E := by
  let F : TotalSpace (Fin k → ℂ) E → ProjectiveNormalTotalSpace k := fun z =>
    ⟨(e z.proj, (φ z.proj z.2).val), (φ z.proj z.2).property⟩
  have hFi : Function.Injective F := by
    rintro ⟨b, v⟩ ⟨c, w⟩ h
    have hb : b = c := e.injective (congrArg (fun z => z.val.1) h)
    subst c
    have hv : φ b v = φ b w := Subtype.ext (congrArg (fun z => z.val.2) h)
    have hvw := (φ b).injective hv
    subst w
    rfl
  have hFs : Function.Surjective F := by
    rintro ⟨⟨p, w⟩, hw⟩
    obtain ⟨b, rfl⟩ := e.surjective p
    refine ⟨⟨b, (φ b).symm ⟨w, hw⟩⟩, ?_⟩
    apply Subtype.ext
    change (e b, (φ b ((φ b).symm ⟨w, hw⟩)).val) = (e b, w)
    rw [LinearEquiv.apply_symm_apply]
  let T := Equiv.ofBijective F ⟨hFi, hFs⟩
  have hbase (w : ProjectiveNormalTotalSpace k) :
      (T.symm w).proj = e.symm w.val.1 := by
    have h := congrArg (fun z => z.val.1) (T.apply_symm_apply w)
    change e (T.symm w).proj = w.val.1 at h
    simpa only [Homeomorph.symm_apply_apply] using congrArg e.symm h
  have hvector (w : ProjectiveNormalTotalSpace k) :
      (φ (T.symm w).proj (T.symm w).2).val = w.val.2 := by
    exact congrArg (fun z => z.val.2) (T.apply_symm_apply w)
  let J : ∀ b, E b →ₗ[ℂ] (ℂ × (Fin k → ℂ)) := fun b =>
    (projectiveNormalKernel k (e b)).subtype.comp (φ b).toLinearMap
  have hJi (b : B) : Function.Injective (J b) :=
    Subtype.val_injective.comp (φ b).injective
  have hbaseInv : Continuous (fun w : ProjectiveNormalTotalSpace k => (T.symm w).proj) :=
    (e.symm.continuous.comp (continuous_fst.comp continuous_subtype_val)).congr
      (fun w => (hbase w).symm)
  have hobsInv : Continuous (fun w : ProjectiveNormalTotalSpace k =>
      J (T.symm w).proj (T.symm w).2) :=
    (continuous_snd.comp continuous_subtype_val).congr (fun w => (hvector w).symm)
  have hInv : Continuous T.symm :=
    paired_bundle_continuous_of_observations E J hφ hJi T.symm hbaseInv hobsInv
  have hF : Continuous F :=
    ((e.continuous.comp (FiberBundle.continuous_proj (Fin k → ℂ) E)).prodMk hφ).subtype_mk _
  exact
    { base := e
      fibre := φ
      total := { toEquiv := T, continuous_toFun := hF, continuous_invFun := hInv }
      base_eq := fun _ => rfl
      vector_eq := fun _ => rfl }

#print axioms projectiveKernelBundleComparisonOfContinuousFibres
end HodgeLean.Foundations.Program.G32Native
