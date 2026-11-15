import HodgeLean.Foundations.Program.G32Native.ProjectiveKernelBundleComparison

/-! # Inverse transport on the literal kernel support pair -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace Bundle
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native
open EulerModel
namespace ProjectiveKernelBundleComparison
variable {B : Type} [TopologicalSpace B] {k : ℕ} {E : B → Type}
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    (D : ProjectiveKernelBundleComparison k E)

/-- The specified homeomorphism identifies the two actual zero-complement pairs. -/
def pairIso : TopPair.ofSubset (X := i1_totalSpace k E) (i1_zeroSupport k E)ᶜ ≅
    TopPair.ofSubset (X := TopCat.of (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0}ᶜ :=
  TopPair.isoOfSubset D.total (fun z => not_congr (D.zero_iff z))

/-- Forward transport uses the original specified pair map. -/
theorem pairIso_hom : D.pairIso.hom = D.pairMap := rfl

/-- The inverse total map retains the specified inverse base point. -/
theorem inverse_base (z : ProjectiveNormalTotalSpace k) :
    (D.total.symm z).proj = D.base.symm z.1.1 := by
  apply D.base.injective
  rw [D.base.apply_symm_apply, ← D.base_eq, D.total.apply_symm_apply]

/-- The inverse total map is precisely the inverse of the supplied linear fibre map. -/
theorem inverse_fibre (b : B) (v : projectiveNormalKernel k (D.base b)) :
    D.total.symm ⟨(D.base b, v.1), v.2⟩ =
      (⟨b, (D.fibre b).symm v⟩ : TotalSpace (Fin k → ℂ) E) := by
  apply D.total.injective
  rw [D.total.apply_symm_apply]
  apply Subtype.ext
  apply Prod.ext
  · exact (D.base_eq ⟨b, (D.fibre b).symm v⟩).symm
  · rw [D.vector_eq]
    exact congrArg Subtype.val ((D.fibre b).apply_symm_apply v).symm

end ProjectiveKernelBundleComparison
#print axioms ProjectiveKernelBundleComparison.pairIso
#print axioms ProjectiveKernelBundleComparison.inverse_fibre
end HodgeLean.Foundations.Program.G32Native
