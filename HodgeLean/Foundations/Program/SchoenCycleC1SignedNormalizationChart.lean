import HodgeLean.Foundations.Program.SchoenCycleC1SignedPairedClosure
import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationEtaleCharts

/-! # Signed paired cancellation on an actual affine normalization chart -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A signed paired power equation for the actual section pullback gives
etaleness of its affine relative normalization projection. -/
theorem s2e_c1_affine_normalization_etale_of_signed_paired_equation
    {T X : Scheme} [IsAffine X] (f : T ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDomain Γ(X, ⊤)] [IsIntegrallyClosed Γ(X, ⊤)]
    (hL : IsField Γ(T, f ⁻¹ᵁ ⊤))
    (K : Type*) [Field K] [Algebra Γ(X, ⊤) K] [IsFractionRing Γ(X, ⊤) K] :
    letI := hL.toField
    letI := (f.app ⊤).hom.toAlgebra
    ∀ [Algebra K Γ(T, f ⁻¹ᵁ ⊤)] [IsScalarTower Γ(X, ⊤) K Γ(T, f ⁻¹ᵁ ⊤)]
      [Algebra.IsSeparable K Γ(T, f ⁻¹ᵁ ⊤)]
      (B : PowerBasis K Γ(T, f ⁻¹ᵁ ⊤)) (a b : ℤ) (m : ℕ),
      0 < m → Module.finrank K Γ(T, f ⁻¹ᵁ ⊤) = m → (m : ℤ) ∣ a + b →
      ∀ x : Γ(X, ⊤), algebraMap Γ(X, ⊤) K x ≠ 0 →
      ∀ v u d : Γ(X, ⊤)ˣ, (d : Γ(X, ⊤)) = (m : Γ(X, ⊤)) →
      B.gen ^ m = algebraMap K Γ(T, f ⁻¹ᵁ ⊤)
        ((algebraMap Γ(X, ⊤) K x) ^ a *
          (algebraMap Γ(X, ⊤) K x * algebraMap Γ(X, ⊤) K (v : Γ(X, ⊤))) ^ b *
          algebraMap Γ(X, ⊤) K (u : Γ(X, ⊤))) →
      Etale f.fromNormalization := by
  letI := hL.toField
  letI := (f.app ⊤).hom.toAlgebra
  intro hKL ht hs B a b m hm hdim hab x hx v u d hd hz
  apply s2e_c1_affine_normalization_etale_of_integralClosure f
  exact s2e_c1_signed_paired_integralClosure_etale B a b m hm hdim hab x hx v u d hd hz

end HodgeLean.Foundations.Program
