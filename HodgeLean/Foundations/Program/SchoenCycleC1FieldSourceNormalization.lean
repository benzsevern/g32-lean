import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationFieldCoordinateTransport

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Signed paired cancellation on an actual affine chart with the original
field spectrum as source uses its canonical section map, without a supplied
section-ring identification or field structure on sections. -/
theorem s2e_c1_field_source_normalization_etale
    (L : Type) [Field L] {X : Scheme} [IsAffine X]
    (f : Spec (CommRingCat.of L) ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDomain Γ(X, ⊤)] [IsIntegrallyClosed Γ(X, ⊤)]
    (K : Type*) [Field K] [Algebra Γ(X, ⊤) K] [IsFractionRing Γ(X, ⊤) K] :
    letI : Algebra Γ(X, ⊤) L :=
      ((Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.comp f.appTop.hom).toAlgebra
    ∀ [Algebra K L] [IsScalarTower Γ(X, ⊤) K L] [Algebra.IsSeparable K L]
      (B : PowerBasis K L) (a b : ℤ) (m : ℕ),
      0 < m → Module.finrank K L = m → (m : ℤ) ∣ a + b →
      ∀ x : Γ(X, ⊤), algebraMap Γ(X, ⊤) K x ≠ 0 →
      ∀ v u d : Γ(X, ⊤)ˣ, (d : Γ(X, ⊤)) = (m : Γ(X, ⊤)) →
      B.gen ^ m = algebraMap K L
        ((algebraMap Γ(X, ⊤) K x) ^ a *
          (algebraMap Γ(X, ⊤) K x * algebraMap Γ(X, ⊤) K (v : Γ(X, ⊤))) ^ b *
          algebraMap Γ(X, ⊤) K (u : Γ(X, ⊤))) →
      Etale f.fromNormalization := by
  letI : Algebra Γ(X, ⊤) L :=
    ((Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.comp f.appTop.hom).toAlgebra
  intro hKL ht hs B a b m hm hdim hab x hx v u d hd hz
  exact s2e_c1_affine_normalization_etale_in_original_field f K L
    (Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv (fun _ => rfl)
    B a b m hm hdim hab x hx v u d hd hz

end HodgeLean.Foundations.Program
