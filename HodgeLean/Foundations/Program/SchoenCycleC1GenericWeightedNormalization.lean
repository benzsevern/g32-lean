import HodgeLean.Foundations.Program.SchoenCycleC1GenericFieldNormalization
import HodgeLean.Foundations.Program.SchoenCycleC1WeightedSignedUnit

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Weighted signed coefficient cancellation concerns the actual relative
normalization in the original covering field and requires no factorial
presentation of the affine section ring. -/
theorem s2e_c1_generic_weighted_normalization_etale
    (L : Type) [Field L] (X : Scheme) [IsIntegral X] [IsAffine X]
    [IsIntegrallyClosed Γ(X, ⊤)] [CharZero X.functionField]
    (η : Spec (CommRingCat.of L) ⟶ X) [QuasiCompact η] [QuasiSeparated η]
    (φ : X.functionField →+* L)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X) = η) :
    letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
    letI := φ.toAlgebra
    ∀ (B : PowerBasis X.functionField L) (m : ℕ), 0 < m → B.dim = m →
      ∀ (J : Type) [Fintype J] (g : J → Γ(X, ⊤)), (∀ j, g j ≠ 0) →
      ∀ (k : J → ℕ) (n : J → ℤ) (E : Γ(X, ⊤)) (s : ℤ),
      (∀ j, (m : ℤ) ∣ n j - s * (k j : ℤ)) →
      (∏ j, (Ideal.span {g j}) ^ k j) = (Ideal.span {E}) ^ m →
      ∀ u d : Γ(X, ⊤)ˣ, (d : Γ(X, ⊤)) = (m : Γ(X, ⊤)) →
      B.gen ^ m = φ (X.germToFunctionField ⊤ (u : Γ(X, ⊤)) *
        ∏ j, (X.germToFunctionField ⊤ (g j)) ^ n j) →
      Etale η.fromNormalization := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
  letI := φ.toAlgebra
  intro B m hm hdim J hJ g hg k n E s hn hI u d hd hroot
  haveI : IsFractionRing Γ(X, ⊤) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  obtain ⟨a, v, ha, he⟩ := s2e_c1_weighted_signed_unit (K := X.functionField)
    g hg k n E s m hm hn hI u
  change B.gen ^ m = φ (algebraMap Γ(X, ⊤) X.functionField (u : Γ(X, ⊤)) *
    ∏ j, (algebraMap Γ(X, ⊤) X.functionField (g j)) ^ n j) at hroot
  rw [he] at hroot
  obtain ⟨C, hgen, _⟩ := s2e_c1_divided_powerBasis B m hm (B.finrank.trans hdim)
    a (algebraMap Γ(X, ⊤) X.functionField (v : Γ(X, ⊤))) ha hroot
  have hpower : C.gen ^ m = φ (algebraMap Γ(X, ⊤) X.functionField (v : Γ(X, ⊤))) := by
    rw [hgen, div_pow, hroot, map_mul, map_pow]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ ((map_ne_zero φ).mpr ha))
  apply s2e_c1_generic_field_normalization_etale L X η φ hφ C 0 0 m hm
    (C.finrank.symm.trans (B.finrank.trans hdim)) (dvd_zero _) 1 one_ne_zero 1 v d hd
  simp only [zpow_zero, one_mul]
  exact hpower

end HodgeLean.Foundations.Program
