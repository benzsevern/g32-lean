import HodgeLean.Foundations.Program.SchoenCycleC1FieldSourceGenericSectionMap
import HodgeLean.Foundations.Program.SchoenCycleC1FieldSourceNormalization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The original generic factorization supplies the scalar tower for signed
cancellation on an actual affine normalization chart. The degree is read from
the specified power basis and nonvanishing from the original section. -/
theorem s2e_c1_generic_field_normalization_etale
    (L : Type) [Field L] (X : Scheme) [IsIntegral X] [IsAffine X]
    [IsIntegrallyClosed Γ(X, ⊤)] [CharZero X.functionField]
    (η : Spec (CommRingCat.of L) ⟶ X) [QuasiCompact η] [QuasiSeparated η]
    (φ : X.functionField →+* L)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X) = η) :
    letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
    letI := φ.toAlgebra
    ∀ (B : PowerBasis X.functionField L) (a b : ℤ) (m : ℕ),
      0 < m → B.dim = m → (m : ℤ) ∣ a + b →
      ∀ x : Γ(X, ⊤), x ≠ 0 →
      ∀ v u d : Γ(X, ⊤)ˣ, (d : Γ(X, ⊤)) = (m : Γ(X, ⊤)) →
      B.gen ^ m = φ
        ((X.germToFunctionField ⊤ x) ^ a *
          (X.germToFunctionField ⊤ x * X.germToFunctionField ⊤ (v : Γ(X, ⊤))) ^ b *
          X.germToFunctionField ⊤ (u : Γ(X, ⊤))) →
      Etale η.fromNormalization := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
  letI := φ.toAlgebra
  intro B a b m hm hdim hab x hx v u d hd hz
  letI : Algebra Γ(X, ⊤) L :=
    ((Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.comp η.appTop.hom).toAlgebra
  haveI : IsScalarTower Γ(X, ⊤) X.functionField L :=
    IsScalarTower.of_algebraMap_eq'
      (s2e_c1_field_source_generic_section_map L X η φ hφ).symm
  haveI : IsFractionRing Γ(X, ⊤) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  letI : Module.Finite X.functionField L := B.finite
  have hdim' : Module.finrank X.functionField L = m := B.finrank.trans hdim
  have hx' : algebraMap Γ(X, ⊤) X.functionField x ≠ 0 :=
    fun h => hx (by simpa using h)
  exact s2e_c1_field_source_normalization_etale L η X.functionField
    B a b m hm hdim' hab x hx' v u d hd hz

end HodgeLean.Foundations.Program
