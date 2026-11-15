import HodgeLean.Foundations.Program.SchoenCycleC1GenericWeightedNormalization
import HodgeLean.Foundations.Program.SchoenCycleC1GenericCoveringFieldSquare
import HodgeLean.Foundations.Program.SchoenCycleC1PartialIsoRationalEquivalence
import HodgeLean.Foundations.Program.SchoenCycleC1PowerBasisBaseFieldTransport

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Actual birational transport identifies the original primitive covering
coordinate with the weighted final chart calculation. The field embedding
and scalar compatibility are constructed from the retained source square. -/
theorem s2e_c1_retained_weighted_normalization_etale
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] [IsAffine X]
    [IsIntegrallyClosed Γ(X, ⊤)] [CharZero X.functionField]
    (f : X ⟶ Y) [IsDominant f] (P : X.PartialIso Y)
    (hP : P.iso.hom ≫ P.target.ι = P.source.ι ≫ f)
    (L : Type) [Field L] (ηX : Spec (CommRingCat.of L) ⟶ X)
    [IsDominant ηX] [QuasiCompact ηX] [QuasiSeparated ηX]
    (ηY : Spec (CommRingCat.of L) ⟶ Y) (hη : ηX ≫ f = ηY)
    (φY : Y.functionField →+* L)
    (hY : Spec.map (CommRingCat.ofHom φY) ≫ Y.fromSpecStalk (genericPoint Y) = ηY) :
    letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
    letI := φY.toAlgebra
    let hg := s2e_c1_dominant_generic_point f
    let ψ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫ f.stalkMap (genericPoint X)).hom
    ∀ (B : PowerBasis Y.functionField L) (c : Y.functionField) (m : ℕ),
      0 < m → B.dim = m → B.gen ^ m = φY c →
      ∀ (J : Type) [Fintype J] (g : J → Γ(X, ⊤)), (∀ j, g j ≠ 0) →
      ∀ (k : J → ℕ) (n : J → ℤ) (E : Γ(X, ⊤)) (s : ℤ),
      (∀ j, (m : ℤ) ∣ n j - s * (k j : ℤ)) →
      (∏ j, (Ideal.span {g j}) ^ k j) = (Ideal.span {E}) ^ m →
      ∀ u d : Γ(X, ⊤)ˣ, (d : Γ(X, ⊤)) = (m : Γ(X, ⊤)) →
      ψ c = X.germToFunctionField ⊤ (u : Γ(X, ⊤)) *
        ∏ j, (X.germToFunctionField ⊤ (g j)) ^ n j →
      Etale ηX.fromNormalization := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
  letI := φY.toAlgebra
  dsimp only
  intro B c m hm hdim hroot J hJ g hg k n E s hn hI u d hd hc
  obtain ⟨φX, _, hX⟩ := s2e_c1_field_source_generic_embedding L X ηX
  obtain ⟨F, hF, _⟩ := s2e_c1_partial_iso_rational_equivalence f P hP
  have hcomp := s2e_c1_generic_covering_field_square f L ηX ηY hη φX φY hX hY
  have hcompat : φX.comp F.toRingHom = φY := by rw [hF]; exact hcomp
  letI := φX.toAlgebra
  obtain ⟨C, hgen, hdimC, _⟩ := s2e_c1_power_basis_base_field_transport F
    (fun r => RingHom.congr_fun hcompat r) B
  apply s2e_c1_generic_weighted_normalization_etale L X ηX φX hX C m hm
    (hdimC.trans hdim) J g hg k n E s hn hI u d hd
  rw [hgen, hroot, ← hc]
  exact (RingHom.congr_fun hcomp c).symm

end HodgeLean.Foundations.Program
