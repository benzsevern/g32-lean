import HodgeLean.Foundations.Program.SchoenCycleC1RetainedWeightedNormalization
import HodgeLean.Foundations.Program.SchoenCycleC1ActualMarkedCoefficientTransport
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

/-- An actual selected marked Kummer chart and the final weighted branch
identity give etaleness of the full normalization after retained birational
transport. The unit correction and all final nonvanishing are constructed. -/
theorem s2e_c1_actual_marked_weighted_normalization_etale
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] [IsAffine X]
    [IsIntegrallyClosed Γ(X, ⊤)] [CharZero X.functionField]
    (f : X ⟶ Y) [IsDominant f] [QuasiCompact f] (P : X.PartialIso Y)
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
      ∀ (I Pts : Type) [Fintype I] [DecidableEq Pts]
        (marks : I → Pts), Function.Injective marks →
      ∀ (A : Finset Pts) (D : I → Y.IdealSheafData)
        (U : Y.affineOpens) [Nonempty U.1], (⊤ : X.Opens) ≤ f ⁻¹ᵁ U.1 →
      ∀ (b : A → Γ(Y, U.1)) (g : I → Γ(X, ⊤)), (∀ j, b j ≠ 0) →
      (∀ i (hi : marks i ∈ A), (D i).ideal U = Ideal.span {b ⟨marks i, hi⟩}) →
      (∀ i, marks i ∉ A → (D i).ideal U = ⊤) →
      (∀ i, ((D i).comap f).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {g i}) →
      ∀ (k : I → ℕ) (n : Pts → ℤ) (E : Γ(X, ⊤)) (s : ℤ),
      (∀ i, (m : ℤ) ∣ n (marks i) - s * (k i : ℤ)) →
      (∏ i, (Ideal.span {g i}) ^ k i) = (Ideal.span {E}) ^ m →
      ∀ (u : Γ(Y, U.1)ˣ) (d : Γ(X, ⊤)ˣ), (d : Γ(X, ⊤)) = (m : Γ(X, ⊤)) →
      c = Y.germToFunctionField U.1 (u : Γ(Y, U.1)) *
        ∏ j ∈ Finset.univ.filter (fun j : A => ∃ i, j.val = marks i),
          (Y.germToFunctionField U.1 (b j)) ^ n j.val →
      Etale ηX.fromNormalization := by
  classical
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
  letI := φY.toAlgebra
  dsimp only
  intro B c m hm hdim hroot I Pts _ _ marks hinj A D U _ hVU b g hb hDU habsent hDV
    k n E s hn hI u d hd hc
  let hg := s2e_c1_dominant_generic_point f
  let ψ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫ f.stalkMap (genericPoint X)).hom
  have hψ := s2e_c1_generic_stalk_map_local_square f hg
  obtain ⟨v, hne, hcoeff⟩ := s2e_c1_actual_marked_coefficient_transport f ψ hψ
    marks hinj A D U ⟨⊤, isAffineOpen_top X⟩ hVU b g hb hDU habsent hDV n u c hc
  exact s2e_c1_retained_weighted_normalization_etale f P hP L ηX ηY hη φY hY
    B c m hm hdim hroot I g hne k (fun i => n (marks i)) E s hn hI v d hd hcoeff

end HodgeLean.Foundations.Program
