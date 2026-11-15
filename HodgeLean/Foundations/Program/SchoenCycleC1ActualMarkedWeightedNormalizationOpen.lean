import HodgeLean.Foundations.Program.SchoenCycleC1ActualMarkedWeightedNormalization
import HodgeLean.Foundations.Program.SchoenCycleC1GenericOpenHelpers
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

/-- Actual original marked charts and weighted equations on a retained
affine open give etaleness on the full normalization restriction. The
canonical open-section identification transports every specified generator. -/
theorem s2e_c1_actual_marked_weighted_normalization_open_etale
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] [QuasiSeparatedSpace X]
    (f : X ⟶ Y) [IsDominant f] [QuasiCompact f] (P : X.PartialIso Y)
    (hP : P.iso.hom ≫ P.target.ι = P.source.ι ≫ f)
    (L : Type) [Field L] (ηX : Spec (CommRingCat.of L) ⟶ X)
    [IsDominant ηX] [QuasiCompact ηX] [QuasiSeparated ηX]
    (ηY : Spec (CommRingCat.of L) ⟶ Y) (hη : ηX ≫ f = ηY)
    (φY : Y.functionField →+* L)
    (hY : Spec.map (CommRingCat.ofHom φY) ≫ Y.fromSpecStalk (genericPoint Y) = ηY)
    (V : X.affineOpens) [Nonempty V.1]
    [IsIntegrallyClosed Γ(V.1.toScheme, ⊤)] [CharZero V.1.toScheme.functionField] :
    letI := φY.toAlgebra
    ∀ (B : PowerBasis Y.functionField L) (c : Y.functionField) (m : ℕ),
      0 < m → B.dim = m → B.gen ^ m = φY c →
      ∀ (I Pts : Type) [Fintype I] [DecidableEq Pts]
        (marks : I → Pts), Function.Injective marks →
      ∀ (A : Finset Pts) (D : I → Y.IdealSheafData)
        (U : Y.affineOpens) [Nonempty U.1], V.1 ≤ f ⁻¹ᵁ U.1 →
      ∀ (b : A → Γ(Y, U.1)) (g : I → Γ(X, V.1)), (∀ j, b j ≠ 0) →
      (∀ i (hi : marks i ∈ A), (D i).ideal U = Ideal.span {b ⟨marks i, hi⟩}) →
      (∀ i, marks i ∉ A → (D i).ideal U = ⊤) →
      (∀ i, ((D i).comap f).ideal V = Ideal.span {g i}) →
      ∀ (k : I → ℕ) (n : Pts → ℤ) (E : Γ(X, V.1)) (s : ℤ),
      (∀ i, (m : ℤ) ∣ n (marks i) - s * (k i : ℤ)) →
      (∏ i, (Ideal.span {g i}) ^ k i) = (Ideal.span {E}) ^ m →
      ∀ (u : Γ(Y, U.1)ˣ) (d : Γ(X, V.1)ˣ), (d : Γ(X, V.1)) = (m : Γ(X, V.1)) →
      c = Y.germToFunctionField U.1 (u : Γ(Y, U.1)) *
        ∏ j ∈ Finset.univ.filter (fun j : A => ∃ i, j.val = marks i),
          (Y.germToFunctionField U.1 (b j)) ^ n j.val →
      Etale (ηX.fromNormalization ∣_ V.1) := by
  classical
  letI := φY.toAlgebra
  dsimp only
  intro B c m hm hdim hroot I Pts _ _ marks hinj A D U _ hVU b g hb hDU habsent hDV
    k n E s hn hI u d hd hc
  letI : IsAffine V.1.toScheme := V.property
  letI : Nonempty (⊤ : V.1.toScheme.Opens) := ⟨⟨genericPoint _, by trivial⟩⟩
  letI : IsDominant V.1.ι := Opens.isDominant_ι
    (V.1.isOpen.dense (by obtain ⟨p⟩ := ‹Nonempty V.1›; exact ⟨p.val, p.property⟩))
  obtain ⟨ζ, hζqc, hζqs, hζ⟩ := s2e_c1_generic_source_lift_to_open X ηX V.1
    (by obtain ⟨p⟩ := ‹Nonempty V.1›; exact ⟨p.val, p.property⟩)
  letI : QuasiCompact ζ := hζqc
  letI : QuasiSeparated ζ := hζqs
  haveI : IsDominant (ζ ≫ V.1.ι) := by rw [hζ]; infer_instance
  haveI : IsDominant ζ := IsDominant.of_comp_of_isOpenImmersion ζ V.1.ι
  have hζη : ζ ≫ (V.1.ι ≫ f) = ηY := by rw [← Category.assoc, hζ, hη]
  obtain ⟨Q, hQ⟩ := (V.1.ι.birationalOver f (V.1.ι ≫ f) rfl).trans
    (show Scheme.BirationalOver f (𝟙 Y) from ⟨P, by simpa [Scheme.PartialIso.IsOver] using hP⟩)
  have hQ' : Q.iso.hom ≫ Q.target.ι = Q.source.ι ≫ (V.1.ι ≫ f) := by
    simpa [Scheme.PartialIso.IsOver] using hQ
  let ρ := V.1.topIso.inv.hom
  have hcomp : ρ.comp V.1.topIso.hom.hom = RingHom.id _ := by
    ext r
    exact CommRingCat.inv_hom_apply V.1.topIso r
  have hDV' (i : I) : ((D i).comap (V.1.ι ≫ f)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {ρ (g i)} := by
    have hi := s2e_c1_open_centre_sections X ((D i).comap f) V
    rw [hDV i] at hi
    have hi' := congrArg (Ideal.map ρ) hi
    rw [Ideal.map_map, hcomp, Ideal.map_id, Ideal.map_span, Set.image_singleton] at hi'
    simpa only [← Scheme.IdealSheafData.comap_comp] using hi'
  have hI' : (∏ i, (Ideal.span {ρ (g i)}) ^ k i) = (Ideal.span {ρ E}) ^ m := by
    have hi := congrArg (Ideal.mapHom ρ) hI
    simpa only [map_prod, Ideal.mapHom_apply, Ideal.map_pow, Ideal.map_span,
      Set.image_singleton] using hi
  let d' := Units.map ρ.toMonoidHom d
  have hd' : (d' : Γ(V.1.toScheme, ⊤)) = (m : Γ(V.1.toScheme, ⊤)) := by
    change ρ (d : Γ(X, V.1)) = _
    rw [hd, map_natCast]
  have hVU' : (⊤ : V.1.toScheme.Opens) ≤ (V.1.ι ≫ f) ⁻¹ᵁ U.1 := by
    intro p _
    exact hVU p.property
  haveI : Etale ζ.fromNormalization :=
    s2e_c1_actual_marked_weighted_normalization_etale (V.1.ι ≫ f) Q hQ'
      L ζ ηY hζη φY hY B c m hm hdim hroot I Pts marks hinj A D U hVU'
      b (fun i => ρ (g i)) hb hDU habsent hDV' k n (ρ E) s hn hI' u d' hd' hc
  obtain ⟨F, hF, _⟩ := s2e_c1_normalization_corestrict_iso ηX V.1 ζ hζ
  have heq : (ηX.fromNormalization ∣_ V.1) = F.inv ≫ ζ.fromNormalization := by
    rw [← hF, F.inv_hom_id_assoc]
  rw [heq]
  infer_instance

end HodgeLean.Foundations.Program
