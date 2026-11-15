import HodgeLean.Foundations.Program.SchoenQuotientIntegrality
import HodgeLean.Foundations.Mathlib.ZmtIso

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency.types false in
/-- Sections on a nonempty affine open in a normal integral scheme are integrally closed. -/
theorem s2_affineOpen_sections_integrallyClosed {X : Scheme.{0}} [IsIntegral X]
    (hX : zmtiso_IsNormal X) {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X, U) := by
  refine IsIntegrallyClosed.of_localization_maximal fun P _ hP ↦ ?_
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf
    ⟨hU.fromSpec ⟨P, hP.isPrime⟩, (hU.isoSpec.inv _).2⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩)) P :=
    hU.isLocalization_stalk' ⟨P, hP.isPrime⟩ (hU.isoSpec.inv _).2
  exact (hX _).2.of_equiv
    (IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩))
      (Localization.AtPrime P)).toRingEquiv

/-- The actual invariant affine quotient charts of a normal integral source have normal stalks. -/
theorem s2_invariantAffineQuotientObj_normal (X : Scheme.{0}) [IsIntegral X]
    (hX : zmtiso_IsNormal X) (G : Type) [Group G] (ρ : G →* Aut X)
    (U : s2_InvariantAffineOpen X G ρ) :
    zmtiso_IsNormal (s2_invariantAffineQuotientObj X G ρ U) := by
  haveI : Nonempty U.val := U.property.2.1.to_subtype
  haveI : IsIntegrallyClosed Γ(X, U.val) :=
    s2_affineOpen_sections_integrallyClosed hX U.property.1
  haveI : IsIntegrallyClosed Γ(U.val.toScheme, ⊤) :=
    IsIntegrallyClosed.of_equiv U.val.topIso.commRingCatIsoToRingEquiv.symm
  letI := s2_schemeSectionAction U.val.toScheme G (s2_invariantAffineOpenAction X G ρ U)
  intro x
  exact ⟨inferInstance, s2_fixedRing_spec_stalk_normal Γ(U.val.toScheme, ⊤) G x⟩

/-- Normality of invariant charts transports through the actual glued atlas. -/
theorem s2_invariantAffineGlued_normal (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hX : zmtiso_IsNormal X) (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) :
    zmtiso_IsNormal (s2_invariantAffineGlued X G ρ) := by
  intro x
  obtain ⟨U, u, rfl⟩ := s2_invariantAffineGluedι_jointly_surjective X G ρ x
  let e := (asIso ((s2_invariantAffineGluedι X G ρ U).stalkMap u)).commRingCatIsoToRingEquiv
  obtain ⟨hdom, hnormal⟩ := s2_invariantAffineQuotientObj_normal X hX G ρ U u
  letI := hdom
  exact ⟨e.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e.symm⟩

/-- A smooth integral source over a field has a normal globally glued invariant scheme. -/
theorem s2_invariantAffineGlued_normal_of_smooth {k : Type} [Field k]
    (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (s : X ⟶ Spec (CommRingCat.of k)) [Smooth s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) :
    zmtiso_IsNormal (s2_invariantAffineGlued X G ρ) :=
  s2_invariantAffineGlued_normal X (zmtiso_normal_of_smooth X s) G ρ

end HodgeLean.Foundations.Program
