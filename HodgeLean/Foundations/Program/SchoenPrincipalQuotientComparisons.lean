import HodgeLean.Foundations.Program.SchoenInvariantPrincipalSchemeCharts
import HodgeLean.Foundations.Program.SchoenInvariantLocalizationMaps

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Quotient comparison along a nonempty invariant principal open of an affine
domain is an open immersion of schemes. -/
theorem s2_principalOpen_quotientComparison_openImmersion
    (X : Scheme.{0}) [IsAffine X] [IsDomain Γ(X, ⊤)]
    (G : Type) [Group G] (ρ : G →* Aut X) :
    letI := s2_schemeSectionAction X G ρ
    ∀ r : FixedPoints.subring Γ(X, ⊤) G, (r : Γ(X, ⊤)) ≠ 0 →
      IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (s2_fixedSectionPullback G (s2_fixedSection_basicOpenAction X G ρ r) ρ
          (X.basicOpen (r : Γ(X, ⊤))).ι (s2_fixedSection_basicOpenAction_ι X G ρ r)))) := by
  letI := s2_schemeSectionAction X G ρ
  intro r hr
  let U := X.basicOpen (r : Γ(X, ⊤))
  let ρU := s2_fixedSection_basicOpenAction X G ρ r
  let B := ↑Γ(X, ⊤)
  let L := ↑Γ(U.toScheme, ⊤)
  letI := s2_schemeSectionAction U.toScheme G ρU
  letI : Algebra B L := U.ι.appTop.hom.toAlgebra
  let A := FixedPoints.subalgebra ℤ B G
  let rA : A := ⟨r.val, r.property⟩
  let M := Submonoid.powers rA
  let K := Localization M
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B M) L := by
    rw [Algebra.algebraMapSubmonoid_powers]
    exact s2_basicOpen_globalSections_isLocalization X r.val
  letI : Algebra A L := ((algebraMap B L).comp (algebraMap A B)).toAlgebra
  letI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra K L := localizationAlgebra M B
  letI : IsScalarTower A K L := isScalarTower_localizationAlgebra M B
  haveI : SMulDistribClass G B L := s2_schemeSectionAction_smulDistribClass G ρU ρ U.ι
    (s2_fixedSection_basicOpenAction_ι X G ρ r)
  have hBL : Function.Injective (algebraMap B L) := by
    apply IsLocalization.injective L (M := Algebra.algebraMapSubmonoid B M)
    rw [Algebra.algebraMapSubmonoid_powers]
    intro b hb
    obtain ⟨n, rfl⟩ := hb
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hr)
  have he : s2_fixedSectionPullback G ρU ρ U.ι (s2_fixedSection_basicOpenAction_ι X G ρ r) =
      s2_localizedFixedBaseMap A B K L G M Subtype.val_injective hBL := by
    ext a
    exact (s2_localizedFixedBaseMap_coe_apply A B K L G M Subtype.val_injective hBL a).symm
  rw [he]
  exact s2_localizedFixedBaseMap_spec_openImmersion A B K L G M
    Subtype.val_injective hBL rA rfl

end HodgeLean.Foundations.Program
