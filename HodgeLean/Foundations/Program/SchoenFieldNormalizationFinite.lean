import HodgeLean.Foundations.Program.SchoenDominantSectionInjection
import HodgeLean.Foundations.Program.SchoenFiniteIntegralClosure
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual normalization of a normal noetherian integral scheme in a dominant quasi-finite field point of characteristic zero is finite. -/
theorem s2_fieldNormalization_finite {K : Type} [Field K] [CharZero K]
    (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (hn : zmtiso_IsNormal X)
    (η : Spec (.of K) ⟶ X) [QuasiCompact η] [QuasiSeparated η]
    [IsDominant η] [LocallyQuasiFinite η] : IsFinite η.fromNormalization := by
  refine { finite_app := ?_ }
  intro U hU
  rcases U.1.eq_empty_or_nonempty with he | he
  · have he' : U = ⊥ := SetLike.ext' he
    haveI : Subsingleton Γ(X, U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty he')
    haveI : Subsingleton Γ(η.normalization, η.fromNormalization ⁻¹ᵁ U) :=
      subsingleton_of_zero_eq_one (by
        rw [← map_zero (η.fromNormalization.app U).hom,
          ← map_one (η.fromNormalization.app U).hom, Subsingleton.elim (0 : Γ(X, U)) 1])
    exact RingHom.Finite.of_surjective _ (fun x => ⟨0, Subsingleton.elim _ x⟩)
  · haveI : Nonempty U := he.to_subtype
    have hpre : η ⁻¹ᵁ U = ⊤ := by
      ext x
      change η x ∈ U ↔ True
      rw [Subsingleton.elim x (genericPoint (Spec (.of K))), s2_dominant_genericPoint η]
      exact iff_true_intro (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
        (by simpa using he))
    let e : Γ(Spec (.of K), η ⁻¹ᵁ U) ≅ .of K :=
      (Spec (.of K)).presheaf.mapIso (eqToIso hpre.symm).op ≪≫ Scheme.ΓSpecIso (.of K)
    letI : Field Γ(Spec (.of K), η ⁻¹ᵁ U) :=
      (e.commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)).toField
    haveI : CharZero Γ(Spec (.of K), η ⁻¹ᵁ U) := e.hom.hom.charZero
    letI : Algebra Γ(X, U) Γ(Spec (.of K), η ⁻¹ᵁ U) := (η.app U).hom.toAlgebra
    haveI : FaithfulSMul Γ(X, U) Γ(Spec (.of K), η ⁻¹ᵁ U) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (s2_dominant_app_injective η ⟨U, hU⟩)
    haveI : CharZero Γ(X, U) := (η.app U).hom.charZero
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    haveI : IsIntegrallyClosed Γ(X, U) := s2_affineOpen_sections_integrallyClosed hn hU
    haveI : Algebra.QuasiFinite Γ(X, U) Γ(Spec (.of K), η ⁻¹ᵁ U) := by
      have hV : IsAffineOpen (η ⁻¹ᵁ U) := by rw [hpre]; exact isAffineOpen_top _
      have hq := LocallyQuasiFinite.quasiFinite_appLE (f := η) hU hV le_rfl
      have hq' : (η.app U).hom.QuasiFinite := by
        simpa only [← Scheme.Hom.app_eq_appLE] using hq
      exact hq'.toAlgebra
    have hf := s2_integralClosure_finite_of_quasiFinite_field Γ(X, U)
      Γ(Spec (.of K), η ⁻¹ᵁ U)
    rw [Scheme.Hom.fromNormalization_app η hU, CommRingCat.hom_comp]
    exact (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (η.normalizationObjIso hU).inv).2).comp
        (RingHom.finite_algebraMap.mpr hf)

end HodgeLean.Foundations.Program
