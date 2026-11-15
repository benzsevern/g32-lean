import HodgeLean.Foundations.Program.SchoenCycleC1FormalSectionEtale
import HodgeLean.Foundations.Program.SchoenTowerEtaleSpecNeighborhood

/-! # Actual source opens from etaleness of affine sections -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Etaleness of the actual finite affine section map at a point produces
an affine source neighbourhood where the original projection is etale. -/
theorem s2e_c1_source_etale_open_of_section_isEtaleAt
    (X Y : Scheme) [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (U : Y.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ f ⁻¹ᵁ U) :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    Algebra.IsEtaleAt Γ(Y, U) ((hU.preimage f).primeIdealOf ⟨x, hx⟩).asIdeal →
    ∃ V : X.Opens, x ∈ V ∧ V ≤ f ⁻¹ᵁ U ∧ IsAffineOpen V ∧ Etale (V.ι ≫ f) := by
  let W := f ⁻¹ᵁ U
  let A := Γ(Y, U)
  let C := Γ(X, W)
  letI : Algebra A C := (f.app U).hom.toAlgebra
  letI : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : Module.Finite A C := f.finite_app U hU
  letI : Algebra.FinitePresentation A C := (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  intro het
  let P := ((hU.preimage f).primeIdealOf ⟨x, hx⟩).asIdeal
  letI : Algebra.IsEtaleAt A P := het
  obtain ⟨r, hr, hEt⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) P
  let V := X.basicOpen r
  have hV : IsAffineOpen V := (hU.preimage f).basicOpen r
  have hle : V ≤ W := X.basicOpen_le r
  let D := Γ(X, V)
  letI : Algebra A D := ((algebraMap C D).comp (algebraMap A C)).toAlgebra
  letI : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsLocalization.Away r D := (hU.preimage f).isLocalization_basicOpen r
  letI : Algebra.Etale A (Localization.Away r) := hEt
  let E := (IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r) D).restrictScalars A
  letI : Algebra.Etale A D := Algebra.Etale.of_equiv E
  have happ : (f.appLE U V hle).hom = algebraMap A D := by
    have h := f.appLE_map (U := U) (V := W) le_rfl (homOfLE hle).op
    rw [show f.appLE U W le_rfl = f.app U from Scheme.Hom.appLE_eq_app f] at h
    exact congrArg CommRingCat.Hom.hom h
  letI : Etale (Spec.map (f.appLE U V hle)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (happ ▸ RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A D))
  have heq : V.ι ≫ f = hV.isoSpec.hom ≫ Spec.map (f.appLE U V hle) ≫ hU.fromSpec := by
    rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hle, ← Category.assoc,
      hV.isoSpec_hom_fromSpec]
  have hxV : x ∈ V := by
    change x ∈ X.basicOpen r
    rw [Scheme.mem_basicOpen X r x hx]
    by_contra hn
    apply hr
    change r ∈ ((hU.preimage f).primeIdealOf ⟨x, hx⟩).asIdeal
    rw [(hU.preimage f).primeIdealOf_eq_map_closedPoint]
    exact hn
  refine ⟨V, hxV, hle, hV, ?_⟩
  rw [heq]
  infer_instance

end HodgeLean.Foundations.Program
