import HodgeLean.Foundations.Program.G32Native.WeilMarkedHodgeTransport

/-! Integral markings, the dual quadratic action and the Hodge plane. -/
noncomputable section
set_option maxRecDepth 8000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.AppellHumbert
namespace HodgeLean.Foundations.Program
private theorem exterior_equiv_cancel {V W : Type} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (e : V ≃ₗ[ℚ] W) (x : ⋀[ℚ]^2 W) :
    exteriorPower.map 2 e.toLinearMap
      (exteriorPower.map 2 e.symm.toLinearMap x) = x := by
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.symm_trans_self,
    LinearEquiv.refl_toLinearMap, exteriorPower.map_id, LinearMap.id_apply]

private theorem exterior_conjugate {V W : Type} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (e : V ≃ₗ[ℚ] W) (J : W →ₗ[ℚ] W)
    (ω : ⋀[ℚ]^2 W) (h : exteriorPower.map 2 J ω = (3 : ℚ) • ω) :
    exteriorPower.map 2 (e.symm.toLinearMap ∘ₗ J ∘ₗ e.toLinearMap)
      (exteriorPower.map 2 e.symm.toLinearMap ω) =
      (3 : ℚ) • exteriorPower.map 2 e.symm.toLinearMap ω := by
  rw [exteriorPower.map_comp, LinearMap.comp_apply,
    exteriorPower.map_comp, LinearMap.comp_apply, exterior_equiv_cancel, h, map_smul]

variable (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (E : LinearMap.BilinForm ℤ Λ) (hE : b2_IsRiemannForm Λ F E)
    (J : Λ →+ Λ) (hJ : ∀ x, J (J x) = (-3 : ℤ) • x)
    (hJF : F ≤ F.comap (b2_cplxMap J))
local notation "P" => weil_marked_torus Λ F hF E hE J hJ hJF
local notation "e" => weil_marked_integralMarking Λ F hF E hE J hJ hJF
local notation "Q" => b4b_transportForm Λ (g32t_Sixfold.X (weil_marked_torus Λ F hF E hE J hJ hJF)) (weil_marked_integralMarking Λ F hF E hE J hJ hJF) E
variable (hskew : ∀ x y, E (J x) y = -E x (J y))

include hskew in
/-- The original skew action induces the cohomological Rosati equation.
Source: Birkenhake–Lange, §§5.2, 9.6. -/
theorem weil_marked_transported_latticeClass_action  :
    let J := (e).toAddMonoidHom.comp
      (J.comp (e).symm.toAddMonoidHom)
    exteriorPower.map 2 (b4b_periodPrecomp _ J)
        (latticeClass (b2_bilinToAddHom (Q))) =
      (3 : ℚ) • latticeClass (b2_bilinToAddHom (Q)) := by
  apply b60b_latticeClass_action (b2_bilinToAddHom (Q))
    (weil_marked_form_riemann Λ F hF E hE J hJ hJF).alt _ 3
  · intro x
    simp only [AddMonoidHom.comp_apply]
    change e
      (J ((e).symm (e
        (J ((e).symm x))))) = -3 • x
    rw [(e).symm_apply_apply]
    have h := hJ ((e).symm x)
    change J (J ((e).symm x)) =
      -3 • (e).symm x at h
    rw [h, map_zsmul, (e).apply_symm_apply]
  · intro x y
    simp only [AddMonoidHom.comp_apply]
    change E ((e).symm (e
        (J ((e).symm x)))) ((e).symm y) =
      -E ((e).symm x) ((e).symm (e
        (J ((e).symm y))))
    rw [(e).symm_apply_apply, (e).symm_apply_apply]
    exact hskew _ _

set_option maxHeartbeats 400000 in
include hskew in
/-- The original skew action induces the cohomological Rosati equation.
Source: Birkenhake–Lange, §§5.2, 9.6. -/
theorem weil_marked_polarization_action  :
    exteriorPower.map 2 ((P).W.J)
        (polarizationVec (torusCohomology_cupProductOf ((P).X)) ((P).pol)) =
      (3 : ℚ) • polarizationVec
        (torusCohomology_cupProductOf ((P).X)) ((P).pol) := by
  have h := weil_marked_transported_latticeClass_action Λ F hF E hE J hJ hJF hskew
  let K := (e).toAddMonoidHom.comp (J.comp (e).symm.toAddMonoidHom)
  have hh := exterior_conjugate (abelianPeriodEquiv (P).X)
    (b4b_periodPrecomp _ K) (latticeClass (b2_bilinToAddHom Q)) h
  change exteriorPower.map 2 (P).W.J
    (polarizationVec (torusCohomology_cupProductOf (P).X)
      (latticeClassHQ (P).X (b2_bilinToAddHom Q))) =
    (3 : ℚ) • polarizationVec (torusCohomology_cupProductOf (P).X)
      (latticeClassHQ (P).X (b2_bilinToAddHom Q))
  rw [weil_riemann_polarization_vec (P).X Q]
  exact hh

include hskew in
/-- The original skew action induces the cohomological Rosati equation.
Source: Birkenhake–Lange, §§5.2, 9.6. -/
theorem weil_marked_rosati_model  :
    letI := (torusCohomology_cupProductOf ((P).X)).finite
    IsRosatiSkew
      (polarizationVec (torusCohomology_cupProductOf ((P).X)) ((P).pol))
      ((P).W.J) := by
  let hω := b2_abelian_nondegenerate ((P).X) (Q) (weil_marked_form_riemann Λ F hF E hE J hJ hJF)
  have hJsquare : (P).W.J ∘ₗ (P).W.J = (-3 : ℚ) • LinearMap.id := by
    exact (P).W.J_sq
  exact ((isRosatiSkew_iff (torusCohomology_cupProductOf ((P).X)) hω
    (by norm_num : (3 : ℚ) ≠ 0) hJsquare).1).1
      (weil_marked_polarization_action Λ F hF E hE J hJ hJF hskew)


#print axioms weil_marked_rosati_model
end HodgeLean.Foundations.Program
