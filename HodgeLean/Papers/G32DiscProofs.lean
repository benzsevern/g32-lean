import HodgeLean.Papers.G32DiscDefs

/-! # Proof obligations for the G32 stage-5 discriminant specification -/

noncomputable section

open HodgeLean.RealDefs HodgeLean.Foundations.HermitianForm
open scoped QuadraticAlgebra

namespace HodgeLean.Papers

theorem g32d_zeta_relation_aux :
    let ζ : QuadraticAlgebra ℚ (-3) 0 := (-1 + QuadraticAlgebra.omega) / 2
    ζ ^ 2 + ζ + 1 = 0 := by
  dsimp
  field_simp
  ring_nf
  rw [QuadraticAlgebra.omega_pow_two_eq_add]
  norm_num

theorem g32d_gram_det_aux
    {W : Type*} [AddCommGroup W] [Module (QuadraticAlgebra ℚ (-3) 0) W]
    (c : ℚ) (e : Module.Basis (Fin 6) (QuadraticAlgebra ℚ (-3) 0) W)
    (H : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0]
      W →ₗ[QuadraticAlgebra ℚ (-3) 0] QuadraticAlgebra ℚ (-3) 0)
    (hgram : LinearMap.toMatrix₂ e e H =
      (c : QuadraticAlgebra ℚ (-3) 0) •
        g32H0 ((-1 + QuadraticAlgebra.omega) / 2)) :
    (LinearMap.toMatrix₂ e e H).det =
      (c : QuadraticAlgebra ℚ (-3) 0) ^ 6 * (-2 / 81) := by
  rw [hgram, Matrix.det_smul, Fintype.card_fin]
  rw [papers_g32_h0_det _ g32d_zeta_relation_aux]

theorem g32d_scaled_det_class_aux (c : ℚ) (hc : 0 < c) :
    ((Units.mk0 ((-2 / 81 : ℚ) * c ^ 6) (mul_ne_zero (by norm_num)
      (pow_ne_zero 6 (ne_of_gt hc))) : ℚˣ) :
      ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) = classNegTwo := by
  let u : ℚˣ := Units.mk0 c (ne_of_gt hc)
  have hu : u ^ 6 ∈ normSubgroup (QuadraticAlgebra ℚ (-3) 0) := by
    rw [show 6 = 3 * 2 by norm_num, pow_mul]
    exact sq_mem_normSubgroup (u ^ 3)
  calc
    ((Units.mk0 ((-2 / 81 : ℚ) * c ^ 6) (mul_ne_zero (by norm_num)
        (pow_ne_zero 6 (ne_of_gt hc))) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) =
        (Units.mk0 (-2 / 81 : ℚ) (by norm_num) : ℚˣ) := by
      apply mk_eq_mk_of_eq_mul hu
      change (-2 / 81 : ℚ) * c ^ 6 = c ^ 6 * (-2 / 81)
      ring
    _ = classNegTwo := classes_F1569.1

set_option maxHeartbeats 400000 in
set_option maxRecDepth 10000 in
theorem g32d_fiber_disc_aux {S : Type} (fiber : S → g32t_Sixfold)
    (fiber_polarized : ∀ s, g32t_PolarizedWeil (fiber s))
    (hpar : ∀ s, g32d_ParabolicPolarization (fiber_polarized s)) :
    ∀ s, g32t_disc (fiber_polarized s) = classNegTwo := by
  intro s
  let hT := HodgeLean.Adapters.torusCohomology_cupProductOf (fiber s).X
  letI := hT.finite
  rcases hpar s with ⟨c, e, hgram⟩
  let E := polarizationForm hT (fiber_polarized s).nondegenerate
  let J : {J : HQ (fiber s).X 1 →ₗ[ℚ] HQ (fiber s).X 1 //
      J ∘ₗ J = (-3 : ℚ) • LinearMap.id} :=
    ⟨(fiber s).W.J, (fiber s).W.J_sq⟩
  have hskew : ∀ x y, E (J.1 x) y = -E x (J.1 y) :=
    (HodgeLean.Foundations.Symplectic.isRosatiSkew_iff_dualForm
      (fiber_polarized s).nondegenerate (fiber s).W.J).1 (fiber_polarized s).rosati
  let H := HodgeLean.Foundations.WeilHermitian.weilHermitian E J hskew
  have hsymm := HodgeLean.Foundations.WeilHermitian.isSymm_weilHermitian
    (J := J) (hskew := hskew)
    (isAlt_polarizationForm hT (fiber_polarized s).nondegenerate)
  have hnd := HodgeLean.Foundations.WeilHermitian.nondegenerate_weilHermitian
    (J := J) (hskew := hskew)
    (nondegenerate_polarizationForm hT (fiber_polarized s).nondegenerate)
  change LinearMap.toMatrix₂ e e H = _ at hgram
  change detClass H hsymm hnd = classNegTwo
  rw [detClass_eq hsymm hnd e]
  have hdet := g32d_gram_det_aux (c : ℚ) e H hgram
  have hdetQ : gramDetℚ H e = (-2 / 81 : ℚ) * (c : ℚ) ^ 6 := by
    apply (algebraMap ℚ (QuadraticAlgebra ℚ (-3) 0)).injective
    rw [algebraMap_gramDetℚ hsymm e, gramDet, hdet]
    simp only [map_mul, map_pow]
    ext <;> simp <;> ring
  refine Eq.trans ?_ (g32d_scaled_det_class_aux c c.property)
  apply congrArg (fun u : ℚˣ =>
    (u : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)))
  apply Units.ext
  exact hdetQ

end HodgeLean.Papers
