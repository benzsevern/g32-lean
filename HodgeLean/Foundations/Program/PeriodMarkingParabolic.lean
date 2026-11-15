import HodgeLean.Foundations.Program.ParabolicCohomology
import HodgeLean.Foundations.Program.ParabolicPolarizationBridge

noncomputable section
open HodgeLean.Papers HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

theorem b64b_parabolic_classes_independent :
    LinearIndependent hp_K (fun a : Fin 6 =>
      (Submodule.Quotient.mk ⟨hp_certK a, hp_certK_mem a⟩ : pc_Vpar hp_rootTupleK)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  refine congrFun (hp_certK_independent c ?_)
  have hmk : (Submodule.Quotient.mk (∑ a, c a • (⟨hp_certK a, hp_certK_mem a⟩ :
      pc_Z hp_rootTupleK)) : pc_Vpar hp_rootTupleK) = 0 := by
    rw [← hc]
    change Submodule.mkQ _ (∑ a, c a • _) = _
    rw [map_sum]
    simp only [map_smul]
    rfl
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hmk
  simpa using hmk

def b64b_parabolicBasis : Module.Basis (Fin 6) hp_K (pc_Vpar hp_rootTupleK) :=
  basisOfLinearIndependentOfCardEqFinrank b64b_parabolic_classes_independent
    (by rw [Fintype.card_fin, hp_vparK_finrank])

theorem b64b_parabolicBasis_gram :
    LinearMap.toMatrix₂ b64b_parabolicBasis b64b_parabolicBasis
      ((1 + 2 * pc_zeta) • pc_SPar hp_rootTupleK 1) = g32H0 pc_zeta := by
  apply Matrix.ext
  intro a b
  rw [map_smul, Matrix.smul_apply, LinearMap.toMatrix₂_apply]
  have he (a : Fin 6) : b64b_parabolicBasis a =
      (Submodule.Quotient.mk ⟨hp_certK a, hp_certK_mem a⟩ : pc_Vpar hp_rootTupleK) := by
    simp [b64b_parabolicBasis]
  rw [he, he, pc_SPar_mk hp_rootTupleK 1 hp_rootTupleK_prod (by simp) hp_rootTupleK_unitary]
  exact hp_certK_gram a b

set_option backward.isDefEq.respectTransparency false in
theorem b64b_parabolic_isometry_to_printed :
    ∃ e : pc_Vpar hp_rootTupleK ≃ₗ[hp_K] (Fin 6 → hp_K),
      ∀ x y, hp_h0Form (e x) (e y) =
        ((1 + 2 * pc_zeta) • pc_SPar hp_rootTupleK 1) x y := by
  let e := b64b_parabolicBasis.equivFun
  have hcoord (a : Fin 6) : e (b64b_parabolicBasis a) = Pi.single a 1 := by
    funext j
    simp only [e, Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
  have hh (a b : Fin 6) : hp_h0Form (Pi.single a 1) (Pi.single b 1) =
      g32H0 pc_zeta a b := by
    have ht := LinearMap.toMatrix₂_toLinearMapₛₗ₂ (σ₁ := starRingEnd hp_K)
      (Pi.basisFun hp_K (Fin 6)) (Pi.basisFun hp_K (Fin 6)) (g32H0 hp_zeta)
    exact congrArg (fun M => M a b) ht
  have hf : (hp_h0Form.comp e.toLinearMap).compl₂ e.toLinearMap =
      (1 + 2 * pc_zeta) • pc_SPar hp_rootTupleK 1 := by
    apply LinearMap.ext_basis b64b_parabolicBasis b64b_parabolicBasis
    intro a b
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hcoord, hcoord, hh]
    have hgram := congrArg (fun M => M a b) b64b_parabolicBasis_gram
    simp only [LinearMap.toMatrix₂_apply] at hgram
    exact hgram.symm
  exact ⟨e, fun x y => congrArg (fun f => f x y) hf⟩

theorem b64b_parabolic_hermitian :
    ((1 + 2 * pc_zeta) • pc_SPar hp_rootTupleK 1).IsSymm ∧
    ((1 + 2 * pc_zeta) • pc_SPar hp_rootTupleK 1).Nondegenerate := by
  obtain ⟨e, he⟩ := b64b_parabolic_isometry_to_printed
  constructor
  · apply LinearMap.isSymm_def.mpr
    intro x y
    rw [← he, ← he]
    exact LinearMap.isSymm_def.mp hp_h0_isSymm (e x) (e y)
  · constructor
    · intro x hx
      apply e.injective
      rw [map_zero]
      apply hp_h0_nondegenerate.1
      intro w
      obtain ⟨y, rfl⟩ := e.surjective w
      rw [he, hx]
    · intro y hy
      apply e.injective
      rw [map_zero]
      apply hp_h0_nondegenerate.2
      intro w
      obtain ⟨x, rfl⟩ := e.surjective w
      rw [he, hy]

theorem b64b_parabolic_detClass
    (hh : ((1 + 2 * pc_zeta) • pc_SPar hp_rootTupleK 1).IsSymm)
    (hn : ((1 + 2 * pc_zeta) • pc_SPar hp_rootTupleK 1).Nondegenerate) :
    detClass ((1 + 2 * pc_zeta) • pc_SPar hp_rootTupleK 1) hh hn = HodgeLean.RealDefs.classNegTwo := by
  obtain ⟨e, he⟩ := b64b_parabolic_isometry_to_printed
  exact (HermitianClass.detClass_eq_of_equiv _ _ _ _ hh hn
    hp_h0_isSymm hp_h0_nondegenerate e he).trans hp_h0_detClass

theorem b64b_printed_gram_detClass {W : Type*} [AddCommGroup W]
    [Module hp_K W] [Module.Finite hp_K W]
    (H : W →ₗ⋆[hp_K] W →ₗ[hp_K] hp_K) (hh : H.IsSymm) (hn : H.Nondegenerate)
    (B : Module.Basis (Fin 6) hp_K W) (c : ℚ) (hc : 0 < c)
    (hgram : LinearMap.toMatrix₂ B B H = (c : hp_K) • g32H0 pc_zeta) :
    detClass H hh hn = HodgeLean.RealDefs.classNegTwo := by
  rw [detClass_eq hh hn B]
  have hdet := g32d_gram_det c B H hgram
  have hdetQ : gramDetℚ H B = (-2 / 81 : ℚ) * c ^ 6 := by
    apply (algebraMap ℚ hp_K).injective
    rw [algebraMap_gramDetℚ hh B, gramDet, hdet]
    simp only [map_mul, map_pow]
    ext <;> simp <;> ring
  refine Eq.trans ?_ (g32d_scaled_det_class c hc)
  apply congrArg (fun u : ℚˣ =>
    (u : ℚˣ ⧸ normSubgroup hp_K))
  apply Units.ext
  exact hdetQ

end HodgeLean.Foundations.Program
