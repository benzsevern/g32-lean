import HodgeLean.Papers.G32ModuliDefs
import HodgeLean.Papers.G32Transfer
import Mathlib.Analysis.Matrix.Order

/-! # G32 Theorem A, stage 1: the Weil-moduli interface, open proof obligations -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff ComplexOrder Matrix MatrixOrder
  Matrix.Norms.L2Operator
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

theorem g32m_periodSet_isOpen_aux : IsOpen g32m_periodSet := by
  have hnorm (A : Matrix (Fin 3) (Fin 3) ℂ) :
      (1 - Aᴴ * A).PosDef ↔ ‖A‖ < 1 := by
    constructor
    · intro h
      have hs : IsStrictlyPositive (1 - Aᴴ * A) := h.isStrictlyPositive
      obtain ⟨r, hr, hrle⟩ : ∃ r > 0, algebraMap ℝ _ r ≤ 1 - Aᴴ * A :=
        (CFC.exists_pos_algebraMap_le_iff (1 - Aᴴ * A) hs.isSelfAdjoint).2
          (fun x hx => hs.spectrum_pos (𝕜 := ℝ) hx)
      have hsum : algebraMap ℝ _ r + Aᴴ * A ≤ 1 := by
        rwa [le_sub_iff_add_le] at hrle
      have hle : Aᴴ * A ≤ algebraMap ℝ _ (1 - r) := by
        rw [map_sub, map_one, le_sub_iff_add_le]
        simpa [add_comm] using hsum
      have hr1 : 0 ≤ 1 - r := by
        have har : 0 ≤ algebraMap ℝ (Matrix (Fin 3) (Fin 3) ℂ) (1 - r) :=
          (star_mul_self_nonneg A).trans hle
        exact (algebraMap_le_algebraMap (β := Matrix (Fin 3) (Fin 3) ℂ)).mp <| by
          simpa only [map_sub, map_one, map_zero] using har
      have hn : ‖Aᴴ * A‖ ≤ 1 - r :=
        (CStarAlgebra.norm_le_iff_le_algebraMap (Aᴴ * A) hr1
          (star_mul_self_nonneg A)).2 hle
      change ‖star A * A‖ ≤ 1 - r at hn
      rw [CStarRing.norm_star_mul_self] at hn
      nlinarith [norm_nonneg A]
    · intro h
      have hn : ‖Aᴴ * A‖ < 1 := by
        change ‖star A * A‖ < 1
        rw [CStarRing.norm_star_mul_self]
        nlinarith [norm_nonneg A]
      have hnon : 0 ≤ 1 - Aᴴ * A := sub_nonneg.mpr <|
        (CStarAlgebra.norm_le_one_iff_of_nonneg (Aᴴ * A)
          (star_mul_self_nonneg A)).mp hn.le
      exact Matrix.isStrictlyPositive_iff_posDef.mp
        ((IsUnit.one_sub_of_norm_lt_one hn).isStrictlyPositive hnon)
  rw [show g32m_periodSet = {z | ‖g32m_toMat z‖ < 1} by
    ext z
    exact hnorm (g32m_toMat z)]
  exact isOpen_lt
    (continuous_norm.comp <| continuous_matrix fun i j => continuous_apply _)
    continuous_const

theorem g32m_domain_coe_aux : (g32m_Domain : Set (Fin 9 → ℂ)) = g32m_periodSet := by
  exact g32m_periodSet_isOpen_aux.interior_eq

theorem g32m_periodSet_convex_aux : Convex ℝ g32m_periodSet := by
  have hnorm (A : Matrix (Fin 3) (Fin 3) ℂ) :
      (1 - Aᴴ * A).PosDef ↔ ‖A‖ < 1 := by
    constructor
    · intro h
      have hs : IsStrictlyPositive (1 - Aᴴ * A) := h.isStrictlyPositive
      obtain ⟨r, hr, hrle⟩ : ∃ r > 0, algebraMap ℝ _ r ≤ 1 - Aᴴ * A :=
        (CFC.exists_pos_algebraMap_le_iff (1 - Aᴴ * A) hs.isSelfAdjoint).2
          (fun x hx => hs.spectrum_pos (𝕜 := ℝ) hx)
      have hsum : algebraMap ℝ _ r + Aᴴ * A ≤ 1 := by
        rwa [le_sub_iff_add_le] at hrle
      have hle : Aᴴ * A ≤ algebraMap ℝ _ (1 - r) := by
        rw [map_sub, map_one, le_sub_iff_add_le]
        simpa [add_comm] using hsum
      have hr1 : 0 ≤ 1 - r := by
        have har : 0 ≤ algebraMap ℝ (Matrix (Fin 3) (Fin 3) ℂ) (1 - r) :=
          (star_mul_self_nonneg A).trans hle
        exact (algebraMap_le_algebraMap (β := Matrix (Fin 3) (Fin 3) ℂ)).mp <| by
          simpa only [map_sub, map_one, map_zero] using har
      have hn : ‖Aᴴ * A‖ ≤ 1 - r :=
        (CStarAlgebra.norm_le_iff_le_algebraMap (Aᴴ * A) hr1
          (star_mul_self_nonneg A)).2 hle
      change ‖star A * A‖ ≤ 1 - r at hn
      rw [CStarRing.norm_star_mul_self] at hn
      nlinarith [norm_nonneg A]
    · intro h
      have hn : ‖Aᴴ * A‖ < 1 := by
        change ‖star A * A‖ < 1
        rw [CStarRing.norm_star_mul_self]
        nlinarith [norm_nonneg A]
      have hnon : 0 ≤ 1 - Aᴴ * A := sub_nonneg.mpr <|
        (CStarAlgebra.norm_le_one_iff_of_nonneg (Aᴴ * A)
          (star_mul_self_nonneg A)).mp hn.le
      exact Matrix.isStrictlyPositive_iff_posDef.mp
        ((IsUnit.one_sub_of_norm_lt_one hn).isStrictlyPositive hnon)
  rw [show g32m_periodSet = {z | ‖g32m_toMat z‖ < 1} by
    ext z
    exact hnorm (g32m_toMat z)]
  intro x hx y hy a b ha hb hab
  have hmap : g32m_toMat (a • x + b • y) =
      a • g32m_toMat x + b • g32m_toMat y := by
    ext i j
    simp [g32m_toMat]
  rw [Set.mem_setOf_eq, hmap]
  calc
    ‖a • g32m_toMat x + b • g32m_toMat y‖
        ≤ ‖a • g32m_toMat x‖ + ‖b • g32m_toMat y‖ := norm_add_le _ _
    _ = a * ‖g32m_toMat x‖ + b * ‖g32m_toMat y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * max ‖g32m_toMat x‖ ‖g32m_toMat y‖ +
        b * max ‖g32m_toMat x‖ ‖g32m_toMat y‖ := by gcongr <;> simp
    _ = max ‖g32m_toMat x‖ ‖g32m_toMat y‖ := by rw [← add_mul, hab, one_mul]
    _ < 1 := max_lt hx hy

theorem g32m_zero_mem_aux : (0 : Fin 9 → ℂ) ∈ g32m_Domain := by
  change (0 : Fin 9 → ℂ) ∈ (g32m_Domain : Set (Fin 9 → ℂ))
  rw [g32m_domain_coe_aux]
  change (1 - (g32m_toMat 0)ᴴ * g32m_toMat 0).PosDef
  have hz : g32m_toMat (0 : Fin 9 → ℂ) = 0 := by ext; simp [g32m_toMat]
  rw [hz]
  simpa using (Matrix.PosDef.one : (1 : Matrix (Fin 3) (Fin 3) ℂ).PosDef)

theorem g32m_periodSet_isBounded_aux : Bornology.IsBounded g32m_periodSet := by
  refine (Metric.isBounded_ball : Bornology.IsBounded
    (Metric.ball (0 : Fin 9 → ℂ) 1)).subset ?_
  intro z hz
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro k
  change (1 - (g32m_toMat z)ᴴ * g32m_toMat z).PosDef at hz
  let e (j : Fin 3) : Fin 3 → ℂ := fun i => if i = j then 1 else 0
  have he (j : Fin 3) : e j ≠ 0 := by
    intro h
    have := congrFun h j
    simp [e] at this
  have hp (j : Fin 3) := hz.dotProduct_mulVec_pos (he j)
  have hstar (w : ℂ) : (starRingEnd ℂ) w * w = (‖w‖ : ℂ) ^ 2 := Complex.conj_mul' w
  fin_cases k <;> first
    | (have q := hp 0
       simp [e, g32m_toMat, finProdFinEquiv, dotProduct, Matrix.mulVec,
         Matrix.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ] at q
       simp_rw [hstar] at q
       have qr : ‖z 0‖ ^ 2 + (‖z 3‖ ^ 2 + ‖z 6‖ ^ 2) < 1 := by exact_mod_cast q
       norm_num at *
       nlinarith [sq_nonneg ‖z 0‖, sq_nonneg ‖z 3‖, sq_nonneg ‖z 6‖])
    | (have q := hp 1
       simp [e, g32m_toMat, finProdFinEquiv, dotProduct, Matrix.mulVec,
         Matrix.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ] at q
       simp_rw [hstar] at q
       have qr : ‖z 1‖ ^ 2 + (‖z 4‖ ^ 2 + ‖z 7‖ ^ 2) < 1 := by exact_mod_cast q
       norm_num at *
       nlinarith [sq_nonneg ‖z 1‖, sq_nonneg ‖z 4‖, sq_nonneg ‖z 7‖])
    | (have q := hp 2
       simp [e, g32m_toMat, finProdFinEquiv, dotProduct, Matrix.mulVec,
         Matrix.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ] at q
       simp_rw [hstar] at q
       have qr : ‖z 2‖ ^ 2 + (‖z 5‖ ^ 2 + ‖z 8‖ ^ 2) < 1 := by exact_mod_cast q
       norm_num at *
       nlinarith [sq_nonneg ‖z 2‖, sq_nonneg ‖z 5‖, sq_nonneg ‖z 8‖])

theorem g32m_not_mem_of_toMat_eq_one_aux (z : Fin 9 → ℂ) (hz : g32m_toMat z = 1) :
    z ∉ g32m_periodSet := by
  intro h
  change (1 - (g32m_toMat z)ᴴ * g32m_toMat z).PosDef at h
  rw [hz] at h
  have hv : (fun i : Fin 3 => if i = 0 then (1 : ℂ) else 0) ≠ 0 := by
    intro he
    have := congrFun he 0
    simp at this
  have hp := h.dotProduct_mulVec_pos hv
  simpa using hp

theorem g32m_domain_connectedSpace_aux : ConnectedSpace g32m_Domain := by
  apply Subtype.connectedSpace
  refine ⟨⟨0, g32m_zero_mem_aux⟩, ?_⟩
  rw [g32m_domain_coe_aux]
  exact g32m_periodSet_convex_aux.isPreconnected

theorem g32m_univ_polarizedWeil_aux (F : g32m_UniversalFamily) (τ : g32m_Domain) :
    g32t_PolarizedWeil (F.univ τ) := by
  exact (g32t_isMember_iff (F.univ τ)).mp (F.member τ) |>.choose

theorem g32m_univ_disc_aux (F : g32m_UniversalFamily) (τ : g32m_Domain)
    (h : g32t_PolarizedWeil (F.univ τ)) : g32t_disc h = classNegTwo := by
  obtain ⟨h', hh'⟩ := (g32t_isMember_iff (F.univ τ)).mp (F.member τ)
  simpa only [proof_irrel_heq h h'] using hh'

theorem g32m_exists_member_aux (F : g32m_UniversalFamily) : ∃ P, g32t_IsMember P := by
  refine ⟨F.univ ⟨0, ?_⟩, F.member _⟩
  exact g32m_zero_mem_aux

theorem g32m_theoremA_of_stages_aux (F : g32m_UniversalFamily) (R : g32m_StageFields F)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  letI : ConnectedSpace g32m_Domain := g32m_domain_connectedSpace_aux
  exact g32t_theoremA_of_transfer (g32m_transferFields F R) A W pol

end HodgeLean.Papers
