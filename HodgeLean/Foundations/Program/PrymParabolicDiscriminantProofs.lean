import HodgeLean.Foundations.Program.PrymParabolicDiscriminantSignature

/-! # H7 draft proof interfaces

Only the seven draft theorem bodies are open. HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Foundations.WeilHermitian
open HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

theorem hg7_matrix_gram {n : ℕ} (M : Matrix (Fin n) (Fin n) hp_K) :
    LinearMap.toMatrix₂ (Pi.basisFun _ _) (Pi.basisFun _ _) (hp_matrixForm M) = M :=
  LinearMap.toMatrix₂_toLinearMapₛₗ₂ _ _ _

theorem hg7_matrix_symm {n : ℕ} (M : Matrix (Fin n) (Fin n) hp_K) :
    (hp_matrixForm M).IsSymm ↔ M.IsHermitian := by
  rw [LinearMap.isSymm_iff_isHermitian_toMatrix (Pi.basisFun _ _), hg7_matrix_gram]

theorem hg7_matrix_nondegenerate {n : ℕ} (M : Matrix (Fin n) (Fin n) hp_K)
    (hh : (hp_matrixForm M).IsSymm) :
    (hp_matrixForm M).Nondegenerate ↔ M.det ≠ 0 := by
  rw [nondegenerate_iff_gramDet_ne_zero hh (Pi.basisFun _ _), gramDet,
    hg7_matrix_gram]

theorem hg7_classes_basis : ∃ B : Module.Basis (Fin 6) hp_K
    (hg_eqH1 hg4_sigmaK b4b_root), ∀ i, B i = hg7_classes i := by
  let v : Fin 6 → pc_Vpar (pc_tuple hg4_sigmaK b4b_root) := fun a =>
    Submodule.Quotient.mk ⟨hp_certK a, hg4_sigmaK_tuple ▸ hp_certK_mem a⟩
  have hli : LinearIndependent hp_K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hmk : (Submodule.Quotient.mk (∑ a, c a • (⟨hp_certK a,
        hg4_sigmaK_tuple ▸ hp_certK_mem a⟩ : pc_Z (pc_tuple hg4_sigmaK b4b_root))) :
        pc_Vpar (pc_tuple hg4_sigmaK b4b_root)) = 0 := by
      rw [← hc]
      change Submodule.mkQ _ (∑ a, c a • _) = _
      rw [map_sum]
      simp only [map_smul]
      rfl
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hmk
    have ht : ∑ a, c a • hp_certK a ∈ pc_trivialPart hp_rootTupleK := by
      rw [← hg4_sigmaK_tuple]
      simpa using hmk
    exact congrFun (hp_certK_independent c ht)
  have hdim : Module.finrank hp_K (pc_Vpar (pc_tuple hg4_sigmaK b4b_root)) = 6 := by
    rw [hg4_sigmaK_tuple, hp_vparK_finrank]
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hdim])
  let e := LinearEquiv.ofBijective (hg4_shapiroH1 hg4_sigmaK b4b_root)
    (hg4_shapiroH1_bijective hg4_sigmaK b4b_root b63d_root_product)
  refine ⟨B.map e, fun i => ?_⟩
  simp only [Module.Basis.map_apply]
  change e (B i) = _
  have hb : B i = v i := by simp [B]
  rw [hb]
  rfl

set_option maxHeartbeats 400000 in
theorem hg7_evaluation_bijective_aux : Function.Bijective hg7_evaluation := by
  classical
  obtain ⟨B, hB⟩ := hg7_classes_basis
  have hi : Function.Injective hg7_evaluation := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    apply Module.eval_apply_injective hp_K
    apply LinearMap.ext
    intro f
    let φ : (ℚ ⊗[ℤ] hg6_cellLattice) →ₗ[ℚ] hp_K :=
      (f.restrictScalars ℚ).comp (WithJ.equiv hg7_cellAction).symm.toLinearMap
    have hφ : φ ∈ hg6_isoSpace := by
      intro y
      change f ((WithJ.equiv hg7_cellAction).symm (hg6_cellJ y)) =
        QuadraticAlgebra.omega * f ((WithJ.equiv hg7_cellAction).symm y)
      have he : (WithJ.equiv hg7_cellAction).symm (hg6_cellJ y) =
          (QuadraticAlgebra.omega : hp_K) • (WithJ.equiv hg7_cellAction).symm y := by
        apply (WithJ.equiv hg7_cellAction).injective
        rw [equiv_omega_smul]
        rfl
      rw [he, map_smul, smul_eq_mul]
    have hm : φ ∈ LinearMap.range hg6_theta := hg6_theta_range.symm ▸ hφ
    obtain ⟨u, hu⟩ := hm
    let F : hg_eqH1 hg4_sigmaK b4b_root →ₗ[hp_K] hp_K :=
      { toFun := fun u => hg6_theta u (WithJ.equiv hg7_cellAction x)
        map_add' := fun u v => by rw [map_add, LinearMap.add_apply]
        map_smul' := fun c u => by rw [map_smul, LinearMap.smul_apply]; rfl }
    have hF : F = 0 := B.ext fun i => by
      change hg6_theta (B i) (WithJ.equiv hg7_cellAction x) = 0
      rw [hB]
      exact congrFun hx i
    have hz := LinearMap.congr_fun hF u
    change hg6_theta u (WithJ.equiv hg7_cellAction x) = 0 at hz
    rw [hu] at hz
    change f x = f 0
    rw [map_zero]
    simpa only [φ, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hz
  refine ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hi⟩
  have hd := finrank_withJ hg7_cellAction
  rw [hg6_ratLattice_finrank] at hd
  change 2 * Module.finrank hp_K (WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction) = 12 at hd
  rw [Module.finrank_pi, Fintype.card_fin]
  omega


theorem hg7_scale_class_aux {W : Type*} [AddCommGroup W] [Module hp_K W]
    [Module.Finite hp_K W] (B : Module.Basis (Fin 6) hp_K W)
    (H : W →ₗ⋆[hp_K] W →ₗ[hp_K] hp_K) (hh : H.IsSymm) (hn : H.Nondegenerate)
    (c : ℚ) (hc : c ≠ 0) :
    ∃ hs : ((c : hp_K) • H).IsSymm, ∃ ns : ((c : hp_K) • H).Nondegenerate,
      detClass ((c : hp_K) • H) hs ns = detClass H hh hn := by
  have hcK : (c : hp_K) ≠ 0 := by exact_mod_cast hc
  have hs : ((c : hp_K) • H).IsSymm := by
    refine LinearMap.isSymm_def.2 fun x y => ?_
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul,
      starRingEnd_apply, show star (c : hp_K) = (c : hp_K) from by simp]
    rw [← starRingEnd_apply, hh.eq]
  have hdet : gramDet ((c : hp_K) • H) B = (c : hp_K) ^ 6 * gramDet H B := by
    simp only [gramDet, map_smul, Matrix.det_smul, Fintype.card_fin]
  have ns : ((c : hp_K) • H).Nondegenerate := by
    apply (nondegenerate_iff_gramDet_ne_zero hs B).2
    rw [hdet]
    exact mul_ne_zero (pow_ne_zero _ hcK) ((nondegenerate_iff_gramDet_ne_zero hh B).1 hn)
  refine ⟨hs, ns, ?_⟩
  have hq : gramDetℚ ((c : hp_K) • H) B = c ^ 6 * gramDetℚ H B := by
    apply (algebraMap ℚ hp_K).injective
    rw [map_mul, map_pow, algebraMap_gramDetℚ hs, algebraMap_gramDetℚ hh]
    exact hdet
  rw [detClass_eq hs ns B, detClass_eq hh hn B]
  apply mk_eq_mk_of_eq_mul (sq_mem_normSubgroup ((Units.mk0 c hc) ^ 3))
  simp only [Units.val_mk0, Units.val_pow_eq_pow_val, hq]
  ring


theorem hg7_conjugate_class_aux {n : ℕ} (M : Matrix (Fin n) (Fin n) hp_K)
    (hh : (hp_matrixForm M).IsSymm) (hn : (hp_matrixForm M).Nondegenerate) :
    ∃ hs : (hp_matrixForm (M.map (starRingEnd hp_K))).IsSymm,
    ∃ ns : (hp_matrixForm (M.map (starRingEnd hp_K))).Nondegenerate,
      detClass (hp_matrixForm (M.map (starRingEnd hp_K))) hs ns =
        detClass (hp_matrixForm M) hh hn := by
  have hm := (hg7_matrix_symm M).1 hh
  have he : M.map (starRingEnd hp_K) = M.transpose := by
    apply Matrix.ext
    intro i j
    exact congrFun (congrFun hm.eq j) i
  have hs := (hg7_matrix_symm M.transpose).2 hm.transpose
  have ns := (hg7_matrix_nondegenerate M.transpose hs).2
    (by simpa only [Matrix.det_transpose] using (hg7_matrix_nondegenerate M hh).1 hn)
  rw [he]
  refine ⟨hs, ns, ?_⟩
  rw [detClass_eq hs ns (Pi.basisFun _ _), detClass_eq hh hn (Pi.basisFun _ _)]
  apply congrArg (fun u : ℚˣ => (u : ℚˣ ⧸ normSubgroup hp_K))
  apply Units.ext
  simp only [gramDetℚ, gramDet, hg7_matrix_gram, Matrix.det_transpose]

theorem hg7_dual_class_aux {n : ℕ} (M : Matrix (Fin n) (Fin n) hp_K)
    (hh : (hp_matrixForm M).IsSymm) (hn : (hp_matrixForm M).Nondegenerate) :
    ∃ hs : (hp_matrixForm M⁻¹.transpose).IsSymm,
    ∃ ns : (hp_matrixForm M⁻¹.transpose).Nondegenerate,
      detClass (hp_matrixForm M⁻¹.transpose) hs ns = detClass (hp_matrixForm M) hh hn := by
  have hm := (hg7_matrix_symm M).1 hh
  have hs := (hg7_matrix_symm M⁻¹.transpose).2 hm.inv.transpose
  have hd := (hg7_matrix_nondegenerate M hh).1 hn
  have ns := (hg7_matrix_nondegenerate M⁻¹.transpose hs).2 (by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact inv_ne_zero hd)
  refine ⟨hs, ns, ?_⟩
  let B := Pi.basisFun hp_K (Fin n)
  have hq : gramDetℚ (hp_matrixForm M⁻¹.transpose) B =
      (gramDetℚ (hp_matrixForm M) B)⁻¹ := by
    apply (algebraMap ℚ hp_K).injective
    rw [algebraMap_gramDetℚ hs, map_inv₀, algebraMap_gramDetℚ hh]
    simp only [gramDet, B, hg7_matrix_gram, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  rw [detClass_eq hs ns B, detClass_eq hh hn B]
  apply mk_eq_mk_of_eq_mul (sq_mem_normSubgroup
    (Units.mk0 (gramDetℚ (hp_matrixForm M) B) (gramDetℚ_ne_zero hh hn B))⁻¹)
  simp only [Units.val_mk0, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hq]
  field_simp


theorem hg7_cupGram_eq : hg7_cupGram =
    (Fintype.card b4b_Group : hp_K) • g32H0 pc_zeta := by
  apply Matrix.ext
  intro i j
  exact hg6_coordCup_gram i j

theorem hg7_cupForm_eq : hp_matrixForm hg7_cupGram =
    (Fintype.card b4b_Group : hp_K) • hp_h0Form := by
  rw [hg7_cupGram_eq]
  exact map_smul (Matrix.toLinearMapₛₗ₂ (starRingEnd hp_K)
    (Pi.basisFun _ _) (Pi.basisFun _ _)) _ _

theorem hg7_cup_properties : ∃ hh : (hp_matrixForm hg7_cupGram).IsSymm,
    ∃ hn : (hp_matrixForm hg7_cupGram).Nondegenerate,
      detClass (hp_matrixForm hg7_cupGram) hh hn = classNegTwo := by
  obtain ⟨hh, hn, hd⟩ := hg7_scale_class_aux (Pi.basisFun _ (Fin 6)) hp_h0Form
    hp_h0_isSymm hp_h0_nondegenerate (Fintype.card b4b_Group)
    (by exact_mod_cast Fintype.card_ne_zero)
  rw [hg7_cupForm_eq]
  exact ⟨hh, hn, hd.trans hp_h0_detClass⟩

theorem hg7_dual_properties : ∃ hh : (hp_matrixForm hg7_cupGram⁻¹.transpose).IsSymm,
    ∃ hn : (hp_matrixForm hg7_cupGram⁻¹.transpose).Nondegenerate,
      detClass (hp_matrixForm hg7_cupGram⁻¹.transpose) hh hn = classNegTwo := by
  obtain ⟨hh, hn, hd⟩ := hg7_cup_properties
  obtain ⟨hs, ns, he⟩ := hg7_dual_class_aux hg7_cupGram hh hn
  exact ⟨hs, ns, he.trans hd⟩

theorem hg7_cellular_hermitian_aux : hg7_cellularForm.IsSymm ∧ hg7_cellularForm.Nondegenerate := by
  obtain ⟨hh, hn, _⟩ := hg7_dual_properties
  have hi := hg7_evaluation_bijective_aux.1
  have hs := hg7_evaluation_bijective_aux.2
  refine ⟨⟨fun x y => hh.eq _ _⟩, ?_⟩
  constructor
  · intro x hx
    apply hi
    rw [map_zero]
    apply hn.1
    intro y
    obtain ⟨v, rfl⟩ := hs y
    exact hx v
  · intro y hy
    apply hi
    rw [map_zero]
    apply hn.2
    intro x
    obtain ⟨v, rfl⟩ := hs x
    exact hy v


theorem hg7_cellular_discriminant_aux
    (hh : hg7_cellularForm.IsSymm) (hn : hg7_cellularForm.Nondegenerate) :
    detClass hg7_cellularForm hh hn = classNegTwo := by
  obtain ⟨hs, ns, hd⟩ := hg7_dual_properties
  let e := LinearEquiv.ofBijective hg7_evaluation hg7_evaluation_bijective_aux
  exact (HermitianClass.detClass_eq_of_equiv _ _ hg7_cellularForm
    (hp_matrixForm hg7_cupGram⁻¹.transpose) hh hn hs ns e (fun _ _ => rfl)).trans hd


theorem hg7_cellular_signature_aux : hermSignature hg7_cellularForm = (3, 3) := by
  obtain ⟨hh, hn, _⟩ := hg7_cup_properties
  have hm := (hg7_matrix_symm hg7_cupGram).1 hh
  have hd := (hg7_matrix_nondegenerate hg7_cupGram hh).1 hn
  let e := LinearEquiv.ofBijective hg7_evaluation hg7_evaluation_bijective_aux
  rw [HermitianClass.hermSignature_eq_of_equiv _ _ hg7_cellularForm
    (hp_matrixForm hg7_cupGram⁻¹.transpose) e (fun _ _ => rfl),
    hg7_signature_inverse_transpose hg7_cupGram hm hd, hg7_cupForm_eq]
  exact hg7_signature_positive_h0 (Fintype.card b4b_Group)
    (by exact_mod_cast Fintype.card_pos)


end HodgeLean.Foundations.Program
