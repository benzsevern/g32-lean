import HodgeLean.Foundations.HermitianClassDefs

noncomputable section
namespace HodgeLean.Foundations.HermitianClass
open HermitianForm
open Module

theorem hermClass_reconstruct_aux (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (x y : W) :
    h x y = algebraMap ℚ _ (traceBilin W h x y / 2) -
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-3) 0) *
        algebraMap ℚ _ (traceBilin W h x ((QuadraticAlgebra.omega :
          QuadraticAlgebra ℚ (-3) 0) • y) / 6) := by
  have hreal : traceBilin W h x y = 2 * (h x y).re := by
    simp [traceBilin, HermitianForm.reBilin]
  have himag : traceBilin W h x
      ((QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-3) 0) • y) = -6 * (h x y).im := by
    simp [traceBilin, HermitianForm.reBilin]
    ring
  rw [hreal, himag]
  have hdivReal : (2 * (h x y).re) / 2 = (h x y).re := by ring
  have hdivImag : (-6 * (h x y).im) / 6 = -(h x y).im := by ring
  rw [hdivReal, hdivImag]
  apply QuadraticAlgebra.ext
  · simp
  · simp

theorem hermClass_trace_regular_aux (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate) :
    (traceBilin W h).IsSymm ∧ (traceBilin W h).Nondegenerate := by
  have hs : (traceBilin W h).IsSymm := ⟨fun x y ↦ by
    change 2 * (h x y).re = 2 * (h y x).re
    congr 1
    have he := congrArg QuadraticAlgebra.re (hh.eq x y)
    simpa only [starRingEnd_apply, QuadraticAlgebra.re_star, zero_mul, add_zero] using he⟩
  refine ⟨hs, hs.isRefl.nondegenerate_iff_separatingLeft.2 ?_⟩
  intro x hx
  apply hn.1 x
  intro y
  rw [hermClass_reconstruct_aux W h x y, hx y, hx
    ((QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-3) 0) • y)]
  simp

theorem hermClass_trace_zero_aux (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (x : W) :
    traceQuad W h x = 0 ↔ h x x = 0 := by
  have hfixed : h x x = algebraMap ℚ _ (h x x).re :=
    QuadraticAlgebraAux.star_eq_self_iff.1 (hh.eq x x)
  constructor
  · intro hz
    have hre : (h x x).re = 0 := by
      change 2 * (h x x).re = 0 at hz
      linarith
    rw [hfixed, hre]
    simp
  · intro hz
    change 2 * (h x x).re = 0
    rw [hz]
    simp

private theorem exists_hermitian_orthogonal_basis (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    [Module.Finite (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate) :
    ∃ v : Module.Basis (Fin (Module.finrank (QuadraticAlgebra ℚ (-3) 0) W))
        (QuadraticAlgebra ℚ (-3) 0) W,
      h.IsOrthoᵢ v ∧ ∀ i, h (v i) (v i) ≠ 0 := by
  let K := QuadraticAlgebra ℚ (-3) 0
  suffices ∀ n, Module.finrank K W = n →
      ∃ v : Module.Basis (Fin n) K W, h.IsOrthoᵢ v ∧ ∀ i, h (v i) (v i) ≠ 0 by
    exact this _ rfl
  intro n hdim
  induction n generalizing W with
  | zero =>
      refine ⟨basisOfFinrankZero hdim, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      letI : Nontrivial W := nontrivial_of_finrank_eq_succ hdim
      have htrace := (hermClass_trace_regular_aux W h hh hn)
      obtain ⟨x₀, hx₀⟩ := exists_ne (0 : W)
      obtain ⟨y₀, hxy₀⟩ := not_forall.1 (fun hall ↦ hx₀ (htrace.2.1 x₀ hall))
      obtain ⟨x, hx⟩ : ∃ x, traceBilin W h x x ≠ 0 := by
        by_cases hx : traceBilin W h x₀ x₀ ≠ 0
        · exact ⟨x₀, hx⟩
        by_cases hy : traceBilin W h y₀ y₀ ≠ 0
        · exact ⟨y₀, hy⟩
        push_neg at hx hy
        refine ⟨x₀ + y₀, ?_⟩
        simp only [map_add, LinearMap.add_apply]
        rw [hx, hy, zero_add, add_zero]
        have hs := htrace.1.eq y₀ x₀
        rw [hs]
        intro hz
        apply hxy₀
        linarith
      have hxx : h x x ≠ 0 := by
        intro hz
        apply hx
        change 2 * (h x x).re = 0
        rw [hz]
        simp
      let U : Submodule K W := K ∙ x
      let V : Submodule K W := U.orthogonalBilin h
      have hdisj : Disjoint U V := by
        exact disjoint_iff.2 (LinearMap.span_singleton_inf_orthogonal_eq_bot h x hxx)
      have hcodisj : Codisjoint U V := by
        rw [codisjoint_iff, eq_top_iff]
        intro y _
        let c : K := (h x x)⁻¹ * h x y
        have hc : h x (y - c • x) = 0 := by
          simp only [map_sub, map_smul, smul_eq_mul, c]
          field_simp
          ring
        refine Submodule.mem_sup.2 ⟨c • x, ?_, y - c • x, ?_, by abel⟩
        · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
        · intro z hz
          rcases Submodule.mem_span_singleton.1 hz with ⟨r, rfl⟩
          simp [hc]
      have hcompl : IsCompl U V := ⟨hdisj, hcodisj⟩
      let hV := h.domRestrict₁₂ V V
      have hhV : hV.IsSymm := hh.domRestrict V
      have hnV : hV.Nondegenerate := by
        have hleft : hV.SeparatingLeft := by
          intro z hz
          apply Subtype.ext
          apply hn.1 z
          intro y
          let uv := (U.prodEquivOfIsCompl V hcompl).symm y
          have hy : y = uv.1 + uv.2 := by
            simpa [uv] using (U.prodEquivOfIsCompl V hcompl).apply_symm_apply y |>.symm
          rw [hy]
          have huv : h z uv.1 = 0 := by
            apply hh.isRefl.eq_zero
            exact z.property uv.1 uv.1.property
          rw [map_add, huv, zero_add]
          exact hz uv.2
        refine ⟨hleft, ?_⟩
        intro z hz
        apply hleft z
        intro y
        exact hhV.isRefl.eq_zero (hz y)
      have hdimV : Module.finrank K V = n := by
        have hadd := Submodule.finrank_add_eq_of_isCompl hcompl
        rw [finrank_span_singleton (ne_zero_of_map hxx), hdim] at hadd
        omega
      obtain ⟨v, hv, hvne⟩ := ih V hV hhV hnV hdimV
      let b := Basis.mkFinCons x v
        (by
          rintro c y hy hc
          rw [add_eq_zero_iff_neg_eq] at hc
          apply (smul_eq_zero.1 ?_).resolve_right (ne_zero_of_map hxx)
          apply hdisj.le_bot
          refine ⟨Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x), ?_⟩
          rw [← hc, Submodule.neg_mem_iff] at hy
          exact hy)
        (by
          intro z
          let uv := (U.prodEquivOfIsCompl V hcompl).symm z
          obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 uv.1.property
          refine ⟨-r, ?_⟩
          have hz : z = uv.1 + uv.2 := by
            simpa [uv] using (U.prodEquivOfIsCompl V hcompl).apply_symm_apply z |>.symm
          rw [hz, ← hr]
          simpa [add_assoc] using uv.2.property)
      refine ⟨b, ?_, ?_⟩
      · rw [Basis.coe_mkFinCons]
        intro j i
        refine Fin.cases ?_ (fun i ↦ ?_) i <;> refine Fin.cases ?_ (fun j ↦ ?_) j <;>
          intro hij <;> simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ,
            Function.comp_apply]
        · exact (hij rfl).elim
        · exact hh.isRefl.eq_zero ((v j).property x (Submodule.mem_span_singleton_self x))
        · exact (v i).property x (Submodule.mem_span_singleton_self x)
        · exact hv (ne_of_apply_ne _ hij)
      · intro i
        rw [Basis.coe_mkFinCons]
        refine Fin.cases hxx (fun i ↦ hvne i) i

theorem hermClass_diagonalize_aux (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    [Module.Finite (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate) :
    ∃ d : Fin (Module.finrank (QuadraticAlgebra ℚ (-3) 0) W) → ℚ,
      (∀ i, d i ≠ 0) ∧
      ∃ e : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (Fin (Module.finrank (QuadraticAlgebra ℚ (-3) 0) W) →
          QuadraticAlgebra ℚ (-3) 0),
        ∀ x y, diagForm d (e x) (e y) = h x y := by
  obtain ⟨v, hv, hvne⟩ := exists_hermitian_orthogonal_basis W h hh hn
  let d : Fin (finrank (QuadraticAlgebra ℚ (-3) 0) W) → ℚ := fun i ↦ (h (v i) (v i)).re
  have hfixed (i) : h (v i) (v i) = algebraMap ℚ _ (d i) := by
    exact QuadraticAlgebraAux.star_eq_self_iff.1 (hh.eq (v i) (v i))
  have hdne : ∀ i, d i ≠ 0 := by
    intro i hi
    apply hvne i
    rw [hfixed i, hi]
    simp
  have hmat : LinearMap.toMatrix₂ v v h = Matrix.diagonal (fun i ↦ algebraMap ℚ _ (d i)) := by
    apply Matrix.ext
    intro i j
    simp only [LinearMap.toMatrix₂_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j
      simp [hfixed]
    · rw [if_neg hij]
      exact hv hij
  refine ⟨d, hdne, v.equivFun, fun x y ↦ ?_⟩
  have he := star_dotProduct_toMatrix₂_mulVec (B := h)
    v (v.equivFun x) (v.equivFun y)
  simp only [LinearEquiv.symm_apply_apply] at he
  rw [← he, hmat]
  simp [diagForm_apply, dotProduct, Matrix.mulVec, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

theorem hermClass_trace_signature_aux (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    [Module.Finite (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate) :
    sigPos ((traceQuad W h).baseChange ℝ) = 2 * (hermSignature h).1 ∧
      sigNeg ((traceQuad W h).baseChange ℝ) = 2 * (hermSignature h).2 := by
  letI : Module.Finite ℚ W := Module.Finite.trans (QuadraticAlgebra ℚ (-3) 0) W
  obtain ⟨d, hd, e, he⟩ := hermClass_diagonalize_aux W h hh hn
  let qh := (hermQuadForm h).baseChange ℝ
  let qd := (hermQuadForm (diagForm (a := -3) (b := 0) d)).baseChange ℝ
  let er := (e.restrictScalars ℚ).baseChange ℚ ℝ _ _
  have heq : QuadraticMap.Equivalent qh qd := by
    refine ⟨{ toLinearEquiv := er, map_app' := fun z ↦ ?_ }⟩
    have hforms : qd.comp er.toLinearMap = qh := by
      apply baseChange_ext
      intro x
      simp [qd, qh, er, LinearEquiv.baseChange_tmul, hermQuadForm_apply, he]
    exact DFunLike.congr_fun hforms z
  have htrace : (traceQuad W h).baseChange ℝ = (2 : ℝ) • qh := by
    apply baseChange_ext
    intro x
    simp [traceQuad, traceBilin, qh, hermQuadForm_apply, HermitianForm.reBilin]
  have hscalePos (Q : QuadraticForm ℝ (TensorProduct ℚ ℝ W)) :
      sigPos ((2 : ℝ) • Q) = sigPos Q := by
    apply le_antisymm
    · obtain ⟨V, hVrank, hV⟩ := exists_finrank_eq_sigPos_and_posDef ((2 : ℝ) • Q)
      rw [← hVrank]
      apply le_sigPos_of_posDef Q
      intro x hx
      have hp := hV x hx
      change 0 < 2 * Q x at hp
      change 0 < Q x
      linarith
    · obtain ⟨V, hVrank, hV⟩ := exists_finrank_eq_sigPos_and_posDef Q
      rw [← hVrank]
      apply le_sigPos_of_posDef ((2 : ℝ) • Q)
      intro x hx
      change 0 < 2 * Q x
      exact mul_pos (by norm_num) (hV x hx)
  have hposScale : sigPos ((traceQuad W h).baseChange ℝ) = sigPos qh := by
    rw [htrace, hscalePos]
  have hnegScale : sigNeg ((traceQuad W h).baseChange ℝ) = sigNeg qh := by
    rw [sigNeg, sigNeg, htrace]
    simpa only [smul_neg, neg_smul] using hscalePos (-qh)
  have hposDiag := heq.sigPos_eq
  have hnegDiag := heq.sigNeg_eq
  have hcpos : {k : Fin (finrank (QuadraticAlgebra ℚ (-3) 0) W) × Fin 2 |
      0 < diagWeights (-3) d k} = {i | 0 < d i} ×ˢ Set.univ := by
    ext ⟨i, j⟩
    fin_cases j <;> simp [diagWeights]
  have hcneg : {k : Fin (finrank (QuadraticAlgebra ℚ (-3) 0) W) × Fin 2 |
      diagWeights (-3) d k < 0} = {i | d i < 0} ×ˢ Set.univ := by
    ext ⟨i, j⟩
    simp only [diagWeights, Rat.cast_mul, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ,
      and_true]
    have hc : (0 : ℝ) < ((![1, (3 : ℚ)] j : ℚ) : ℝ) := by
      fin_cases j <;> norm_num
    exact ⟨fun hlt ↦ Rat.cast_lt_zero.1 (lt_of_not_ge fun hd ↦
      (not_lt.2 (mul_nonneg hd hc.le)) hlt),
      fun hlt ↦ mul_neg_of_neg_of_pos (Rat.cast_lt_zero.2 hlt) hc⟩
  have hdpos : sigPos qd = 2 * (hermSignature (diagForm (a := -3) (b := 0) d)).1 := by
    rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares (equivalent_diagWeights d), hcpos,
      Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
      hermSignature_diagForm (by norm_num)]
    simp [Nat.mul_comm]
  have hdneg : sigNeg qd = 2 * (hermSignature (diagForm (a := -3) (b := 0) d)).2 := by
    rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares (equivalent_diagWeights d), hcneg,
      Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
      hermSignature_diagForm (by norm_num)]
    simp [Nat.mul_comm]
  have hsig : hermSignature h = hermSignature (diagForm (a := -3) (b := 0) d) := by
    simp only [hermSignature, Prod.mk.injEq]
    exact ⟨congrArg (fun n ↦ n / 2) hposDiag, congrArg (fun n ↦ n / 2) hnegDiag⟩
  constructor
  · rw [hposScale, hposDiag, hdpos, hsig]
  · rw [hnegScale, hnegDiag, hdneg, hsig]

end HodgeLean.Foundations.HermitianClass
