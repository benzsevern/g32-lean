import HodgeLean.Foundations.Program.PrymParabolicDiscriminantProofs

/-! # H7: cellular discriminant and norm-class invariance

Implication from the cellular evaluation and coordinate cup construction to its dual
determinant class. The geometric pairing identification and B5-model transport are deferred.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Foundations.WeilHermitian
open HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

/-- Evaluation is a bijection: the H6 classes form a basis and H5 identifies their cohomology
with the `K`-linear dual of the saturated rational lattice.
Source: Hatcher, §3.1, Theorem 3.2; `hg6_isotypic_comparison`, `hp_certK_independent`. -/
theorem hg7_evaluation_bijective : Function.Bijective hg7_evaluation :=
  hg7_evaluation_bijective_aux 

/-- The cup-dual form is Hermitian and nondegenerate.
Source: Bourbaki, Algebra, Ch. IX, §1; `hg6_coordCup_gram`, `hp_h0_nondegenerate`. -/
theorem hg7_cellular_hermitian : hg7_cellularForm.IsSymm ∧ hg7_cellularForm.Nondegenerate :=
  hg7_cellular_hermitian_aux 

/-- The cup-dual form on the saturated rational cellular lattice has class `[-2]`.
The proof arguments only supply the domain of `detClass`.
Source: G32 v0.16, proof of Proposition 6.3; `hg6_coordCup_gram`, `hp_h0_detClass`. -/
theorem hg7_cellular_discriminant
    (hh : hg7_cellularForm.IsSymm) (hn : hg7_cellularForm.Nondegenerate) :
    detClass hg7_cellularForm hh hn = classNegTwo :=
  hg7_cellular_discriminant_aux hh hn

/-- Duality preserves the signature of the coordinate cup form.
Source: Sylvester's law of inertia; G32 v0.16, Proposition 6.3; `hp_h0_hermSignature`. -/
theorem hg7_cellular_signature : hermSignature hg7_cellularForm = (3, 3) :=
  hg7_cellular_signature_aux 

/-- Every nonzero rational scale preserves the determinant class in rank six,
including negative scales: `c⁶ = N(c³)`.
Source: Serre, A Course in Arithmetic, Ch. III, §1.1; `gramDetℚ_basis_change`. -/
theorem hg7_scale_class {W : Type*} [AddCommGroup W] [Module hp_K W]
    [Module.Finite hp_K W] (B : Module.Basis (Fin 6) hp_K W)
    (H : W →ₗ⋆[hp_K] W →ₗ[hp_K] hp_K) (hh : H.IsSymm) (hn : H.Nondegenerate)
    (c : ℚ) (hc : c ≠ 0) :
    ∃ hs : ((c : hp_K) • H).IsSymm, ∃ ns : ((c : hp_K) • H).Nondegenerate,
      detClass ((c : hp_K) • H) hs ns = detClass H hh hn :=
  hg7_scale_class_aux B H hh hn c hc

/-- Conjugation preserves the determinant class of any nondegenerate Hermitian matrix:
its determinant is rational and hence fixed by conjugation.
Source: Bourbaki, Algebra, Ch. IX, §1; `HermitianForm.star_gramDet`. -/
theorem hg7_conjugate_class {n : ℕ} (M : Matrix (Fin n) (Fin n) hp_K)
    (hh : (hp_matrixForm M).IsSymm) (hn : (hp_matrixForm M).Nondegenerate) :
    ∃ hs : (hp_matrixForm (M.map (starRingEnd hp_K))).IsSymm,
    ∃ ns : (hp_matrixForm (M.map (starRingEnd hp_K))).Nondegenerate,
      detClass (hp_matrixForm (M.map (starRingEnd hp_K))) hs ns =
        detClass (hp_matrixForm M) hh hn :=
  hg7_conjugate_class_aux M hh hn

/-- The linear dual has inverse transpose Gram matrix and the same determinant class.
For rational `d ≠ 0`, the ratio `d⁻¹/d = N(d⁻¹)`.
Source: Bourbaki, Algebra, Ch. IX, §1; Serre, A Course in Arithmetic, Ch. III, §1.1. -/
theorem hg7_dual_class {n : ℕ} (M : Matrix (Fin n) (Fin n) hp_K)
    (hh : (hp_matrixForm M).IsSymm) (hn : (hp_matrixForm M).Nondegenerate) :
    ∃ hs : (hp_matrixForm M⁻¹.transpose).IsSymm,
    ∃ ns : (hp_matrixForm M⁻¹.transpose).Nondegenerate,
      detClass (hp_matrixForm M⁻¹.transpose) hs ns = detClass (hp_matrixForm M) hh hn :=
  hg7_dual_class_aux M hh hn

/-- The lattice input is nonzero of rank twelve, and its centre is nontrivial.
This check uses H5 only, independently of the seven draft bodies. -/
example : Module.finrank ℤ hg6_cellLattice = 12 ∧
    Module.finrank hp_K (WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction) = 6 ∧
    hg6_cellCentreL ≠ LinearMap.id := by
  refine ⟨hg6_cellLattice_finrank, ?_, hg6_cellCentreL_ne_id⟩
  exact b64b_rank_six _ (Classical.choice hg6_cellLattice_basis) hg7_cellAction

/-- The matrix inputs for scale, conjugation and duality have rank six, are nondegenerate,
and have a nontrivial determinant class. All these input checks use H1 only. -/
example : Module.finrank hp_K (Fin 6 → hp_K) = 6 ∧
    hp_h0Form.IsSymm ∧ hp_h0Form.Nondegenerate ∧ (-2 : ℚ) ≠ 0 ∧
    detClass hp_h0Form hp_h0_isSymm hp_h0_nondegenerate ≠ 1 := by
  refine ⟨by simp, hp_h0_isSymm, hp_h0_nondegenerate, by norm_num, ?_⟩
  rw [hp_h0_detClass]
  exact class_neg_two_ne_one

example : Function.Bijective hg7_evaluation := hg7_evaluation_bijective

example : hg7_cellularForm.IsSymm ∧ hg7_cellularForm.Nondegenerate :=
  hg7_cellular_hermitian

/-- Chain check to the determinant-class target shared by the geometric lattice consumers.
The identification of this cellular form with their intersection form is still required. -/
example : detClass hg7_cellularForm hg7_cellular_hermitian.1 hg7_cellular_hermitian.2 =
    classNegTwo :=
  hg7_cellular_discriminant _ _

example : hermSignature hg7_cellularForm = (3, 3) := hg7_cellular_signature

example : ∃ hs : ((-2 : hp_K) • hp_h0Form).IsSymm,
    ∃ ns : ((-2 : hp_K) • hp_h0Form).Nondegenerate,
      detClass ((-2 : hp_K) • hp_h0Form) hs ns =
        detClass hp_h0Form hp_h0_isSymm hp_h0_nondegenerate := by
  simpa only [Rat.cast_neg, Rat.cast_ofNat] using
    hg7_scale_class (Pi.basisFun hp_K (Fin 6)) hp_h0Form hp_h0_isSymm
      hp_h0_nondegenerate (-2) (by norm_num)

example : ∃ hs : (hp_matrixForm ((g32H0 pc_zeta).map (starRingEnd hp_K))).IsSymm,
    ∃ ns : (hp_matrixForm ((g32H0 pc_zeta).map (starRingEnd hp_K))).Nondegenerate,
      detClass (hp_matrixForm ((g32H0 pc_zeta).map (starRingEnd hp_K))) hs ns =
        detClass hp_h0Form hp_h0_isSymm hp_h0_nondegenerate :=
  hg7_conjugate_class (g32H0 pc_zeta) hp_h0_isSymm hp_h0_nondegenerate

example : ∃ hs : (hp_matrixForm (g32H0 pc_zeta)⁻¹.transpose).IsSymm,
    ∃ ns : (hp_matrixForm (g32H0 pc_zeta)⁻¹.transpose).Nondegenerate,
      detClass (hp_matrixForm (g32H0 pc_zeta)⁻¹.transpose) hs ns =
        detClass hp_h0Form hp_h0_isSymm hp_h0_nondegenerate :=
  hg7_dual_class (g32H0 pc_zeta) hp_h0_isSymm hp_h0_nondegenerate

end HodgeLean.Foundations.Program
