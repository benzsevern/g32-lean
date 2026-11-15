import HodgeLean.RealDefs.Compare.Markman

/-!
# The concrete homology–cohomology transport

Contraction intertwines the transpose action on homology with the **negative** action on
cohomology. This sign is part of the equivalence, rather than an equality of the two actions.

Relation to the goal: HC no distance; AV milestone no distance.
-/

namespace HodgeLean.RealDefs.Compare.Markman

set_option backward.isDefEq.respectTransparency false

open Module HodgeLean.Foundations HodgeLean.Foundations.Symplectic
open HodgeLean.Foundations.WeilHermitian HodgeLean.Foundations.HermitianForm

section Transport

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {a : ℚ}
variable (J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id})

/-- The negative generator on cohomology.
Source: the Rosati identity `contract ω ∘ Jᵀ = -J ∘ contract ω`. -/
def negativeAction : {T : V →ₗ[ℚ] V // T ∘ₗ T = a • LinearMap.id} :=
  ⟨-J.1, by ext x; simpa using LinearMap.congr_fun J.2 x⟩

example : (negativeAction J).1 = -J.1 := rfl

/-- The transposed generator on homology.
Source: Markman's `PolarizedWeilType.fT`, the transpose of the action on `H¹`. -/
def transposeAction : {T : Module.Dual ℚ V →ₗ[ℚ] Module.Dual ℚ V //
    T ∘ₗ T = a • LinearMap.id} :=
  ⟨J.1.dualMap, by
    ext φ x
    change φ (J.1 (J.1 x)) = a * φ x
    rw [apply_apply J, map_smul, smul_eq_mul]⟩

example (φ : Module.Dual ℚ V) (x : V) : (transposeAction J).1 φ x = φ (J.1 x) := rfl

/-- The Riemann form of a 2-vector on homology.
Source: `DualForm.lean`, `B_ω(φ,ψ) = ψ(contract ω φ)`. -/
noncomputable def riemannForm (ω : ⋀[ℚ]^2 V) : LinearMap.BilinForm ℚ (Module.Dual ℚ V) :=
  (Module.Dual.eval ℚ V).comp (contract ω)

example (ω : ⋀[ℚ]^2 V) (φ ψ : Module.Dual ℚ V) :
    riemannForm ω φ ψ = ψ (contract ω φ) := rfl

theorem riemannForm_skew {ω : ⋀[ℚ]^2 V} (hR : IsRosatiSkew ω J.1) :
    ∀ φ ψ, riemannForm ω ((transposeAction J).1 φ) ψ =
      -riemannForm ω φ ((transposeAction J).1 ψ) :=
  (isRosatiSkew_iff_skew ω J.1).mp hR

theorem dualForm_negative_skew {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω)
    (hR : IsRosatiSkew ω J.1) :
    ∀ x y, dualForm hω ((negativeAction J).1 x) y =
      -dualForm hω x ((negativeAction J).1 y) := by
  intro x y
  have h := (isRosatiSkew_iff_dualForm hω J.1).mp hR x y
  simpa [negativeAction] using congrArg Neg.neg h

/-- Contraction is a quadratic-field-linear equivalence from homology with the transposed
generator to cohomology with the negative generator.
Source: the Rosati identity and `contractEquiv`; external roadmap §1.2, step 4. -/
noncomputable def homologyEquiv {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω)
    (hR : IsRosatiSkew ω J.1) :
    WithJ (Module.Dual ℚ V) (transposeAction J) ≃ₗ[QuadraticAlgebra ℚ a 0]
      WithJ V (negativeAction J) :=
  { (WithJ.equiv (transposeAction J)).trans
      ((contractEquiv hω).trans (WithJ.equiv (negativeAction J)).symm) with
    map_smul' := by
      intro z φ
      let φ₀ := WithJ.equiv (transposeAction J) φ
      change contract ω (z.re • φ₀ + z.im • J.1.dualMap φ₀) =
        z.re • contract ω φ₀ + z.im • (-J.1) (contract ω φ₀)
      have hr := LinearMap.congr_fun hR φ₀
      change contract ω (J.1.dualMap φ₀) = -J.1 (contract ω φ₀) at hr
      simp [hr] }

example {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω) (hR : IsRosatiSkew ω J.1)
    (φ : WithJ (Module.Dual ℚ V) (transposeAction J)) :
    WithJ.equiv (negativeAction J) (homologyEquiv J hω hR φ) =
      contract ω (WithJ.equiv (transposeAction J) φ) := rfl

/-- The transported Hermitian forms agree on every pair of vectors.
Source: `dualForm_contract_contract` and the Rosati identity, roadmap §1.2. -/
theorem homologyEquiv_isometry {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω)
    (hR : IsRosatiSkew ω J.1)
    (φ ψ : WithJ (Module.Dual ℚ V) (transposeAction J)) :
    weilHermitian (dualForm hω) (negativeAction J) (dualForm_negative_skew J hω hR)
        (homologyEquiv J hω hR φ) (homologyEquiv J hω hR ψ) =
      weilHermitian (riemannForm ω) (transposeAction J) (riemannForm_skew J hR) φ ψ := by
  let φ₀ := WithJ.equiv (transposeAction J) φ
  let ψ₀ := WithJ.equiv (transposeAction J) ψ
  have hr := LinearMap.congr_fun hR ψ₀
  change contract ω (J.1.dualMap ψ₀) = -J.1 (contract ω ψ₀) at hr
  apply QuadraticAlgebra.ext
  · change dualForm hω (contract ω φ₀) (-J.1 (contract ω ψ₀)) = _
    rw [← hr, dualForm_contract_contract]
    rfl
  · exact dualForm_contract_contract hω φ₀ ψ₀

/-- The Gram matrices agree entry by entry in bases carried by contraction.
Source: `homologyEquiv_isometry`, roadmap §1.2, steps 3–4. -/
theorem homologyEquiv_gram {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω)
    (hR : IsRosatiSkew ω J.1) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι (QuadraticAlgebra ℚ a 0) (WithJ (Module.Dual ℚ V) (transposeAction J))) :
    LinearMap.toMatrix₂ (b.map (homologyEquiv J hω hR)) (b.map (homologyEquiv J hω hR))
      (weilHermitian (dualForm hω) (negativeAction J) (dualForm_negative_skew J hω hR)) =
    LinearMap.toMatrix₂ b b
      (weilHermitian (riemannForm ω) (transposeAction J) (riemannForm_skew J hR)) := by
  apply Matrix.ext
  intro i j
  simpa only [LinearMap.toMatrix₂_apply, Basis.map_apply] using
    homologyEquiv_isometry J hω hR (b i) (b j)

end Transport

section Basis

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {a : ℚ}
variable (J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id})
variable {ι : Type*} [Fintype ι]

/-- Markman's rational independence test is exactly independence over the quadratic algebra.
Source: expansion in the basis `(1, ω)` of the quadratic algebra; `DiscIs`. -/
theorem linearIndependent_double_iff (b : ι → V) :
    LinearIndependent ℚ (Sum.elim b (fun i => J.1 (b i))) ↔
      LinearIndependent (QuadraticAlgebra ℚ a 0) (fun i => (WithJ.equiv J).symm (b i)) := by
  classical
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h c hc i
    have hc' := congrArg (WithJ.equiv J) hc
    simp only [map_sum, equiv_smul, LinearEquiv.apply_symm_apply, map_zero] at hc'
    have hs : ∑ j, Sum.elim (fun j => (c j).re) (fun j => (c j).im) j •
        Sum.elim b (fun i => J.1 (b i)) j = 0 := by
      simpa [Fintype.sum_sum_type, Finset.sum_add_distrib] using hc'
    exact QuadraticAlgebra.ext (h _ hs (Sum.inl i)) (h _ hs (Sum.inr i))
  · intro h c hc i
    have hs : ∑ j, (⟨c (Sum.inl j), c (Sum.inr j)⟩ : QuadraticAlgebra ℚ a 0) •
        (WithJ.equiv J).symm (b j) = 0 := by
      apply (WithJ.equiv J).injective
      simpa [map_sum, equiv_smul, Finset.sum_add_distrib, Fintype.sum_sum_type] using hc
    cases i with
    | inl i => exact congrArg QuadraticAlgebra.re (h _ hs i)
    | inr i => exact congrArg QuadraticAlgebra.im (h _ hs i)

end Basis

section Negative

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
variable {a : ℚ} [Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r)]
variable (J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id})
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem negative_independent
    (b : Basis ι (QuadraticAlgebra ℚ a 0) (WithJ V J)) :
    LinearIndependent (QuadraticAlgebra ℚ a 0)
      (fun i => (WithJ.equiv (negativeAction J)).symm (WithJ.equiv J (b i))) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hc' := congrArg (WithJ.equiv (negativeAction J)) hc
  simp only [map_sum, equiv_smul, LinearEquiv.apply_symm_apply, map_zero] at hc'
  have hs : ∑ j, star (c j) • b j = 0 := by
    apply (WithJ.equiv J).injective
    simpa [map_sum, equiv_smul, negativeAction, smul_neg] using hc'
  have h := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ hs i
  simpa using congrArg star h

/-- A basis for the negative action, on the same underlying vectors.
Source: conjugating every coefficient in the quadratic field changes `J` to `−J`. -/
noncomputable def negativeBasis
    (b : Basis ι (QuadraticAlgebra ℚ a 0) (WithJ V J)) :
    Basis ι (QuadraticAlgebra ℚ a 0) (WithJ V (negativeAction J)) :=
  basisOfLinearIndependentOfCardEqFinrank' _ (negative_independent J b) (by
    have h₁ := finrank_withJ J
    have h₂ := finrank_withJ (negativeAction J)
    have h₃ := Module.finrank_eq_card_basis b
    omega)

@[simp] theorem negativeBasis_apply
    (b : Basis ι (QuadraticAlgebra ℚ a 0) (WithJ V J)) (i : ι) :
    negativeBasis J b i = (WithJ.equiv (negativeAction J)).symm (WithJ.equiv J (b i)) := by
  simp [negativeBasis]

example (b : Basis ι (QuadraticAlgebra ℚ a 0) (WithJ V J)) (i : ι) :
    WithJ.equiv (negativeAction J) (negativeBasis J b i) = WithJ.equiv J (b i) := by simp

variable (E : LinearMap.BilinForm ℚ V)
variable (hs : ∀ x y, E (J.1 x) y = -E x (J.1 y))

include hs in
theorem negative_skew : ∀ x y, E ((negativeAction J).1 x) y =
    -E x ((negativeAction J).1 y) := by
  intro x y
  simpa [negativeAction] using congrArg Neg.neg (hs x y)

/-- Reversing the generator changes the Gram matrix to its negative conjugate.
Source: the formula `E(x,Jy) + ω E(x,y)`, roadmap §1.2, step 4. -/
theorem negative_gram (b : Basis ι (QuadraticAlgebra ℚ a 0) (WithJ V J)) :
    LinearMap.toMatrix₂ (negativeBasis J b) (negativeBasis J b)
        (weilHermitian E (negativeAction J) (negative_skew J E hs)) =
      -(LinearMap.toMatrix₂ b b (weilHermitian E J hs)).map (starRingEnd _) := by
  apply Matrix.ext
  intro i j
  simp only [LinearMap.toMatrix₂_apply, Matrix.neg_apply, Matrix.map_apply]
  rw [negativeBasis_apply, negativeBasis_apply]
  apply QuadraticAlgebra.ext <;> simp [negativeAction, starRingEnd_apply]

/-- Reversing the generator multiplies the rational Gram determinant by `(-1)^dim_K`.
Source: `negative_gram` and rationality of Hermitian Gram determinants. -/
theorem negative_gramDet (hE : E.IsAlt)
    (b : Basis ι (QuadraticAlgebra ℚ a 0) (WithJ V J)) :
    gramDetℚ (weilHermitian E (negativeAction J) (negative_skew J E hs))
        (negativeBasis J b) =
      (-1) ^ Fintype.card ι * gramDetℚ (weilHermitian E J hs) b := by
  unfold gramDetℚ gramDet
  rw [negative_gram J E hs b, Matrix.det_neg]
  have hd : star (gramDet (weilHermitian E J hs) b) =
      ((LinearMap.toMatrix₂ b b (weilHermitian E J hs)).map (starRingEnd _)).det :=
    (starRingEnd (QuadraticAlgebra ℚ a 0)).map_det _
  rw [← hd]
  change ((-1 : QuadraticAlgebra ℚ a 0) ^ Fintype.card ι *
    star (gramDet (weilHermitian E J hs) b)).re = _
  rw [star_gramDet (isSymm_weilHermitian hE)]
  rw [show (-1 : QuadraticAlgebra ℚ a 0) = algebraMap ℚ _ (-1) by simp, ← map_pow]
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im, mul_zero, zero_mul, add_zero, gramDet]

end Negative

namespace Port

theorem kdEquiv_sqrtNeg (d : ℚ) (hd : 0 < d) :
    kdEquiv d hd (WeilClasses.Kd.sqrtNeg d) = QuadraticAlgebra.omega := by
  change (AlgEquiv.ofBijective _ _).symm (WeilClasses.Kd.sqrtNeg d) = _
  rw [AlgEquiv.symm_apply_eq]
  simp [WeilClasses.Kd.sqrtNeg]

/-- The field equivalence preserves the norm used in `DiscIs`.
Source: invariance of the algebra norm under an algebra equivalence. -/
theorem kdEquiv_norm (d : ℚ) (hd : 0 < d) (k : WeilClasses.Kd d) :
    WeilClasses.Kd.Nm d k = QuadraticAlgebra.norm (kdEquiv d hd k) := by
  rw [WeilClasses.Kd.Nm, ← Algebra.norm_eq_of_algEquiv (kdEquiv d hd),
    QuadraticAlgebraAux.algebraNorm_eq_norm]

/-- The inverse field equivalence has the chosen complex embedding `ω ↦ √−d`.
Source: the construction of `kdEquiv` by `QuadraticAlgebra.lift`. -/
theorem kdEquiv_symm_coe (d : ℚ) (hd : 0 < d) (z : QuadraticAlgebra ℚ (-d) 0) :
    ((kdEquiv d hd).symm z : ℂ) = (z.re : ℂ) + WeilClasses.sqrtNeg d * (z.im : ℂ) := by
  simp [kdEquiv, QuadraticAlgebra.lift_apply_apply, Rat.smul_def,
    WeilClasses.Kd.sqrtNeg, mul_comm]

end Port

end HodgeLean.RealDefs.Compare.Markman
