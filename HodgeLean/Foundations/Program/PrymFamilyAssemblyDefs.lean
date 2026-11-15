import HodgeLean.Foundations.Program.TorusAlgebraization
import HodgeLean.Foundations.Program.RelativeTorusAbelian
import HodgeLean.Foundations.Program.PrymVariationFrames
import HodgeLean.Papers.G32FamilyDefs

/-! # B6-3g, part 1: data for the fibre fields of the Prym family

For a complex abelian variety `X` with lattice `Λ_X = b2_abelianLattice X` (its `H₁(X(ℂ), ℤ)`),
an additive endomorphism `φ` of `Λ_X` acts on `H¹(X(ℂ); ℚ)` through the period equivalence
`abelianPeriodEquiv X : H¹(X(ℂ); ℚ) ≃ (Λ_X →+ ℚ)` by precomposition. This is the dualization
from `H₁` to `H¹` used by the field `W` of `g32t_Sixfold`.

For a B5 model `b5_model Λ F hF Q` of lattice data, the marking `b5_periodEquiv` carries a lattice
endomorphism and the integral form `Q` to the model's lattice; the carried form gives the
degree-two class through `latticeClassHQ`, the cup-product convention of `cupProductOf`.

Only data are defined here. No definition selects a witness from an open statement, and none is
a proposition. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.AppellHumbert
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

/-- Precomposition with an additive endomorphism, a `ℚ`-linear map on rational characters.
Source: Bourbaki, *Algèbre*, ch. II, §2.5 (the transpose of a linear map). -/
def b63g_precomp {Λ : Type*} [AddCommGroup Λ] (φ : Λ →+ Λ) : (Λ →+ ℚ) →ₗ[ℚ] (Λ →+ ℚ) where
  toFun f := f.comp φ
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

example {Λ : Type*} [AddCommGroup Λ] (φ : Λ →+ Λ) (f : Λ →+ ℚ) (x : Λ) :
    b63g_precomp φ f x = f (φ x) := rfl

/-- **The dual operator on `H¹`.** For an additive endomorphism `φ` of `Λ_X = H₁(X(ℂ), ℤ)`, the
rational endomorphism `x ↦ P⁻¹ (P x ∘ φ)` of `H¹(X(ℂ); ℚ)`, with `P = abelianPeriodEquiv X`:
the transpose of `φ` under `H¹(X, ℚ) = Hom(Λ_X, ℚ)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`H¹(X, ℤ) = Hom(Λ, ℤ)`)
and §1.2 (rational representation); `abelianPeriodEquiv`. -/
def b63g_dualOperator (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (φ : b2_abelianLattice X →+ b2_abelianLattice X) :
    HQ X 1 →ₗ[ℚ] HQ X 1 :=
  (abelianPeriodEquiv X).symm.toLinearMap ∘ₗ b63g_precomp φ ∘ₗ
    (abelianPeriodEquiv X).toLinearMap

/-- The periods of `J x` are the periods of `x` on `φ`-images. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (φ : b2_abelianLattice X →+ b2_abelianLattice X) (x : HQ X 1)
    (l : b2_abelianLattice X) :
    abelianPeriodEquiv X (b63g_dualOperator X φ x) l = abelianPeriodEquiv X x (φ l) := by
  simp [b63g_dualOperator, b63g_precomp]

/-- **The lattice endomorphism carried to the model.** `e ∘ φ ∘ e⁻¹` on the lattice of the B5
model, with `e = b5_periodEquiv` the B5 marking.
Source: Birkenhake–Lange, §1.1–§1.2; `b5_periodEquiv`. -/
def b63g_modelMap (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b2_abelianLattice (b5_model Λ F hF Q) →+ b2_abelianLattice (b5_model Λ F hF Q) :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom.comp
    (φ.comp (b5_periodEquiv Λ F hF Q hQ).symm.toAddMonoidHom)

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ) (l : Λ) :
    b63g_modelMap Λ F hF Q hQ φ (b5_periodEquiv Λ F hF Q hQ l) =
      b5_periodEquiv Λ F hF Q hQ (φ l) := by
  simp [b63g_modelMap]

/-- **The integral form carried to the model**, `(l, m) ↦ Q (e⁻¹ l) (e⁻¹ m)`, with the original
normalization and orientation of `Q`.
Source: Birkenhake–Lange, §2.2 and §5.3; `b5_periodEquiv`. -/
def b63g_modelForm (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    LinearMap.BilinForm ℤ (b2_abelianLattice (b5_model Λ F hF Q)) :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  Q.compl₁₂ (b5_periodEquiv Λ F hF Q hQ).symm.toAddMonoidHom.toIntLinearMap
    (b5_periodEquiv Λ F hF Q hQ).symm.toAddMonoidHom.toIntLinearMap

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (l m : Λ) :
    b63g_modelForm Λ F hF Q hQ (b5_periodEquiv Λ F hF Q hQ l) (b5_periodEquiv Λ F hF Q hQ m) =
      Q l m := by
  simp [b63g_modelForm]

/-- **The degree-two class of the model**: `latticeClassHQ` of the carried form, that is
`[E] = ∑ᵢ ∑ⱼ (E(eᵢ, eⱼ)/2) eᵢ* ∧ eⱼ*` carried to `⋀² H¹` by the inverse period equivalence
and to `H²` by the cup-wedge map of `cupProductOf`.
Source: Birkenhake–Lange, §1.3 and Lemma 1.3.1 (`H²(X, ℤ) = Alt²(Λ, ℤ)`); `latticeClassHQ`. -/
def b63g_modelClass (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    HQ (b5_model Λ F hF Q) 2 :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  latticeClassHQ (b5_model Λ F hF Q) (b2_bilinToAddHom (b63g_modelForm Λ F hF Q hQ))

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b63g_modelClass Λ F hF Q hQ =
      latticeClassHQ (b5_model Λ F hF Q) (b2_bilinToAddHom (b63g_modelForm Λ F hF Q hQ)) :=
  rfl

/-- **The rational operator of the model**: the dual operator on `H¹` of the model of the
carried lattice endomorphism.
Source: Birkenhake–Lange, §1.2 (rational representation); `b63g_dualOperator`,
`b63g_modelMap`. -/
def b63g_modelOperator (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ) :
    HQ (b5_model Λ F hF Q) 1 →ₗ[ℚ] HQ (b5_model Λ F hF Q) 1 :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  b63g_dualOperator (b5_model Λ F hF Q) (b63g_modelMap Λ F hF Q hQ φ)

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (x : HQ (b5_model Λ F hF Q) 1) (l : Λ) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    abelianPeriodEquiv _ (b63g_modelOperator Λ F hF Q hQ φ x) (b5_periodEquiv Λ F hF Q hQ l) =
      abelianPeriodEquiv _ x (b5_periodEquiv Λ F hF Q hQ (φ l)) := by
  simp [b63g_modelOperator, b63g_dualOperator, b63g_precomp, b63g_modelMap]

/-- **The rotation of `ℤ²`**, `e₀ ↦ e₁`, `e₁ ↦ -e₀`: multiplication by `i` on `ℤ + iℤ`.
Used only by the positive-rank checks.
Source: Birkenhake–Lange, §1.1 (the elliptic curve `ℂ ⧸ (ℤ + iℤ)` has `i` as an
endomorphism). -/
def b63g_rot : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) :=
  (Matrix.toLin' !![0, -1; 1, 0]).toAddMonoidHom

example : b63g_rot (Pi.single 0 1) = Pi.single 1 1 := by
  ext i
  fin_cases i <;> simp [b63g_rot]

/-- `b63g_rot ∘ b63g_rot = -1`.
Source: `i² = -1`. -/
theorem b63g_rot_sq : ∀ l, b63g_rot (b63g_rot l) = (-(1 : ℤ)) • l := by
  intro l
  ext i
  fin_cases i <;> simp [b63g_rot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

example : b63g_rot (b63g_rot (Pi.single 0 1)) = -Pi.single 0 1 := by
  simpa using b63g_rot_sq (Pi.single 0 1)

/-- The rotation is skew for the standard form `b2_stdForm`.
Source: `det (R x, y) = det (x, R⁻¹ y)` and `R⁻¹ = -R`. -/
theorem b63g_rot_skew : ∀ l m, b2_stdForm (b63g_rot l) m = -b2_stdForm l (b63g_rot m) := by
  intro l m
  simp [b2_stdForm, b63g_rot, Matrix.toLinearMap₂'_apply', Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

example : b2_stdForm (b63g_rot (Pi.single 0 1)) (Pi.single 0 1) = -1 := by
  simp [b2_stdForm, b63g_rot, Matrix.toLinearMap₂'_apply', Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

/-- The rotation preserves the standard filtration `ℂ · (e₀ + i e₁)`, acting on it by `-i`.
Source: Birkenhake–Lange, §1.2 (analytic representation of `i` on `ℂ ⧸ (ℤ + iℤ)`). -/
theorem b63g_rot_stdF : b2_stdF ≤ b2_stdF.comap (b2_cplxMap b63g_rot) := by
  have h0 : b63g_rot (Pi.single 0 1) = Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp [b63g_rot]
  have h1 : b63g_rot (Pi.single 1 1) = -Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp [b63g_rot]
  rw [b2_stdF, Submodule.span_singleton_le_iff_mem, Submodule.mem_comap,
    Submodule.mem_span_singleton]
  refine ⟨-Complex.I, ?_⟩
  simp only [map_add, b2_cplxMap, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
    h0, h1, smul_add, TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.tmul_neg,
    mul_one]
  rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg],
    ← TensorProduct.neg_tmul, add_comm]

example : b2_cplxMap b63g_rot ((1 : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ)) =
    (1 : ℂ) ⊗ₜ[ℤ] (Pi.single 1 1 : Fin 2 → ℤ) := by
  have h0 : b63g_rot (Pi.single 0 1) = Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp [b63g_rot]
  simp [b2_cplxMap, h0]

end HodgeLean.Foundations.Program
