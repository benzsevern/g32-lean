import HodgeLean.Foundations.Program.SchoenCycleS3AffineConormalFree
import HodgeLean.Foundations.Program.SchoenCycleS3AffineIdealCotangent

/-! # Conormal bases for independent affine linear graph equations -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable {A τ υ : Type} [CommRing A]

/-- One independent equation for each normal coordinate, with its
retained free-coordinate term. -/
def pairedC3AffineLinearEquation (t : τ → A) (p : τ → υ) (i : τ) :
    MvPolynomial (τ ⊕ υ) A := X (Sum.inl i) - C (t i) * X (Sum.inr (p i))

/-- The ideal retains the actual linear equations. -/
def pairedC3AffineLinearIdeal (t : τ → A) (p : τ → υ) :
    Ideal (MvPolynomial (τ ⊕ υ) A) :=
  Ideal.span (Set.range (pairedC3AffineLinearEquation t p))

/-- Differentiation in a normal coordinate detects its own linear
equation with coefficient one and every other equation with zero. -/
theorem paired_c3_affine_linear_conormal_coordinate [DecidableEq τ] (t : τ → A) (p : τ → υ)
    (i j : τ) :
    s2e_cotangentCoordinate (pairedC3AffineLinearIdeal t p) (Sum.inl i)
      ((pairedC3AffineLinearIdeal t p).toCotangent
        ⟨pairedC3AffineLinearEquation t p j, Ideal.subset_span ⟨j, rfl⟩⟩) =
      if j = i then 1 else 0 := by
  classical
  change Ideal.Quotient.mk _ (pderiv (Sum.inl i) (pairedC3AffineLinearEquation t p j)) = _
  simp only [pairedC3AffineLinearEquation, map_sub, pderiv_mul, pderiv_C,
    zero_mul, pderiv_X, Pi.single_apply, Sum.inl.injEq, Sum.inr_ne_inl,
    ite_false, mul_zero, add_zero, sub_zero]
  split_ifs <;> simp only [map_one, map_zero]

/-- Independence holds over the quotient coordinate ring, without a
field hypothesis and without constraints on the free coordinates. -/
theorem paired_c3_affine_linear_conormal_independent (t : τ → A) (p : τ → υ) :
    LinearIndependent (MvPolynomial (τ ⊕ υ) A ⧸ pairedC3AffineLinearIdeal t p)
      (fun j => (pairedC3AffineLinearIdeal t p).toCotangent
        ⟨pairedC3AffineLinearEquation t p j, Ideal.subset_span ⟨j, rfl⟩⟩) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s a ha j hj
  have h := congrArg
    (s2e_cotangentCoordinateQuotient (pairedC3AffineLinearIdeal t p) (Sum.inl j)) ha
  simp only [map_sum, map_smul, map_zero] at h
  simp only [s2e_cotangentCoordinateQuotient, LinearMap.coe_mk, AddHom.coe_mk,
    paired_c3_affine_linear_conormal_coordinate] at h
  simpa only [smul_eq_mul, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq',
    ite_eq_left hj] using h

/-- The normal equation classes form a basis of the actual ideal modulo
its square, rather than a vector space with matching dimension. -/
def pairedC3AffineLinearConormalBasis (t : τ → A) (p : τ → υ) :
    Module.Basis τ (MvPolynomial (τ ⊕ υ) A ⧸ pairedC3AffineLinearIdeal t p)
      (pairedC3AffineLinearIdeal t p).Cotangent :=
  Module.Basis.mk (paired_c3_affine_linear_conormal_independent t p)
    (s2e_cotangent_generators_span (pairedC3AffineLinearEquation t p))

/-- The basis identifies the actual generators with their classes. -/
theorem paired_c3_affine_linear_conormal_basis_apply (t : τ → A) (p : τ → υ) (j : τ) :
    pairedC3AffineLinearConormalBasis t p j =
      (pairedC3AffineLinearIdeal t p).toCotangent
        ⟨pairedC3AffineLinearEquation t p j, Ideal.subset_span ⟨j, rfl⟩⟩ :=
  Module.Basis.mk_apply _ _ _

/-- Sheafification preserves the frame on the affine graph. -/
def pairedC3AffineLinearConormalSheafIso (t : τ → A) (p : τ → υ) :
    let Q := CommRingCat.of (MvPolynomial (τ ⊕ υ) A ⧸ pairedC3AffineLinearIdeal t p)
    tilde (ModuleCat.of Q (pairedC3AffineLinearIdeal t p).Cotangent) ≅
      (SheafOfModules.free (R := (Spec Q).ringCatSheaf) τ : (Spec Q).Modules) :=
  (tilde.functor _).mapIso (pairedC3AffineLinearConormalBasis t p).repr.toModuleIso ≪≫
    tildeFinsupp τ

/-- The actual affine quotient immersion has the equation-indexed
conormal frame; no dimension-only replacement is used. -/
def pairedC3AffineLinearImmersionConormalIso (t : τ → A) (p : τ → υ) :
    let I := pairedC3AffineLinearIdeal t p
    let Q := CommRingCat.of (MvPolynomial (τ ⊕ υ) A ⧸ I)
    s2c_conormal (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
      (SheafOfModules.free (R := (Spec Q).ringCatSheaf) τ : (Spec Q).Modules) :=
  s2e_affineQuotientConormalIso (R := CommRingCat.of (MvPolynomial (τ ⊕ υ) A))
    (pairedC3AffineLinearIdeal t p) ≪≫ pairedC3AffineLinearConormalSheafIso t p

end HodgeLean.Foundations.Program.G32Native
