import HodgeLean.Foundations.Program.PrymFamilyAssemblyProofs
import HodgeLean.Papers.G32Family

/-! # B6-3g, part 1: the fibre fields of the Prym family on a B5 model (FROZEN SPEC)

Each public theorem is the matching `_aux` theorem of `PrymFamilyAssemblyProofs.lean`.

**Claimed.** For a complex abelian variety `X` and an additive endomorphism `φ` of its lattice
`Λ_X = H₁(X(ℂ), ℤ)`, the dual operator `J = b63g_dualOperator X φ` on `H¹(X(ℂ); ℚ)` satisfies
`J² = -n` when `φ² = -n`; preserves every Hodge piece of the package's weight-one structure when
`φ_ℂ` preserves the period filtration; and is Rosati-skew for the 2-vector of
`latticeClassHQ X Q` when `φ` is skew for the integral form `Q`. For B5 data
`(Λ, F, Q)` with weight-one and Riemann certificates, the rank of `Λ` is twice the dimension of
the model; the marking `b5_periodEquiv` carries `φ²= -n`, filtration preservation and
`Q`-skewness to the model lattice; the carried form is a Riemann form for the model's period
filtration, and it equals the original B5 Chern pairing `b5_originalChernPairing`.

These are implications from lattice data. Together they give the field `W` of
`g32t_Sixfold` (with `n = 3`), its `pol` as `b63g_modelClass`, and the fields `nondegenerate`
and `rosati` of `g32h_PrymFamily` on the model; they reduce `dim_eq` to the rank of the lattice
(examples at the end of the file).

**Not claimed.** That the actual Prym centre operator satisfies the three lattice hypotheses on
the transported filtration of B6-3f (part 2 of stage 3g); positivity `PolarizationPositive`
(part 4); the Hodge ranks `g32h_h10`, `g32h_h01` (part 3); the assembly of `S := V` with marked
Nielsen tuples and the rational `d1_PolarizedVHS` (parts 5 and 6). Nothing here concerns a
discriminant, algebraicity of Weil classes or dominance. The selected model of
`b4b_algebraization` is not used. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Foundations.Symplectic TopologicalSpace
open HodgeLean.Foundations.AppellHumbert HodgeLean.Papers
open scoped TensorProduct Manifold ContDiff

namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-! ## The dual operator on `H¹` of an abelian variety -/

/-- **The quadratic relation dualizes.** If `φ ∘ φ = -n` on `Λ_X`, then `J ∘ J = -n` on
`H¹(X(ℂ); ℚ)` for the dual operator `J`: transposition reverses composition, and
`abelianPeriodEquiv` is a linear equivalence.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1–§1.2;
`abelianPeriodEquiv`. -/
theorem b63g_dualOperator_sq (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (n : ℤ)
    (φ : b2_abelianLattice X →+ b2_abelianLattice X) (hφ : ∀ l, φ (φ l) = (-n) • l) :
    (b63g_dualOperator X φ).comp (b63g_dualOperator X φ) = (-(n : ℚ)) • LinearMap.id :=
  b63g_dualOperator_sq_aux X n φ hφ

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (n : ℤ)
    (φ : b2_abelianLattice X →+ b2_abelianLattice X) (hφ : ∀ l, φ (φ l) = (-n) • l) :
    (b63g_dualOperator X φ).comp (b63g_dualOperator X φ) = (-(n : ℚ)) • LinearMap.id :=
  b63g_dualOperator_sq X n φ hφ

/-- **Hodge compatibility dualizes.** If `φ_ℂ` preserves the period filtration
`b2_abelianF X` of `ℂ ⊗ Λ_X`, then `J_ℂ` preserves every piece of the weight-one Hodge structure
of `H¹(X(ℂ); ℚ)` in `abelianVarietyCohomologyOf`, the structure the field `W` of
`g32t_Sixfold` uses. `H^{1,0}` is the annihilator of the filtration under the perfect period
pairing (`b2_abelianHodgeF_eq`), `H^{0,1}` is its conjugate, `J` is rational, and the other
pieces are zero.
Source: Birkenhake–Lange, §1.2 and Theorem 1.4.1; `b2_abelianHodgeF_eq`,
`b2_abelianEnd_preserves`. -/
theorem b63g_dualOperator_hodge (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (hφ : b2_abelianF X ≤ (b2_abelianF X).comap (b2_cplxMap φ)) :
    letI := (torusCohomology_cupProductOf X).finite
    ∀ pq : ℤ × ℤ,
      ((abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
          (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H pq).map
          ((b63g_dualOperator X φ).baseChange ℂ) ≤
        (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
          (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H pq :=
  b63g_dualOperator_hodge_aux X φ hφ

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (hφ : b2_abelianF X ≤ (b2_abelianF X).comap (b2_cplxMap φ)) :
    letI := (torusCohomology_cupProductOf X).finite
    ∀ pq : ℤ × ℤ,
      ((abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
          (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H pq).map
          ((b63g_dualOperator X φ).baseChange ℂ) ≤
        (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
          (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H pq :=
  b63g_dualOperator_hodge X φ hφ

/-- **Rosati skewness dualizes.** If `Q (φ l) m = -Q l (φ m)` on `Λ_X`, then the dual operator
is Rosati-skew (`IsRosatiSkew`) for the 2-vector `polarizationVec` of the class
`latticeClassHQ X Q`: under `H₁ ⊗ ℚ = (H¹)^∨` the transpose of `J` is `φ`, and the form
`B_ω` of `ω` is the alternation `(Q - Qᵀ)/2` of `Q`, skew for `φ` as `Q` is.
Source: Birkenhake–Lange, §1.3, Lemma 1.3.1 and §5.1 (the Rosati involution);
`isRosatiSkew_iff_skew`, `latticeClassHQ`. -/
theorem b63g_dualOperator_rosati (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hskew : ∀ l m, Q (φ l) m = -Q l (φ m)) :
    letI := (torusCohomology_cupProductOf X).finite
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf X)
      (latticeClassHQ X (b2_bilinToAddHom Q))) (b63g_dualOperator X φ) :=
  b63g_dualOperator_rosati_aux X φ Q hskew

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hskew : ∀ l m, Q (φ l) m = -Q l (φ m)) :
    letI := (torusCohomology_cupProductOf X).finite
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf X)
      (latticeClassHQ X (b2_bilinToAddHom Q))) (b63g_dualOperator X φ) :=
  b63g_dualOperator_rosati X φ Q hskew

/-! ## Transport through the B5 marking -/

/-- **Rank transfer.** The rank of `Λ` is twice the dimension of its B5 model: `b5_periodEquiv`
is an isomorphism onto the model's lattice, whose rank is `2 dim` (`b2_abelian_finrank`,
`b2_two_mul_finrank`).
Source: Birkenhake–Lange, §1.1; `b5_periodEquiv`, `b2_abelian_finrank`. -/
theorem b63g_model_finrank (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    Module.finrank ℤ Λ = 2 * dim (b5_model Λ F hF Q).left :=
  b63g_model_finrank_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    Module.finrank ℤ Λ = 2 * dim (b5_model Λ F hF Q).left :=
  b63g_model_finrank Λ F hF Q hQ

/-- **The quadratic relation is carried to the model lattice**, through `e ∘ φ ∘ e⁻¹`.
Source: `b5_periodEquiv` is an additive equivalence; Birkenhake–Lange, §1.2. -/
theorem b63g_modelMap_sq (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (n : ℤ) (φ : Λ →+ Λ)
    (hφ : ∀ l, φ (φ l) = (-n) • l) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l, b63g_modelMap Λ F hF Q hQ φ (b63g_modelMap Λ F hF Q hQ φ l) = (-n) • l :=
  b63g_modelMap_sq_aux Λ F hF Q hQ n φ hφ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (n : ℤ) (φ : Λ →+ Λ)
    (hφ : ∀ l, φ (φ l) = (-n) • l) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l, b63g_modelMap Λ F hF Q hQ φ (b63g_modelMap Λ F hF Q hQ φ l) = (-n) • l :=
  b63g_modelMap_sq Λ F hF Q hQ n φ hφ

/-- **Filtration preservation is carried to the model.** If `φ_ℂ` preserves `F`, the carried
map preserves the model's period filtration, which is the image of `F` under the marking
(`b5_period_filtration`).
Source: Birkenhake–Lange, §1.2 and Theorem 4.5.1; `b5_period_filtration`. -/
theorem b63g_modelMap_filtration (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b2_abelianF (b5_model Λ F hF Q) ≤
      (b2_abelianF (b5_model Λ F hF Q)).comap (b2_cplxMap (b63g_modelMap Λ F hF Q hQ φ)) :=
  b63g_modelMap_filtration_aux Λ F hF Q hQ φ hφ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b2_abelianF (b5_model Λ F hF Q) ≤
      (b2_abelianF (b5_model Λ F hF Q)).comap (b2_cplxMap (b63g_modelMap Λ F hF Q hQ φ)) :=
  b63g_modelMap_filtration Λ F hF Q hQ φ hφ

/-- **The carried form is a Riemann form for the model.** Alternation, isotropy of the
filtration and positivity are carried along the marking, whose complexification maps `F` onto
the model's period filtration (`b5_period_filtration`) and commutes with conjugation.
Source: Birkenhake–Lange, §4.2 (Riemann relations) and §5.3; `b5_period_filtration`. -/
theorem b63g_modelForm_riemann (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b2_IsRiemannForm (b2_abelianLattice (b5_model Λ F hF Q)) (b2_abelianF (b5_model Λ F hF Q))
      (b63g_modelForm Λ F hF Q hQ) :=
  b63g_modelForm_riemann_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b2_IsRiemannForm (b2_abelianLattice (b5_model Λ F hF Q)) (b2_abelianF (b5_model Λ F hF Q))
      (b63g_modelForm Λ F hF Q hQ) :=
  b63g_modelForm_riemann Λ F hF Q hQ

/-- **Skewness is carried to the model.** If `φ` is skew for `Q`, the carried map is skew for
the carried form.
Source: Birkenhake–Lange, §5.1; `b5_periodEquiv` is an additive equivalence. -/
theorem b63g_modelForm_skew (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hskew : ∀ l m, Q (φ l) m = -Q l (φ m)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l m, b63g_modelForm Λ F hF Q hQ (b63g_modelMap Λ F hF Q hQ φ l) m =
      -b63g_modelForm Λ F hF Q hQ l (b63g_modelMap Λ F hF Q hQ φ m) :=
  b63g_modelForm_skew_aux Λ F hF Q hQ φ hskew

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hskew : ∀ l m, Q (φ l) m = -Q l (φ m)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l m, b63g_modelForm Λ F hF Q hQ (b63g_modelMap Λ F hF Q hQ φ l) m =
      -b63g_modelForm Λ F hF Q hQ l (b63g_modelMap Λ F hF Q hQ φ m) :=
  b63g_modelForm_skew Λ F hF Q hQ φ hskew

/-- **The carried form is the original B5 Chern pairing**, with no rescaling: the degree-two
class `b63g_modelClass` is built from the unscaled, original-orientation form.
Source: `b5_polarization_normalized`; Birkenhake–Lange, §2.2. -/
theorem b63g_modelForm_original (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l m, b63g_modelForm Λ F hF Q hQ l m = b5_originalChernPairing Λ F hF Q hQ l m :=
  b63g_modelForm_original_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l m, b63g_modelForm Λ F hF Q hQ l m = b5_originalChernPairing Λ F hF Q hQ l m :=
  b63g_modelForm_original Λ F hF Q hQ

/-! ## Positive-rank and rejected-case checks

The lattice hypotheses of the model statements hold for the standard elliptic data
`(ℤ², b2_stdF, b2_stdForm)` with the rotation `b63g_rot` (`n = 1`): the lattice has rank two and
the operator is nonzero, so neither a zero lattice nor a zero operator is the only instance.
The skewness hypothesis is not automatic: the idempotent `b2_skewIdem` fails it. -/

/-- The rotation is not zero, and the lattice has rank two. -/
example : b63g_rot ≠ 0 ∧ Module.finrank ℤ (Fin 2 → ℤ) = 2 := by
  refine ⟨fun h ↦ ?_, by simp⟩
  have h0 := congrArg (fun f : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) ↦ f (Pi.single 0 1) 1) h
  simp [b63g_rot] at h0

/-- The model statements apply to the elliptic data with the rotation: the hypotheses
`b63g_rot_sq`, `b63g_rot_stdF` and `b63g_rot_skew` are theorems of the definitions file, not
binders. The result is a Weil action with `J² = -1` on `H¹` of the elliptic model, whose
lattice has rank two. -/
example :
    letI := b5_groupObj _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
    letI : IsIntegral b5_elliptic.left := b5_integral_aux _ _ b2_std_isWeightOne _
      b2_std_isRiemannForm
    letI := b5_smooth_aux _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
    letI := b5_projective_aux _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
    letI := (torusCohomology_cupProductOf b5_elliptic).finite
    (∃ W : HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian b5_elliptic)
          (spec_bettiDeRhamIso_abelian b5_elliptic) (hodgeDecomposition_of_abelian b5_elliptic)
          (torusCohomology_cupProductOf b5_elliptic)).weight1 1,
      W.J = b63g_modelOperator _ _ b2_std_isWeightOne _ b2_std_isRiemannForm b63g_rot) ∧
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf b5_elliptic)
      (b63g_modelClass _ _ b2_std_isWeightOne _ b2_std_isRiemannForm))
      (b63g_modelOperator _ _ b2_std_isWeightOne _ b2_std_isRiemannForm b63g_rot) ∧
    Module.finrank ℤ (Fin 2 → ℤ) = 2 * dim b5_elliptic.left :=
  letI := b5_groupObj _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
  letI : IsIntegral b5_elliptic.left := b5_integral_aux _ _ b2_std_isWeightOne _
    b2_std_isRiemannForm
  letI := b5_smooth_aux _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
  letI := b5_projective_aux _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
  letI := (torusCohomology_cupProductOf b5_elliptic).finite
  ⟨⟨⟨b63g_modelOperator _ _ b2_std_isWeightOne _ b2_std_isRiemannForm b63g_rot,
      (b63g_dualOperator_sq _ 1 _ (b63g_modelMap_sq _ _ b2_std_isWeightOne _
        b2_std_isRiemannForm 1 b63g_rot b63g_rot_sq)).trans (by norm_num),
      b63g_dualOperator_hodge _ _ (b63g_modelMap_filtration _ _ b2_std_isWeightOne _
        b2_std_isRiemannForm b63g_rot b63g_rot_stdF)⟩, rfl⟩,
    b63g_dualOperator_rosati _ _ _ (b63g_modelForm_skew _ _ b2_std_isWeightOne _
      b2_std_isRiemannForm b63g_rot b63g_rot_skew),
    b63g_model_finrank _ _ b2_std_isWeightOne _ b2_std_isRiemannForm⟩

/-- Rejected case: `b2_skewIdem` is not skew for the standard form, so the skewness
hypotheses are not automatic. -/
example : ¬ ∀ l m, b2_stdForm (b2_skewIdem l) m = -b2_stdForm l (b2_skewIdem m) := by
  intro h
  have := h (Pi.single 0 1) (Pi.single 1 1)
  simp [b2_stdForm, b2_skewIdem, Matrix.toLinearMap₂'_apply', Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] at this

/-! ## Chain checks toward the fields of `g32t_Sixfold` and `g32h_PrymFamily` -/

/-- **The field `W`.** With `n = 3`, the model operator is a `HodgeBlocks.WeilAction` of
`ℚ(√-3)` on `H¹` of the model, of exactly the type of the field `W` of `g32t_Sixfold`. -/
example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hsq : ∀ l, φ (φ l) = (-3 : ℤ) • l) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
    ∃ W : HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian (b5_model Λ F hF Q))
          (spec_bettiDeRhamIso_abelian (b5_model Λ F hF Q))
          (hodgeDecomposition_of_abelian (b5_model Λ F hF Q))
          (torusCohomology_cupProductOf (b5_model Λ F hF Q))).weight1 3,
      W.J = b63g_modelOperator Λ F hF Q hQ φ :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
  ⟨⟨b63g_modelOperator Λ F hF Q hQ φ,
    (b63g_dualOperator_sq _ 3 _ (b63g_modelMap_sq Λ F hF Q hQ 3 φ hsq)).trans (by norm_num),
    b63g_dualOperator_hodge _ _ (b63g_modelMap_filtration Λ F hF Q hQ φ hφ)⟩, rfl⟩

/-- **A bundled sixfold.** The B5 model with its five instances, the Weil action of the model
operator and the degree-two class `b63g_modelClass` form a `g32t_Sixfold`. -/
example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hsq : ∀ l, φ (φ l) = (-3 : ℤ) • l) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    g32t_Sixfold :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  letI : IsCommMonObj (b5_model Λ F hF Q) := b5_commutative_aux Λ F hF Q hQ
  letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
  { X := b5_model Λ F hF Q
    W := ⟨b63g_modelOperator Λ F hF Q hQ φ,
      (b63g_dualOperator_sq _ 3 _ (b63g_modelMap_sq Λ F hF Q hQ 3 φ hsq)).trans (by norm_num),
      b63g_dualOperator_hodge _ _ (b63g_modelMap_filtration Λ F hF Q hQ φ hφ)⟩
    pol := b63g_modelClass Λ F hF Q hQ }

/-- **The field `nondegenerate`** on the model's class: `b2_abelian_nondegenerate` applied to the
carried Riemann form. -/
example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    Symplectic.IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (b5_model Λ F hF Q))
      (b63g_modelClass Λ F hF Q hQ)) :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  b2_abelian_nondegenerate _ _ (b63g_modelForm_riemann Λ F hF Q hQ)

/-- **The field `rosati`** on the model: the model operator is Rosati-skew for the model's
class. -/
example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hskew : ∀ l m, Q (φ l) m = -Q l (φ m)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (b5_model Λ F hF Q))
      (b63g_modelClass Λ F hF Q hQ)) (b63g_modelOperator Λ F hF Q hQ φ) :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  b63g_dualOperator_rosati _ _ _ (b63g_modelForm_skew Λ F hF Q hQ φ hskew)

/-- **The field `dim_eq`.** On a lattice of rank twelve (as `b63d_lattice_rank` supplies), the
model has dimension six, which is the Chevalley–Weil multiplicity of every Nielsen tuple. -/
example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q)
    (B : Module.Basis (Fin 12) ℤ Λ) (g : Fin 13 → Matrix (Fin 4) (Fin 4) ℂ)
    (hg : g32h_Nielsen g) :
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    (dim (b5_model Λ F hF Q).left : ℤ) = g32h_multCW g := by
  have h := b63g_model_finrank Λ F hF Q hQ
  rw [Module.finrank_eq_card_basis B, Fintype.card_fin] at h
  rw [g32h_multCW_of_nielsen g hg]
  omega

/-- **The actual moving fibres.** For the saturated lattice at `s` with a basis of rank twelve
(as `b63d_lattice_rank` supplies), the filtration transported from `t` and the original form,
the certificates of `b63e_weight_one_riemann` give the B5 model; it has dimension six and its
degree-two class is nondegenerate, the fields `dim_eq` and `nondegenerate` at this fibre. -/
example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hs : Function.Surjective f)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice b C hC V hV s)) :
    letI : Module.Free ℤ (b63l_parameterLattice b C hC V hV s) := Module.Free.of_basis B
    letI : Module.Finite ℤ (b63l_parameterLattice b C hC V hV s) := Module.Finite.of_basis B
    letI := b5_groupObj _ _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ
      P hP s t).1 _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t).2
    letI : IsIntegral (b5_model _ _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀
        hQ₀ Q hQ P hP s t).1 (b63e_singularQ b C hC V hV s (P s) (Q s))).left :=
      b5_integral_aux _ _ _ _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q
        hQ P hP s t).2
    letI := b5_smooth_aux _ _ _ _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀
      Q hQ P hP s t).2
    letI := b5_projective_aux _ _ _ _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀
      hQ₀ Q hQ P hP s t).2
    dim (b5_model _ _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP
        s t).1 (b63e_singularQ b C hC V hV s (P s) (Q s))).left = 6 ∧
      Symplectic.IsNondegenerate (polarizationVec (torusCohomology_cupProductOf _)
        (b63g_modelClass _ _ _ _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀
          Q hQ P hP s t).2)) :=
  letI : Module.Free ℤ (b63l_parameterLattice b C hC V hV s) := Module.Free.of_basis B
  letI : Module.Finite ℤ (b63l_parameterLattice b C hC V hV s) := Module.Finite.of_basis B
  have W := b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t
  letI := b5_groupObj _ _ W.1 _ W.2
  letI : IsIntegral (b5_model _ _ W.1 (b63e_singularQ b C hC V hV s (P s) (Q s))).left :=
    b5_integral_aux _ _ _ _ W.2
  letI := b5_smooth_aux _ _ _ _ W.2
  letI := b5_projective_aux _ _ _ _ W.2
  ⟨by
    have h := b63g_model_finrank _ _ W.1 _ W.2
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin] at h
    omega,
    b2_abelian_nondegenerate _ _ (b63g_modelForm_riemann _ _ W.1 _ W.2)⟩

end HodgeLean.Foundations.Program
