import HodgeLean.Foundations.Program.RelativeTorusAbelianProofs
import HodgeLean.Adapters.LatticeClassHQ

/-! # Track B2, comparison with the complex points of an abelian variety (FROZEN SPEC)

Each theorem is the matching `_aux` theorem of `RelativeTorusAbelianProofs.lean`. For a complex
abelian variety `X` (`GrpObj`, integral, smooth, projective), `g = dim X.left`, the objects are
constructed in `RelativeTorusAbelianDefs.lean`: the lattice `Λ_X = abelianPeriodLattice X`, the
evaluation `ℂ ⊗[ℤ] Λ_X → ℂ^g` and its kernel `b2_abelianF X`, the Hodge filtration
`b2_abelianHodgeF X` (the annihilator of `H^{1,0}` of `abelianWeightOneHodgeStructure X` under the
period pairing), and the homomorphism `b2_abelianToPoint X : b2_torus Λ_X (b2_abelianF X) → X(ℂ)`.

**Claimed.** The Hodge filtration from `abelianWeightOneHodgeStructure X` is the period
filtration, and it is a weight-one Hodge structure on `Λ_X`; `dim_ℂ ((ℂ ⊗ Λ_X) ⧸ F) = dim X`;
`b2_abelianToPoint X` is a bijective group homomorphism, holomorphic with holomorphic inverse
for the charted spaces `b2_torus_chartedSpace` and the algebraic charts of `ComplexPoint X`. A form
`Q` on `Λ_X` is a Riemann form for this filtration if and only if `Q = Im H` on `Λ_X` for a
positive definite Hermitian form `H` on `ℂ^g` (the repository's `HermitianForm` convention,
conjugate-linear in the first variable); then the 2-vector of `latticeClassHQ X Q` is
nondegenerate. For an endomorphism `f` of `X` with lattice map `φ`, `φ_ℂ` preserves the filtration
and the induced endomorphism of the torus is `f(ℂ)`; so the sub-torus of an idempotent is the
image of `f(ℂ)`.

**Not claimed.** That `latticeClassHQ X Q` is the class of a line bundle or is algebraic; the
positivity condition `PolarizationPositive` of `RealDefs.F1569` for it (its `HodgeBlocks`
sign convention on the dual form of `H¹` is not compared here; see
`docs/specs/RelativeTorusKernel.md`); any statement about curves, Jacobians, Pryms, Hurwitz
spaces or the Weil action. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Manifold
open scoped TensorProduct ContDiff CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open HodgeLean.Foundations.AppellHumbert

namespace HodgeLean.Foundations.Program

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- **The Hodge filtration is the period filtration.** The annihilator in `ℂ ⊗[ℤ] Λ_X` of
`H^{1,0}` (the piece `(1, 0)` of `abelianWeightOneHodgeStructure X`) under the period pairing is
the kernel of the evaluation `ℂ ⊗ Λ_X → ℂ^g`: holomorphic `1`-forms pair with `λ ∈ Λ_X` by their
values on `λ ∈ ℂ^g`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1 and §1.1;
`spec_g4_cohomologyHodgePiece_one_eq` (`H^{1,0}` is the lattice-side holomorphic piece). -/
theorem b2_abelianHodgeF_eq : b2_abelianHodgeF X = b2_abelianF X :=
  b2_abelianHodgeF_eq_aux X

example (v : ℂ ⊗[ℤ] b2_abelianLattice X) (hv : b2_abelianEval X v = 0) :
    v ∈ b2_abelianHodgeF X := by
  rw [b2_abelianHodgeF_eq]
  exact hv

/-- **The period filtration is a weight-one Hodge structure** on `Λ_X`: `ℂ ⊗ Λ_X = F ⊕ F̄`.
Source: Birkenhake–Lange, §1.1 and Proposition 1.1.3 (`Λ ⊗ ℝ = ℂ^g`). -/
theorem b2_abelianF_isWeightOne : b2_IsWeightOne (b2_abelianLattice X) (b2_abelianF X) :=
  b2_abelianF_isWeightOne_aux X

example : b2_IsWeightOne (b2_abelianLattice X) (b2_abelianHodgeF X) :=
  (b2_abelianHodgeF_eq X).symm ▸ b2_abelianF_isWeightOne X

/-- **Dimension.** `dim_ℂ ((ℂ ⊗ Λ_X) ⧸ F) = dim X`: the evaluation induces `(ℂ ⊗ Λ_X) ⧸ F ≅ ℂ^g`.
Source: Birkenhake–Lange, §1.1. -/
theorem b2_abelian_finrank :
    Module.finrank ℂ ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X) = dim X.left :=
  b2_abelian_finrank_aux X

example : Module.finrank ℤ (b2_abelianLattice X) = 2 * dim X.left := by
  rw [← b2_two_mul_finrank (b2_abelianF X) (b2_abelianF_isWeightOne X), b2_abelian_finrank]

/-- **The torus of the data is `X(ℂ)`**: `[[v]] ↦ exp (eval v)` is a bijective group homomorphism
`b2_torus Λ_X (b2_abelianF X) → X(ℂ)`.
Source: Birkenhake–Lange, §1.1; S12 `complexExponentialQuotientEquiv`. -/
theorem b2_abelianToPoint_bijective : Function.Bijective (b2_abelianToPoint X) :=
  b2_abelianToPoint_bijective_aux X

example : b2_torus (b2_abelianLattice X) (b2_abelianF X) ≃+ Additive (ComplexPoint X) :=
  AddEquiv.ofBijective _ (b2_abelianToPoint_bijective X)

/-- **The comparison is holomorphic.** `b2_abelianToPoint X` is holomorphic from the charted space
`b2_torus_chartedSpace` (the lattice is discrete by `b2_latticeMap_discrete`) to the algebraic
charted space of `ComplexPoint X`.
Source: Birkenhake–Lange, §1.1; `UniformizationBiholomorphic`
(`spec_contMDiff_complexExponential`). -/
theorem b2_abelianToPoint_contMDiff :
    haveI := b2_latticeMap_discrete (b2_abelianF X) (b2_abelianF_isWeightOne X)
    ContMDiff
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X)) → ℂ)
      𝓘(ℂ, Fin (dim X.left) → ℂ) ω (fun t ↦ Additive.toMul (b2_abelianToPoint X t)) :=
  b2_abelianToPoint_contMDiff_aux X

/-- **The inverse comparison is holomorphic**, so `b2_abelianToPoint X` is a biholomorphic group
isomorphism.
Source: Birkenhake–Lange, §1.1; `UniformizationBiholomorphic`. -/
theorem b2_abelianToPoint_symm_contMDiff :
    haveI := b2_latticeMap_discrete (b2_abelianF X) (b2_abelianF_isWeightOne X)
    ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X)) → ℂ) ω
      (fun x : ComplexPoint X ↦
        (Equiv.ofBijective _ (b2_abelianToPoint_bijective X)).symm (Additive.ofMul x)) :=
  b2_abelianToPoint_symm_contMDiff_aux X

example : b2_torus (b2_abelianLattice X) (b2_abelianF X) ≃ₜ ComplexPoint X :=
  haveI := b2_latticeMap_discrete (b2_abelianF X) (b2_abelianF_isWeightOne X)
  { toEquiv := (Equiv.ofBijective _ (b2_abelianToPoint_bijective X)).trans Additive.toMul
    continuous_toFun := (b2_abelianToPoint_contMDiff X).continuous
    continuous_invFun := (b2_abelianToPoint_symm_contMDiff X).continuous }

/-- **Riemann forms on `Λ_X` are the imaginary parts of positive Hermitian forms.** A form `Q` on
`Λ_X` is a Riemann form for the period filtration if and only if `Q(λ, μ) = Im H(λ, μ)` on
`Λ_X ⊂ ℂ^g` for a positive definite Hermitian form `H` (conjugate-linear in the first variable,
as `AppellHumbert.HermitianForm`). In the standard example (`ℤ + iℤ ⊂ ℂ`, `Q(1, i) = 1`) this is
`H(z, w) = z̄ w`.
Source: Birkenhake–Lange, §2.1 (Hermitian and alternating forms, `E = Im H`) and §4.1–4.2; Griffiths,
Amer. J. Math. 90 (1968), §2. -/
theorem b2_abelian_isRiemannForm_iff (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X)) :
    b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q ↔
      ∃ H : HermitianForm (V := Fin (dim X.left) → ℂ), H.IsPositiveDefinite ∧
        ∀ l m : b2_abelianLattice X, (Q l m : ℝ) = H.imaginary l m :=
  b2_abelian_isRiemannForm_iff_aux X Q

-- A Riemann form gives Hard Lefschetz for its class in `HQ X 2`, through
-- `spec_latticeClassHQ_hardLefschetz`.
example (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    HardLefschetz X (cupProductOf X) (latticeClassHQ X (b2_bilinToAddHom Q)) :=
  let ⟨H, hH, hE⟩ := (b2_abelian_isRiemannForm_iff X Q).1 hQ
  spec_latticeClassHQ_hardLefschetz X H hH _ hE

/-- **Nondegeneracy.** For a Riemann form `Q` on `Λ_X`, the 2-vector
`polarizationVec (torusCohomology_cupProductOf X) (latticeClassHQ X Q)` is nondegenerate, the
form of the field `nondegenerate` of `g32h_PrymFamily`: it is `⋀²` of the inverse period
equivalence applied to `latticeClass Q`, and `Q` is nondegenerate (`b2_riemannForm_nondegenerate`).
Source: Birkenhake–Lange, Lemma 1.3.1 and §4.1; `latticeClassHQ`, `polarizationVec`. -/
theorem b2_abelian_nondegenerate (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    Symplectic.IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X)
      (latticeClassHQ X (b2_bilinToAddHom Q))) :=
  b2_abelian_nondegenerate_aux X Q hQ

example (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    Function.Injective (Symplectic.contract (polarizationVec (torusCohomology_cupProductOf X)
      (latticeClassHQ X (b2_bilinToAddHom Q)))) :=
  (b2_abelian_nondegenerate X Q hQ).1

/-- **Endomorphisms preserve the filtration.** For an endomorphism `f` of `X` and its lattice map
`φ` (characterised by the periods, `spec_abelianEndAction_period`), `φ_ℂ` preserves the period
filtration: `eval ∘ φ_ℂ = A_f ∘ eval` for the analytic representation `A_f`.
Source: Birkenhake–Lange, §1.2 (analytic and rational representations);
`spec_latticeRepresentation_eq_analytic`. -/
theorem b2_abelianEnd_preserves (f : AbelianEnd X)
    (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (hφ : ∀ x l, abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ l)) :
    b2_abelianF X ≤ (b2_abelianF X).comap (b2_cplxMap φ) :=
  b2_abelianEnd_preserves_aux X f φ hφ

/-- **The induced map of tori is `f(ℂ)`.** Through `b2_abelianToPoint X`, the endomorphism
`b2_torusHom` of the torus induced by the lattice map `φ` of `f` is the map `f(ℂ)` of complex
points. Hence the sub-torus `b2_subTorus` of `φ`, whose image is that of `b2_torusHom`
(`b2_subTorus_range`), is the image of `f(ℂ)`; for an idempotent `f` it is the abelian
subvariety `f(X)`.
Source: Birkenhake–Lange, §1.2, §5.3 and §12.2; `spec_abelianEnd_analyticRepresentation`. -/
theorem b2_abelianEnd_torusHom (f : AbelianEnd X)
    (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (hφ : ∀ x l, abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ l))
    (hφF : b2_abelianF X ≤ (b2_abelianF X).comap (b2_cplxMap φ))
    (t : b2_torus (b2_abelianLattice X) (b2_abelianF X)) :
    Additive.toMul (b2_abelianToPoint X (b2_torusHom _ _ φ hφF t)) =
      Point.map f.hom (Additive.toMul (b2_abelianToPoint X t)) :=
  b2_abelianEnd_torusHom_aux X f φ hφ hφF t

example (f : AbelianEnd X) (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (hφ : ∀ x l, abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ l))
    (y : b2_torus φ.range (b2_imageF (b2_abelianF X) φ)) :
    ∃ t, Additive.toMul (b2_abelianToPoint X (b2_subTorus (b2_abelianF X) φ y)) =
      Point.map f.hom (Additive.toMul (b2_abelianToPoint X t)) := by
  have hF := b2_abelianEnd_preserves X f φ hφ
  obtain ⟨t, ht⟩ : b2_subTorus (b2_abelianF X) φ y ∈ (b2_torusHom _ _ φ hF).range :=
    b2_subTorus_range _ φ hF ▸ ⟨y, rfl⟩
  exact ⟨t, ht ▸ b2_abelianEnd_torusHom X f φ hφ hF t⟩

end HodgeLean.Foundations.Program
