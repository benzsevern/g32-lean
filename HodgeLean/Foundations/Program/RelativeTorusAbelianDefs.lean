import HodgeLean.Foundations.Program.RelativeTorusKernel
import HodgeLean.Adapters.LatticeClassHQDefs
import HodgeLean.Adapters.HodgeHigherDegreeAbelianDefs
import HodgeLean.Adapters.AbelianEndomorphismsDefs
import HodgeLean.RealDefs.F1569

/-!
# Track B2, comparison with the complex points of an abelian variety: definitions

For a complex abelian variety `X` (a group object of `Over (Spec ℂ)`, integral, smooth and
projective), `g = dim X.left`, the lattice of track B2 is the S12 period lattice
`Λ_X = abelianPeriodLattice X ⊂ ℂ^g` (the kernel of the exponential, `H₁(X(ℂ), ℤ)`). Constructed
here:
* the evaluation `ℂ ⊗[ℤ] Λ_X → ℂ^g`, `c ⊗ λ ↦ c λ`, and its kernel `b2_abelianF X`, the period
  filtration;
* the period pairing of `ℂ ⊗[ℤ] Λ_X` with `ℂ ⊗[ℚ] H¹(X(ℂ); ℚ)`, through `abelianPeriodEquiv`, and
  the Hodge filtration `b2_abelianHodgeF X`, the annihilator of the piece `H^{1,0}` of
  `abelianWeightOneHodgeStructure X`;
* the group homomorphism `b2_abelianToPoint X : b2_torus Λ_X (b2_abelianF X) → X(ℂ)`,
  `[[v]] ↦ exp (eval v)`;
* the integral form `Λ_X →+ Λ_X →+ ℤ` of a bilinear form, the input of `latticeClassHQ`.

With `F = H^{1,0}`-annihilator on `H₁` (not `F¹` on `H¹`) the torus of track B2 is `X(ℂ)` itself;
on `H¹` with `F¹` it would be the dual torus. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

/-- The integral form `Λ →+ Λ →+ ℤ` of a `ℤ`-bilinear form, the input of `latticeClassHQ`.
Source: Mathlib `LinearMap.toAddMonoidHom`. -/
def b2_bilinToAddHom {Λ : Type*} [AddCommGroup Λ] (Q : LinearMap.BilinForm ℤ Λ) :
    Λ →+ Λ →+ ℤ :=
  AddMonoidHom.mk' (fun x ↦ (Q x).toAddMonoidHom) (fun x y ↦ by ext; simp)

example {Λ : Type*} [AddCommGroup Λ] (Q : LinearMap.BilinForm ℤ Λ) (x y : Λ) :
    b2_bilinToAddHom Q x y = Q x y := rfl

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- **The lattice of `X`**: the S12 period lattice `Λ_X ⊂ ℂ^g`, `H₁(X(ℂ), ℤ)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; `abelianPeriodLattice`. -/
abbrev b2_abelianLattice : Type :=
  abelianPeriodLattice X

example : Module.Free ℤ (b2_abelianLattice X) := inferInstance

/-- **The evaluation** `ℂ ⊗[ℤ] Λ_X → ℂ^g`, `c ⊗ λ ↦ c λ`.
Source: Birkenhake–Lange, §1.1 (`Λ ⊗ ℝ = ℂ^g`); Mathlib `LinearMap.liftBaseChange`. -/
def b2_abelianEval : ℂ ⊗[ℤ] b2_abelianLattice X →ₗ[ℂ] (Fin (dim X.left) → ℂ) :=
  LinearMap.liftBaseChange ℂ (abelianPeriodLattice X).subtype

example (c : ℂ) (l : b2_abelianLattice X) :
    b2_abelianEval X (c ⊗ₜ l) = c • (l : Fin (dim X.left) → ℂ) := by
  simp [b2_abelianEval]

/-- **The period filtration** of `ℂ ⊗[ℤ] Λ_X`: the kernel of the evaluation, so that
`(ℂ ⊗ Λ_X) ⧸ F = ℂ^g` and the torus of track B2 is `ℂ^g ⧸ Λ_X`.
Source: Birkenhake–Lange, §1.1 and §2.4. -/
def b2_abelianF : Submodule ℂ (ℂ ⊗[ℤ] b2_abelianLattice X) :=
  LinearMap.ker (b2_abelianEval X)

example : b2_abelianF X = LinearMap.ker (b2_abelianEval X) := rfl

/-- The period of a class of `H¹(X(ℂ); ℚ)`, extended `ℂ`-linearly to `ℂ ⊗[ℤ] Λ_X`.
Source: Birkenhake–Lange, §1.1 (`H¹(X, ℤ) = Hom(Λ, ℤ)`); `abelianPeriodEquiv`. -/
def b2_abelianPeriodDual : HQ X 1 →ₗ[ℚ] Module.Dual ℂ (ℂ ⊗[ℤ] b2_abelianLattice X) where
  toFun x := LinearMap.liftBaseChange ℂ
    (((algebraMap ℚ ℂ).toAddMonoidHom.comp (abelianPeriodEquiv X x)).toIntLinearMap)
  map_add' x y := by
    ext l
    simp
  map_smul' c x := by
    ext l
    simp [Algebra.smul_def]

/-- **The period pairing** `ℂ ⊗[ℚ] H¹(X(ℂ); ℚ) → (ℂ ⊗[ℤ] Λ_X)^∨`, `⟨c ⊗ x, d ⊗ λ⟩ = c d ∫_λ x`.
Source: Birkenhake–Lange, §1.1 and §1.4; Hatcher, *Algebraic Topology*, §3.1 (universal
coefficients). -/
def b2_abelianPairing : ℂ ⊗[ℚ] HQ X 1 →ₗ[ℂ] Module.Dual ℂ (ℂ ⊗[ℤ] b2_abelianLattice X) :=
  LinearMap.liftBaseChange ℂ (b2_abelianPeriodDual X)

example (c d : ℂ) (x : HQ X 1) (l : b2_abelianLattice X) :
    b2_abelianPairing X (c ⊗ₜ x) (d ⊗ₜ l) = c * (d * (abelianPeriodEquiv X x l : ℂ)) := by
  simp [b2_abelianPairing, b2_abelianPeriodDual]

/-- **The Hodge filtration on `H₁`**: the annihilator in `ℂ ⊗[ℤ] Λ_X` of the piece `H^{1,0}` of
`abelianWeightOneHodgeStructure X` under the period pairing.
Source: Birkenhake–Lange, Theorem 1.4.1 (`H^{1,0} = H⁰(Ω¹)`) and §1.1; Deligne, *Théorie de
Hodge II*, §4.4 (the torus of a weight-one structure). -/
def b2_abelianHodgeF : Submodule ℂ (ℂ ⊗[ℤ] b2_abelianLattice X) :=
  letI := (finiteBetti_abelian X).finite 1
  (((abelianWeightOneHodgeStructure X).H (1, 0)).map (b2_abelianPairing X)).dualCoannihilator

example (v : ℂ ⊗[ℤ] b2_abelianLattice X) (hv : v ∈ b2_abelianHodgeF X) :
    letI := (finiteBetti_abelian X).finite 1
    ∀ w ∈ (abelianWeightOneHodgeStructure X).H (1, 0), b2_abelianPairing X w v = 0 :=
  fun _ hw ↦ (Submodule.mem_dualCoannihilator _).1 hv _ (Submodule.mem_map_of_mem hw)

/-- **The map to the complex points** `b2_torus Λ_X (b2_abelianF X) → X(ℂ)`, `[[v]] ↦ exp (eval v)`,
a group homomorphism.
Source: Birkenhake–Lange, §1.1; S12 `complexExponentialHom`. -/
def b2_abelianToPoint :
    b2_torus (b2_abelianLattice X) (b2_abelianF X) →+ Additive (ComplexPoint X) :=
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  QuotientAddGroup.lift _
    ((complexExponentialHom X (dim X.left)).comp
      ((b2_abelianF X).liftQ (b2_abelianEval X) le_rfl).toAddMonoidHom) (by
    rintro _ ⟨l, rfl⟩
    change complexExponential X (dim X.left) (b2_abelianEval X ((1 : ℂ) ⊗ₜ l)) = 0
    have hl := l.2
    simp only [b2_abelianEval, LinearMap.liftBaseChange_tmul, one_smul, Submodule.subtype_apply]
    exact hl)

example (v : ℂ ⊗[ℤ] b2_abelianLattice X) :
    b2_abelianToPoint X (QuotientAddGroup.mk (Submodule.Quotient.mk v)) =
      complexExponential X (dim X.left) (b2_abelianEval X v) := rfl

end HodgeLean.Foundations.Program
