import HodgeLean.Adapters.TorusCohomology
import HodgeLean.Adapters.DegreeOneSplitDefs
import HodgeLean.Blocks.HodgeStructure.Basic

/-! # Degree-one periods of tori (FROZEN)

The period of a degree-one rational singular class along a loop: pull the class back to the
circle and read off its coefficient on the oriented S4 generator `circleClass`. Applied to the
straight loops `t ↦ t • λ` of the coordinate torus and of the S12 period lattice, this gives the
period map from degree-one cohomology to functions on the lattice. All definitions are
constructions; no comparison is chosen by matching bases.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Singular

namespace HodgeLean.Adapters

/-- The basis of degree-one rational cohomology of the circle given by the oriented
Mayer–Vietoris generator `circleClass`.
Source: Hatcher, *Algebraic Topology*, §3.1 (the circle computation); S4 `circleClass_ne_zero`
and `span_circleClass_eq_top`. -/
def circleClassBasis : Module.Basis (Fin 1) ℚ (Cohomology ℚ (TopCat.of UnitAddCircle) 1) :=
  Module.Basis.mk (v := fun _ => circleClass)
    (linearIndependent_unique_iff.mpr circleClass_ne_zero)
    (by rw [Set.range_const, span_circleClass_eq_top])

example : circleClassBasis 0 = circleClass := by simp [circleClassBasis]

/-- The degree of a degree-one class on the circle: its coefficient on `circleClass`.
Source: Hatcher, *Algebraic Topology*, §2.2 (degree of a circle map) and §3.1. -/
def circleDegree : Cohomology ℚ (TopCat.of UnitAddCircle) 1 →ₗ[ℚ] ℚ :=
  circleClassBasis.coord 0

example : circleDegree circleClass = 1 := by
  have h : circleClass = circleClassBasis 0 := by simp [circleClassBasis]
  rw [circleDegree, h, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same]

/-- The period of a degree-one class along a loop `p`: the degree of its pullback to the circle,
i.e. the pairing of the class with the homology class of `p`.
Source: Hatcher, *Algebraic Topology*, §3.1 (universal coefficients, `H¹ = Hom(H₁, ℚ)`) and
§2.A (Hurewicz in degree one). -/
def loopPeriod {T : Type} [TopologicalSpace T] (p : C(UnitAddCircle, T)) :
    Cohomology ℚ (TopCat.of T) 1 →ₗ[ℚ] ℚ :=
  circleDegree ∘ₗ cohomologyMap ℚ 1 (TopCat.ofHom p)

example : loopPeriod (ContinuousMap.id UnitAddCircle) circleClass = 1 := by
  have h : circleClass = circleClassBasis 0 := by simp [circleClassBasis]
  change circleDegree (cohomologyMap ℚ 1 (𝟙 (TopCat.of UnitAddCircle)) circleClass) = 1
  rw [cohomologyMap_id, LinearMap.id_apply, circleDegree, h, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same]

/-- The straight loop `t ↦ t • λ` of the coordinate torus `ℝⁿ/ℤⁿ` through the lattice vector `λ`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`H₁(ℝⁿ/Λ, ℤ) = Λ`). -/
def torusLoop {n : ℕ} (l : Fin n → ℤ) : C(UnitAddCircle, UnitAddTorus (Fin n)) :=
  ⟨fun z i => l i • z, continuous_pi fun i => continuous_zsmul (l i)⟩

example {n : ℕ} (l : Fin n → ℤ) (z : UnitAddCircle) (i : Fin n) :
    torusLoop l z i = l i • z := rfl

/-- The period map of the coordinate torus: a degree-one class to its periods along the
straight loops of the integer lattice `ℤⁿ`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; Hatcher, *Algebraic
Topology*, §3.1. -/
def torusPeriod (n : ℕ) :
    Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1 →ₗ[ℚ] ((Fin n → ℤ) → ℚ) :=
  LinearMap.pi fun l => loopPeriod (torusLoop l)

example (n : ℕ) (x : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1) (l : Fin n → ℤ) :
    torusPeriod n x l = loopPeriod (torusLoop l) x := rfl

/-- The continuous group homomorphism of coordinate tori induced by an integer matrix.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (analytic and rational
representations of homomorphisms). -/
def torusMatrixMap {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) :
    C(UnitAddTorus (Fin n), UnitAddTorus (Fin m)) :=
  ⟨fun t i => ∑ j, M i j • t j,
    continuous_pi fun i => continuous_finsetSum _ fun j _ =>
      (continuous_zsmul (M i j)).comp (continuous_apply j)⟩

example {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) (t : UnitAddTorus (Fin n)) (i : Fin m) :
    torusMatrixMap M t i = ∑ j, M i j • t j := rfl

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- The S12 period lattice `Λ ⊂ ℂ^g` of `X`, `g = dim X.left`, with the commutativity that S12
derives from properness and integrality (as in `complexPointUniformization`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; S12
`complexExponentialLattice`. -/
abbrev abelianPeriodLattice : Submodule ℤ (Fin (dim X.left) → ℂ) :=
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  complexExponentialLattice X (dim X.left)

example (v : Fin (dim X.left) → ℂ) :
    v ∈ abelianPeriodLattice X ↔ complexExponential X (dim X.left) v = 0 := Iff.rfl

/-- The S12 integer basis of the period lattice, the one `complexPointUniformization` uses.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; S12
`complexExponentialLatticeBasis`. -/
abbrev abelianLatticeBasis : Module.Basis (Fin (2 * dim X.left)) ℤ (abelianPeriodLattice X) :=
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  complexExponentialLatticeBasis X (dim X.left)

example (l : abelianPeriodLattice X) :
    ∑ i, (abelianLatticeBasis X).repr l i • abelianLatticeBasis X i = l :=
  (abelianLatticeBasis X).sum_repr l

-- The S12 uniformization is built from exactly this basis.
example : complexPointUniformization X (dim X.left) =
    (letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
      (complexSelfProductIntegral_of_isIntegral X)
    letI := isZLattice_complexExponentialLattice X (dim X.left)
    (complexExponentialQuotientEquiv X (dim X.left)).symm.trans
      (LatticeTorus.quotientEquivOfBasis (abelianPeriodLattice X) (abelianLatticeBasis X))) := rfl

/-- The loop `t ↦ exp(t • λ)` of `X(ℂ)` through a period `λ`: S11's one-parameter subgroup of
`λ`, which factors through `ℝ/ℤ` because `exp λ = 1`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; Mumford, *Abelian
Varieties*, §1. -/
def abelianLatticeLoop (l : abelianPeriodLattice X) : C(UnitAddCircle, ComplexPoint X) :=
  let φ := oneParameterSubgroup X (dim X.left) (l : Fin (dim X.left) → ℂ)
  have hφ : AddSubgroup.zmultiples (1 : ℝ) ≤ φ.ker :=
    (AddSubgroup.zmultiples_le_of_mem (by exact l.2))
  ⟨fun z => Additive.toMul (QuotientAddGroup.lift _ φ hφ z),
    continuous_toMul.comp (QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
      (continuous_oneParameterSubgroup X (dim X.left) (l : Fin (dim X.left) → ℂ)))⟩

example (l : abelianPeriodLattice X) (t : ℝ) :
    abelianLatticeLoop X l (t : UnitAddCircle) =
      Additive.toMul (oneParameterSubgroup X (dim X.left) (l : Fin (dim X.left) → ℂ) t) := rfl

/-- The period map of `X`: a rational degree-one class, through the S7 comparison
`cupComparison` with singular cohomology of `X(ℂ)`, to its periods along the S12 loops.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; S7 `cupComparison`. -/
def abelianPeriod : HQ X 1 →ₗ[ℚ] (abelianPeriodLattice X → ℚ) :=
  LinearMap.pi fun l => loopPeriod (abelianLatticeLoop X l) ∘ₗ (cupComparison X 1).toLinearMap

example (x : HQ X 1) (l : abelianPeriodLattice X) :
    abelianPeriod X x l = loopPeriod (abelianLatticeLoop X l) (cupComparison X 1 x) := rfl

/-- Restriction of a complex-valued real functional on `ℂ^g` to the period lattice.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and Theorem 1.4.1. -/
def latticeRestriction :
    DegreeOneLatticeDual (dim X.left) →ₗ[ℂ] (abelianPeriodLattice X → ℂ) where
  toFun f l := f l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

example (f : DegreeOneLatticeDual (dim X.left)) (l : abelianPeriodLattice X) :
    latticeRestriction X f l = f l := rfl

/-- The complexified period map `ℂ ⊗[ℚ] HQ X 1 → (Λ → ℂ)`, `c ⊗ x ↦ (λ ↦ c · period x λ)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and §1.4. -/
def complexAbelianPeriod : ℂ ⊗[ℚ] HQ X 1 →ₗ[ℂ] (abelianPeriodLattice X → ℂ) :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ _
      (LinearMap.compLeft (Algebra.linearMap ℚ ℂ) (abelianPeriodLattice X) ∘ₗ abelianPeriod X))

example (c : ℂ) (x : HQ X 1) (l : abelianPeriodLattice X) :
    complexAbelianPeriod X (c ⊗ₜ x) l = c * (abelianPeriod X x l : ℂ) := by
  simp [complexAbelianPeriod]

/-- The holomorphic summand of `ℂ ⊗[ℚ] HQ X 1`: classes whose periods are those of a
complex-linear functional on `ℂ^g`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1. -/
def complexHolomorphicH1 : Submodule ℂ (ℂ ⊗[ℚ] HQ X 1) :=
  ((degreeOneLatticeHolomorphic (dim X.left)).map (latticeRestriction X)).comap
    (complexAbelianPeriod X)

example (ω : ℂ ⊗[ℚ] HQ X 1) : ω ∈ complexHolomorphicH1 X ↔
    ∃ f ∈ degreeOneLatticeHolomorphic (dim X.left),
      latticeRestriction X f = complexAbelianPeriod X ω := Iff.rfl

/-- The antiholomorphic summand of `ℂ ⊗[ℚ] HQ X 1`: classes whose periods are those of a
conjugate-linear functional on `ℂ^g`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1. -/
def complexAntiholomorphicH1 : Submodule ℂ (ℂ ⊗[ℚ] HQ X 1) :=
  ((degreeOneLatticeAntiholomorphic (dim X.left)).map (latticeRestriction X)).comap
    (complexAbelianPeriod X)

example (ω : ℂ ⊗[ℚ] HQ X 1) : ω ∈ complexAntiholomorphicH1 X ↔
    ∃ f ∈ degreeOneLatticeAntiholomorphic (dim X.left),
      latticeRestriction X f = complexAbelianPeriod X ω := Iff.rfl

end HodgeLean.Adapters
