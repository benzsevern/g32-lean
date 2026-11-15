import HodgeLean.Adapters.HolomorphicPeriods
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.Quotient

/-! # Integrals of holomorphic `1`-forms along paths in `X(ℂ)`, by lifting along `exp`

For a global holomorphic `1`-form `θ` on `X`, the pullback `exp^*θ` along the S12 uniformization
`exp : ℂ^d → X(ℂ)` is, for abelian `X`, the constant covector `a = exp^*θ(0)` (stage 4f), so
`v ↦ a v` is a global primitive of `exp^*θ` on `ℂ^d`. The integral of `θ` along a continuous path
`γ` in `X(ℂ)` is then `a (Γ 1 - Γ 0)` for any continuous lift `Γ` of `γ` along `exp`: the value of
the primitive at the end of the lift minus its value at the start. This file defines the lifts,
the displacement `Γ 1 - Γ 0` of a chosen lift (`0` when no lift exists), and the integral.
Integrating through a primitive needs no differentiability of the path, unlike Mathlib's
`curveIntegral`, which reads the velocity of the path through `derivWithin`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.Foundations

namespace HodgeLean.Adapters

section Lift

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [SmoothOfRelativeDimension d X.hom]

/-- `Γ` is a lift of the path `γ` of `X(ℂ)` along the uniformization: `exp (Γ t) = γ t`.
Source: Hatcher, *Algebraic Topology*, §1.3 (lifts along a covering); S12 `complexExponential`. -/
def IsExpLift (γ : C(unitInterval, ComplexPoint X)) (Γ : C(unitInterval, Fin d → ℂ)) : Prop :=
  ∀ t, (complexExponential X d (Γ t)).toMul = γ t

example (γ : C(unitInterval, ComplexPoint X)) (Γ : C(unitInterval, Fin d → ℂ)) :
    IsExpLift X d γ Γ ↔ ∀ t, (complexExponential X d (Γ t)).toMul = γ t := Iff.rfl

/-- The displacement `Γ 1 - Γ 0` of a chosen lift `Γ` of `γ` along the uniformization, and `0`
when `γ` has no lift.
Source: Hatcher, *Algebraic Topology*, §1.3 (path lifting, the monodromy of a covering);
Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`π₁(ℂ^g/Λ) = Λ`). -/
def expLiftDisplacement (γ : C(unitInterval, ComplexPoint X)) : Fin d → ℂ :=
  open Classical in
  if h : ∃ Γ, IsExpLift X d γ Γ then h.choose 1 - h.choose 0 else 0

example (γ : C(unitInterval, ComplexPoint X)) (h : ¬ ∃ Γ, IsExpLift X d γ Γ) :
    expLiftDisplacement X d γ = 0 := by
  simp [expLiftDisplacement, h]

/-- The path `exp ∘ Γ` of `X(ℂ)` for a path `Γ` of `ℂ^d`, for commutative `X`.
Source: S12 `continuous_complexExponential`. -/
def expPath [IsCommMonObj X] (Γ : C(unitInterval, Fin d → ℂ)) : C(unitInterval, ComplexPoint X) :=
  ⟨fun t ↦ (complexExponential X d (Γ t)).toMul,
    continuous_toMul.comp ((continuous_complexExponential X d).comp Γ.continuous)⟩

example [IsCommMonObj X] (Γ : C(unitInterval, Fin d → ℂ)) : IsExpLift X d (expPath X d Γ) Γ := fun _ ↦ rfl

/-- The integral of a global holomorphic `1`-form `θ` along a path `γ` of `X(ℂ)`: the covector
`exp^*θ(0)` applied to the displacement of a lift of `γ`. For abelian `X` it is the difference of
the values of the primitive `v ↦ exp^*θ(0) v` of `exp^*θ` at the ends of the lift.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 10.12 and §10.38 (integrals of
closed forms along continuous paths through local primitives); Birkenhake–Lange, *Complex Abelian
Varieties*, 2nd ed., §1.1 and Lemma 1.3.1; stage 4f `spec_expPullback_eq_expPullback_zero`. -/
def holomorphicPathIntegral (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (γ : C(unitInterval, ComplexPoint X)) : ℂ :=
  expPullback X d θ 0 (expLiftDisplacement X d γ)

example (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (γ : C(unitInterval, ComplexPoint X)) :
    holomorphicPathIntegral X d θ γ = expPullback X d θ 0 (expLiftDisplacement X d γ) := rfl

end Lift

section Lattice

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The S12 loop through a period `λ`, as a path `[0, 1] → X(ℂ)`: `t ↦ exp (t • λ)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; `abelianLatticeLoop`
composed with the quotient map `[0, 1] → ℝ/ℤ`. -/
def abelianLatticePath (l : abelianPeriodLattice X) : C(unitInterval, ComplexPoint X) :=
  (abelianLatticeLoop X l).comp
    ⟨fun t ↦ ((t : ℝ) : UnitAddCircle), (AddCircle.continuous_mk' 1).comp continuous_subtype_val⟩

example (l : abelianPeriodLattice X) (t : unitInterval) :
    abelianLatticePath X l t = abelianLatticeLoop X l ((t : ℝ) : UnitAddCircle) := rfl

end Lattice

end HodgeLean.Adapters
