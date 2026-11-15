import HodgeLean.Adapters.LefschetzOneOneHodgeAbelian3
import HodgeLean.Adapters.AutomorphyLineBundleOnX
import HodgeLean.Foundations.AnalyticDivisorAlgebraic15

/-! # Divisors on the abelian universal cover

Global effective analytic divisors are represented by local equations on the universal cover,
with association under lattice translations. Algebraization records reduced component equations
and their positive integral multiplicities, without cohomology.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open Filter Set Topology
namespace HodgeLean.Adapters

/-- Appell--Humbert input on the fixed period lattice, with no positivity condition.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, second edition, Theorem 2.2.3. -/
structure bh4_AHData (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] where
  H : HermitianForm (V := Fin (dim X.left) → ℂ)
  E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ
  integral : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m
  chi : abelianPeriodLattice X → Circle
  semicharacter : ∀ l m : abelianPeriodLattice X,
    chi (l + m) = chi l * chi m * Circle.exp (Real.pi * H.imaginary l m)

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

example (D : bh4_AHData X) : HermitianForm (V := Fin (dim X.left) → ℂ) := D.H

/-- Local equations of an effective divisor, with descent expressed by association under every
period translation. These are equations on the cover, not a new manifold divisor type.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Chapter 1, section 1. -/
structure bh4_LocalDivisorData where
  ι : Type
  V : ι → Set (Fin (dim X.left) → ℂ)
  f : ι → (Fin (dim X.left) → ℂ) → ℂ
  valid : IsLocalDivisorData univ V f
  periodic : ∀ (l : abelianPeriodLattice X) i j p,
    p ∈ V i → p + l ∈ V j → AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p

example (D : bh4_LocalDivisorData X) : IsLocalDivisorData univ D.V D.f := D.valid

/-- Complex points lying in the Zariski closure of a scheme point.
Source: Serre, *Géométrie algébrique et géométrie analytique*, section 2. -/
def bh4_componentSupport (x : X.left) : Set (ComplexPoint X) :=
  {z | z.underlying ∈ closure ({x} : Set X.left)}

example (x : X.left) (z : ComplexPoint X) :
    z ∈ bh4_componentSupport X x ↔ z.underlying ∈ closure ({x} : Set X.left) := Iff.rfl

/-- Algebraic realization of effective local divisor equations. Reduced local equations of each
component have squarefree analytic germs. Association to their powered product records every
branch multiplicity, including at singular and intersection points.
Source: Serre, *Géométrie algébrique et géométrie analytique*, Théorème 3;
Griffiths--Harris, Chapter 1, section 1 (divisors). -/
structure bh4_Algebraization (D : bh4_LocalDivisorData X) where
  n : ℕ
  x : Fin n → X.left
  distinct : Function.Injective x
  codim : ∀ i, Order.coheight (x i) = 1
  mult : Fin n → ℕ
  positive : ∀ i, 0 < mult i
  support : abelianExp X '' localDivisorSupport D.V D.f =
    ⋃ i, bh4_componentSupport X (x i)
  local_equations : ∀ j p, p ∈ D.V j →
    ∃ (g : Fin n → (Fin (dim X.left) → ℂ) → ℂ)
      (hg : ∀ i, AnalyticAt ℂ (g i) p),
      (∀ i, Squarefree (⟨Filter.Germ.ofFun (g i), g i, hg i, rfl⟩ :
        AnalyticGermAt (dim X.left) p)) ∧
      (∀ i, ∀ᶠ z in 𝓝 p, g i z = 0 ↔ abelianExp X z ∈ bh4_componentSupport X (x i)) ∧
      AreAssociatedAt (D.f j) (fun z ↦ ∏ i, g i z ^ mult i) p

example (D : bh4_LocalDivisorData X) (A : bh4_Algebraization X D) (i : Fin A.n) :
    0 < A.mult i := A.positive i

/-- The GAGA target: every valid, lattice-invariant effective divisor algebraizes, with its local
multiplicities. This binder contains no Chern class or cycle-class span.
Source: Serre, *Géométrie algébrique et géométrie analytique*, Théorème 3 (coherent ideals). -/
def bh4_LocalDivisorDataAlgebraizes : Prop :=
  ∀ D : bh4_LocalDivisorData X, Nonempty (bh4_Algebraization X D)

-- Expanding the binder exposes only equations, supports and multiplicities; no cohomology
-- predicate occurs. This is a structural check, not a claim of logical independence.
example (h : bh4_LocalDivisorDataAlgebraizes X) (D : bh4_LocalDivisorData X) :
    Nonempty (bh4_Algebraization X D) := h D

/-- Evaluation of a degree-two rational class on an ordered pair of periods. The class is
carried to the exterior square of the rational lattice dual, contracted against the first
period and evaluated on the second. This is a linear map, independent of divisor data.
Source: Birkenhake--Lange, second edition, section 1.3; `latticeClassHQ`;
`Symplectic.contract`. -/
def bh4_periodPair (l m : abelianPeriodLattice X) : HQ X 2 →ₗ[ℚ] ℚ :=
  let ev : Module.Dual ℚ (abelianPeriodLattice X →+ ℚ) :=
    { toFun := fun f ↦ f l
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  { toFun := fun c ↦ Symplectic.contract
      (exteriorPower.map 2 (abelianPeriodEquiv X).toLinearMap
        (((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm c)) ev m
    map_add' := by
      intro c d
      simp only [map_add, LinearMap.add_apply, AddMonoidHom.add_apply]
    map_smul' := by
      intro r c
      simp only [map_smul, LinearMap.smul_apply, AddMonoidHom.smul_apply, smul_eq_mul,
        RingHom.id_apply] }

example (l m : abelianPeriodLattice X) : bh4_periodPair X l m 0 = 0 := map_zero _

/-- The four oriented edges of the translated period parallelogram, traversed in the order
`l`, `m`, `-l`, `-m`. Only parameters in `[0,1]` are used in boundary comparisons.
Source: Birkenhake--Lange, second edition, section 2.1 (the fundamental parallelogram). -/
def bh4_squareEdge (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (i : Fin 4) (t : ℝ) : Fin (dim X.left) → ℂ :=
  ![z + t • (l : Fin (dim X.left) → ℂ),
    z + l + t • (m : Fin (dim X.left) → ℂ),
    z + (1 - t) • (l : Fin (dim X.left) → ℂ) + m,
    z + (1 - t) • (m : Fin (dim X.left) → ℂ)] i

example (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ) :
    bh4_squareEdge X l m z 0 0 = z := by simp [bh4_squareEdge]

/-- Sum of endpoint increments of four logarithm lifts, normalized by the exponential
`exp (2 pi i g)`. For compatible nonvanishing boundary data this is their winding number.
Source: Hatcher, *Algebraic Topology*, section 1.3 (lifting loops to the universal cover of a circle). -/
def bh4_boundaryIncrement (g : Fin 4 → ℝ → ℂ) : ℂ := ∑ i, (g i 1 - g i 0)

example : bh4_boundaryIncrement (fun _ _ ↦ 0) = 0 := by simp [bh4_boundaryIncrement]

/-- Logarithmic-derivative integral of the pullback of a function to the four oriented
edges. For an entire function nonzero on the boundary, this is its winding number.
Source: Ahlfors, *Complex Analysis*, third edition, Chapter 4, section 5 (argument principle). -/
def bh4_boundaryWinding (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (f : (Fin (dim X.left) → ℂ) → ℂ) : ℂ :=
  ∑ i : Fin 4, ∫ t in (0 : ℝ)..1,
    deriv (fun s : ℝ ↦ f (bh4_squareEdge X l m z i s)) t /
      (2 * Real.pi * Complex.I * f (bh4_squareEdge X l m z i t))

example (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ) :
    bh4_boundaryWinding X l m z (fun _ ↦ 1) = 0 := by
  simp [bh4_boundaryWinding]

end HodgeLean.Adapters
