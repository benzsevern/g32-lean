import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelianDefs
import HodgeLean.Foundations.AutomorphyChernClassDefs
import HodgeLean.Adapters.LatticeClassHQDefs

/-! # Divisor classes on abelian varieties: the constructed objects (DC1)

The objects of the Appell–Humbert route from a prime divisor of an abelian variety `X` to its
class in `HQ X 2`, each a construction, none a stored field:

* `dc1_coverDivisor X x`: the prime divisor `closure {x}`, pulled back to the universal cover
  `ℂ^g` along the S12 exponential;
* `dc1_factor f L`: the factor of automorphy `l ↦ f (z + l) / f z` of an entire function `f`,
  extended over the zeros of `f` by its limit (the line bundle `𝒪(D)` when `f` is a reduced
  equation of `D` on the cover);
* `dc1_factorLog a`: a logarithm of a nowhere-vanishing factor, by integrating the logarithmic
  derivative along the segment from `0`;
* `dc1_chernBihom F`: the integral bilinear form with the values `-chernForm F` on a `ℤ`-basis;
* `dc1_chernClass X f`: the class in `HQ X 2` of that form, the first Chern class of the line
  bundle of the factor of `f`.

No hypothesis is built into any of them: holomorphy, nonvanishing and the cocycle identity are
explicit binders of the statements in `DivisorClassHodge.lean`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AutomorphyChernClass HodgeLean.Adapters
open Filter Set Topology

namespace HodgeLean.Foundations

section Cover

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

/-- The divisor `closure {x}` of a scheme point, pulled back to the universal cover `ℂ^g` of
`X(ℂ)` along the S12 exponential.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (the uniformization
`ℂ^g → X(ℂ)`); `bh4_componentSupport`, `abelianExp`. -/
def dc1_coverDivisor (x : X.left) : Set (Fin (dim X.left) → ℂ) :=
  {p | abelianExp X p ∈ bh4_componentSupport X x}

example (x : X.left) (p : Fin (dim X.left) → ℂ) :
    p ∈ dc1_coverDivisor X x ↔ (abelianExp X p).underlying ∈ closure ({x} : Set X.left) :=
  Iff.rfl

end Cover

section Factor

variable {n : ℕ}

/-- The factor of automorphy of a function `f` on `ℂ^n` for a subgroup `L`: the quotient
`f (z + l) / f z`, taken as a limit along the points where `f` does not vanish, so that it is
defined at the zeros of `f` too. For a reduced entire equation `f` of an `L`-invariant divisor
it is the holomorphic factor of the line bundle `𝒪(D)` on `ℂ^n / L`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.1 and Appendix B (factors of
automorphy; the factor of a theta function); Griffiths–Harris, *Principles of Algebraic
Geometry*, Ch. 1 §1 (the line bundle of a divisor). -/
def dc1_factor (f : (Fin n → ℂ) → ℂ) (L : Submodule ℤ (Fin n → ℂ)) (l : L)
    (z : Fin n → ℂ) : ℂ :=
  limUnder (𝓝[{w | f w ≠ 0}] z) (fun w ↦ f (w + l) / f w)

/-- The constant function `1` has the trivial factor. -/
example (L : Submodule ℤ (Fin n → ℂ)) (l : L) (z : Fin n → ℂ) :
    dc1_factor (fun _ ↦ 1) L l z = 1 := by
  have h : {w : Fin n → ℂ | (1 : ℂ) ≠ 0} = univ := by ext; simp
  simp only [dc1_factor, h, nhdsWithin_univ, div_one]
  exact tendsto_const_nhds.limUnder_eq

/-- The logarithm of a factor obtained by integrating its logarithmic derivative along the
segment `t ↦ t • z`, normalized by the principal logarithm at `0` and divided by `2πi`.
Source: Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4, §3.4 (logarithms of nonvanishing
holomorphic functions on simply connected regions); Birkenhake–Lange, 2nd ed., §2.1
(`a = e^{2πi f}`). -/
def dc1_factorLog {L : Submodule ℤ (Fin n → ℂ)} (a : L → (Fin n → ℂ) → ℂ) (l : L)
    (z : Fin n → ℂ) : ℂ :=
  (Complex.log (a l 0) +
      ∫ t in (0 : ℝ)..1, deriv (fun s : ℝ ↦ a l (s • z)) t / a l (t • z)) /
    (2 * Real.pi * Complex.I)

/-- The trivial factor has logarithm `0`. -/
example (L : Submodule ℤ (Fin n → ℂ)) (l : L) (z : Fin n → ℂ) :
    dc1_factorLog (fun (_ : L) (_ : Fin n → ℂ) ↦ (1 : ℂ)) l z = 0 := by
  simp [dc1_factorLog]

/-- The integral bilinear form on `L` with the values `-chernForm F` on the chosen `ℤ`-basis of
`L`. The sign is the repository's: `chernForm` of the Appell–Humbert factor is `-Im H`
(`spec_chernForm_holFactor`), so this form is `Im H` there and an effective divisor has class
`latticeClassHQ` of it (`spec_bh4_chern_comparison`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2 (the alternating
form of a factor); `chernForm`, `Basis.constr`. -/
def dc1_chernBihom {L : Submodule ℤ (Fin n → ℂ)} [Module.Free ℤ L] [Module.Finite ℤ L]
    (F : L → (Fin n → ℂ) → ℂ) : L →+ L →+ ℤ :=
  let b := Module.Free.chooseBasis ℤ L
  let φ : L →ₗ[ℤ] L →ₗ[ℤ] ℤ :=
    b.constr ℤ fun i ↦ b.constr ℤ fun j ↦ -chernForm F (b i) (b j)
  { toFun := fun l ↦ (φ l).toAddMonoidHom
    map_zero' := by ext; simp
    map_add' := fun l m ↦ by ext; simp }

/-- On basis vectors the form is `-chernForm F`, by construction. -/
example {L : Submodule ℤ (Fin n → ℂ)} [Module.Free ℤ L] [Module.Finite ℤ L]
    (F : L → (Fin n → ℂ) → ℂ) (i j : Module.Free.ChooseBasisIndex ℤ L) :
    dc1_chernBihom F (Module.Free.chooseBasis ℤ L i) (Module.Free.chooseBasis ℤ L j) =
      -chernForm F (Module.Free.chooseBasis ℤ L i) (Module.Free.chooseBasis ℤ L j) := by
  simp [dc1_chernBihom, Finsupp.single_apply]

end Factor

section ChernClass

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

/-- The first Chern class in `HQ X 2` of the line bundle of the factor of `f` on the S12 period
lattice: `latticeClassHQ` of the integral form `dc1_chernBihom` of the logarithm `dc1_factorLog`
of the factor `dc1_factor f`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2 and §1.3
(`H²(X, ℤ) = Alt²(Λ, ℤ)`); `latticeClassHQ`. -/
def dc1_chernClass (f : (Fin (dim X.left) → ℂ) → ℂ) : HQ X 2 :=
  latticeClassHQ X (dc1_chernBihom (dc1_factorLog (dc1_factor f (abelianPeriodLattice X))))

example (f : (Fin (dim X.left) → ℂ) → ℂ) :
    dc1_chernClass X f = latticeClassHQ X
      (dc1_chernBihom (dc1_factorLog (dc1_factor f (abelianPeriodLattice X)))) := rfl

end ChernClass

end HodgeLean.Foundations
