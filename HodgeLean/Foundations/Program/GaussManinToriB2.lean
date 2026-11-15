import HodgeLean.Foundations.Program.GaussManinToriB2Proofs

/-!
# The adapter from marked periods to B2 torus families (FROZEN SPEC)

This specification constructs B2's homology filtration from D2's marked period matrix and
isolates implications from D2's full-rank and Riemann-form inputs.  It identifies each B2 fibre
with the classical quotient as a topological group and identifies D2's `F¹` and polarization
with the corresponding B2 data and identifies the underlying total spaces through the fibre
quotient maps.  Comparison with a variation of Hodge structure or a Kodaira--Spencer map remains
deferred until B2 has a cohomology VHS for a B2 family and its Kodaira--Spencer map.  HC no
distance; AV milestone no distance.
-/

noncomputable section

open Manifold
open scoped TensorProduct Matrix ContDiff

namespace HodgeLean.Foundations.Program

variable {g : ℕ}

/-- A full-rank marked period matrix induces a surjective complex period map.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
theorem d2b_cplxPeriod_surjective {P : Fin g → Fin (2 * g) → ℂ}
    (hP : d2_IsPeriodMatrix P) : Function.Surjective (d2b_cplxPeriod P) :=
  d2b_cplxPeriod_surjective_aux hP

/-- The kernel of a full-rank complex period map is a weight-one B2 filtration.
Source: Birkenhake--Lange, §1.2 and Proposition 1.1.3. -/
theorem d2b_homologyF_isWeightOne {P : Fin g → Fin (2 * g) → ℂ}
    (hP : d2_IsPeriodMatrix P) :
    b2_IsWeightOne (Fin (2 * g) → ℤ) (d2b_homologyF P) :=
  d2b_homologyF_isWeightOne_aux hP

/-- D2's `F¹` is exactly the annihilator of B2's homology filtration.
Source: Birkenhake--Lange, §1.4 (holomorphic forms and the period pairing). -/
theorem d2b_hodgeOne_eq_annihilator (P : Fin g → Fin (2 * g) → ℂ) :
    d2_hodgeOne P = {c | ∀ x ∈ d2b_homologyF P, d2b_pairing g c x = 0} :=
  d2b_hodgeOne_eq_annihilator_aux P

/-- D2 and B2 impose the same Riemann relations on the same integral matrix.
Source: Birkenhake--Lange, §4.1--§4.2; Griffiths--Harris, ch. 2, §6. -/
theorem d2b_isRiemannForm_iff {P : Fin g → Fin (2 * g) → ℂ}
    (hP : d2_IsPeriodMatrix P) (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) :
    d2_IsRiemannForm P A ↔
      b2_IsRiemannForm (Fin (2 * g) → ℤ) (d2b_homologyF P)
        (Matrix.toLinearMap₂' ℤ A) :=
  d2b_isRiemannForm_iff_aux hP A

/-- The map induced by `P_ℂ` is a bijection from B2's fibre to `ℂ^g / Λ_P`.
Source: Birkenhake--Lange, §1.1 and §2.4. -/
theorem d2b_fiberMap_bijective {P : Fin g → Fin (2 * g) → ℂ}
    (hP : d2_IsPeriodMatrix P) : Function.Bijective (d2b_fiberMap P) :=
  d2b_fiberMap_bijective_aux hP

/-- The fibre bijection induced by `P_ℂ` is a homeomorphism of topological groups.
Source: Birkenhake--Lange, §1.1; Bourbaki, *Topological Vector Spaces*, ch. I, §2.3. -/
theorem d2b_fiberMap_isHomeomorph {P : Fin g → Fin (2 * g) → ℂ}
    (hP : d2_IsPeriodMatrix P) : IsHomeomorph (d2b_fiberMap P) :=
  d2b_fiberMap_isHomeomorph_aux hP

/-- A fixed D2 Riemann matrix makes the associated B2 torus family polarized.
Source: Griffiths, Publ. Math. IHES 38 (1970), §§1--3; Birkenhake--Lange, §8.1. -/
theorem d2b_isPolarizedTorusFamily
    {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace B] [ChartedSpace E B] [IsManifold 𝓘(ℂ, E) ω B]
    (X : d2_MarkedPeriodFamily E B g) (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (hA : ∀ b, d2_IsRiemannForm (X.period b) A) :
    b2_IsPolarizedTorusFamily E (d2b_localSystem B g)
      (fun b ↦ d2b_homologyF (X.period b)) (fun _ ↦ Matrix.toLinearMap₂' ℤ A) :=
  d2b_isPolarizedTorusFamily_aux X A hA

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace B] [ChartedSpace E B]

/-- The classical quotient coordinates cover B2's total space. -/
theorem d2b_totalMap_surjective (X : d2_MarkedPeriodFamily E B g) :
    Function.Surjective (d2b_totalMap X) :=
  d2b_totalMap_surjective_aux X

/-- Two classical coordinates give the same total-space point exactly modulo the period lattice. -/
theorem d2b_totalMap_eq_iff (X : d2_MarkedPeriodFamily E B g)
    (b b' : B) (z z' : Fin g → ℂ) :
    d2b_totalMap X (b, z) = d2b_totalMap X (b', z') ↔
      b = b' ∧ z - z' ∈ d2_lattice (X.period b) :=
  d2b_totalMap_eq_iff_aux X b b' z z'

/-- The Gaussian elliptic period gives B2's standard Hodge line. -/
theorem d2b_elliptic_homologyF_eq_stdF :
    d2b_homologyF (d2_ellipticPeriod Complex.I) = b2_stdF :=
  d2b_elliptic_homologyF_eq_stdF_aux

/-- The standard integral matrix converts to B2's standard alternating form. -/
theorem d2b_stdRiemann_toLinearMap_eq_stdForm :
    Matrix.toLinearMap₂' ℤ d2_stdRiemann = b2_stdForm := rfl

/-- The positive-dimensional zero period matrix does not induce a surjective period map. -/
theorem d2b_zero_cplxPeriod_not_surjective :
    ¬ Function.Surjective (d2b_cplxPeriod (0 : Fin 1 → Fin 2 → ℂ)) :=
  d2b_zero_cplxPeriod_not_surjective_aux

/-- The positive-dimensional zero period matrix does not give a weight-one filtration. -/
theorem d2b_zero_homologyF_not_isWeightOne :
    ¬ b2_IsWeightOne (Fin 2 → ℤ) (d2b_homologyF (0 : Fin 1 → Fin 2 → ℂ)) :=
  d2b_zero_homologyF_not_isWeightOne_aux

/-- Negating the standard alternating form violates positivity on the standard Hodge line. -/
theorem d2b_neg_stdForm_not_isRiemannForm :
    ¬ b2_IsRiemannForm (Fin 2 → ℤ) b2_stdF (-b2_stdForm) :=
  d2b_neg_stdForm_not_isRiemannForm_aux

end HodgeLean.Foundations.Program
