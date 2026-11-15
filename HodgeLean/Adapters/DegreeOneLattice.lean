import HodgeLean.Adapters.DegreeOneLatticeProofs

/-! # Degree-one period bridge specification (FROZEN)

Scope: the period map from degree-one rational cohomology to rational characters of the lattice,
constructed from loops (`loopPeriod`, `torusPeriod`, `abelianPeriod` in
`DegreeOneLatticeDefs`), for the coordinate torus `UnitAddTorus (Fin n)` and for the S12 period
lattice `Λ = complexExponentialLattice X (dim X.left)` of a smooth projective integral complex
group `X`. The comparison with `HQ X 1` is an implication from the geometric scope already used
by `abelianTorusComparison` (`GrpObj`, `IsIntegral`, `Smooth`, `IsProjective`) only; no statement
assumes `HodgeDecomposition`, `BettiDeRhamIso` or a finiteness hypothesis, and no basis is chosen
to match dimensions. The complexified statements transport the lattice-side split of
`DegreeOneSplit` to `ℂ ⊗[ℚ] HQ X 1` along the period map; they say nothing about Dolbeault or de
Rham cohomology. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Singular

namespace HodgeLean.Adapters

/-- Periods are additive in the loop for a path-connected topological abelian group: the pointwise
sum of two loops is homologous to their concatenation. Path-connectedness is needed: on
`S¹ × ZMod 2` a class can restrict differently to the two components (statement review).
Source: Hatcher, *Algebraic Topology*, §3.C (H-spaces, Eckmann–Hilton) and §2.A (Hurewicz in
degree one). -/
theorem spec_loopPeriod_add {T : Type} [AddCommGroup T] [TopologicalSpace T]
    [IsTopologicalAddGroup T] [PathConnectedSpace T] (p q : C(UnitAddCircle, T)) :
    loopPeriod (p + q) = loopPeriod p + loopPeriod q :=
  spec_loopPeriod_add_aux p q

example (p : C(UnitAddCircle, UnitAddCircle)) :
    loopPeriod (p + p) = loopPeriod p + loopPeriod p := spec_loopPeriod_add p p

/-- Falsification check: the coordinate class `j` has period `δ_ij` along the coordinate loop
`e_i`. A zero or basis-scrambled period map fails it.
Source: Hatcher, *Algebraic Topology*, Example 3.11 and §2.2 (degree of the identity and of a
constant map). -/
theorem spec_torusPeriod_coordinate_single {n : ℕ} (i j : Fin n) :
    torusPeriod n (torusCoordinateClass j) (Pi.single i 1) = if i = j then 1 else 0 :=
  spec_torusPeriod_coordinate_single_aux i j

example : torusPeriod 2 (torusCoordinateClass 0) (Pi.single 1 1) = 0 := by
  simpa using spec_torusPeriod_coordinate_single (n := 2) 1 0

/-- The coordinate class `j` has period `λ_j` along the straight loop of `λ ∈ ℤⁿ`: the map
`z ↦ k • z` of the circle has degree `k`.
Source: Hatcher, *Algebraic Topology*, §2.2 (degree of `z ↦ zᵏ`) and Example 3.11. -/
theorem spec_torusPeriod_coordinate {n : ℕ} (j : Fin n) (l : Fin n → ℤ) :
    torusPeriod n (torusCoordinateClass j) l = l j :=
  spec_torusPeriod_coordinate_aux j l

example : torusPeriod 1 (torusCoordinateClass 0) (fun _ => -3) = -3 := by
  simpa using spec_torusPeriod_coordinate (n := 1) 0 (fun _ => -3)

/-- Naturality: pulling back along the torus homomorphism of an integer matrix `M` composes the
periods with `M` on the lattice, since `M` carries the straight loop of `λ` to that of `Mλ`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (rational representation);
functoriality of singular cohomology. -/
theorem spec_torusPeriod_matrix {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ)
    (y : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin m))) 1) (l : Fin n → ℤ) :
    torusPeriod n (cohomologyMap ℚ 1 (TopCat.ofHom (torusMatrixMap M)) y) l =
      torusPeriod m y (M.mulVec l) :=
  spec_torusPeriod_matrix_aux M y l

example {n : ℕ} (y : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1) (l : Fin n → ℤ) :
    torusPeriod n (cohomologyMap ℚ 1 (TopCat.ofHom (torusMatrixMap (1 : Matrix _ _ ℤ))) y) l =
      torusPeriod n y l := by
  simpa using spec_torusPeriod_matrix (1 : Matrix (Fin n) (Fin n) ℤ) y l

/-- Degree-one rational cohomology of the coordinate torus is the rational character dual of
`ℤⁿ`, by the period map itself.
Source: Hatcher, *Algebraic Topology*, Example 3.11, Theorem 3.15 and §3.1 (universal
coefficients); Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
theorem spec_torusPeriod_equiv (n : ℕ) :
    ∃ e : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1 ≃ₗ[ℚ] ((Fin n → ℤ) →+ ℚ),
      ∀ x l, e x l = torusPeriod n x l :=
  spec_torusPeriod_equiv_aux n

example (n : ℕ) : Function.Injective (torusPeriod n) := by
  obtain ⟨e, he⟩ := spec_torusPeriod_equiv n
  intro x y hxy
  apply e.injective
  refine DFunLike.ext _ _ fun l => ?_
  rw [he, he, hxy]

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- The S12 periods of a class of `HQ X 1` are additive on the period lattice.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; `spec_loopPeriod_add`
with the S12 identity `exp((l + l')t) = exp(lt) exp(l't)`. -/
theorem spec_abelianPeriod_add (x : HQ X 1) (l l' : abelianPeriodLattice X) :
    abelianPeriod X x (l + l') = abelianPeriod X x l + abelianPeriod X x l' :=
  spec_abelianPeriod_add_aux X x l l'

example (x : HQ X 1) (l : abelianPeriodLattice X) :
    abelianPeriod X x (l + l) = abelianPeriod X x l + abelianPeriod X x l :=
  spec_abelianPeriod_add X x l l

/-- Naturality for the S12 homeomorphism: the periods of `x` along the S12 loops are the torus
periods of `abelianTorusComparison X 1 x` at the S12 basis coordinates, because the uniformization
carries `t ↦ exp(t • l)` to the straight loop of `(abelianLatticeBasis X).repr l`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; S12
`complexPointUniformization`, `LatticeTorus.quotientEquivOfBasis_mk`. -/
theorem spec_abelianPeriod_torus (x : HQ X 1) (l : abelianPeriodLattice X) :
    abelianPeriod X x l =
      torusPeriod (2 * dim X.left) (abelianTorusComparison X 1 x)
        ((abelianLatticeBasis X).repr l) :=
  spec_abelianPeriod_torus_aux X x l

example (x : HQ X 1) (l : abelianPeriodLattice X) :
    abelianPeriod X x l = loopPeriod (torusLoop ((abelianLatticeBasis X).repr l))
      (abelianTorusComparison X 1 x) := spec_abelianPeriod_torus X x l

/-- `HQ X 1` is the rational character dual of the S12 period lattice, by the period map.
This is an implication from the scope of `abelianTorusComparison` only.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`H¹(X, ℤ) = Hom(Λ, ℤ)`);
`spec_torusPeriod_equiv`, `spec_abelianPeriod_torus`, `abelianTorusComparison`. -/
theorem spec_abelianPeriod_equiv :
    ∃ e : HQ X 1 ≃ₗ[ℚ] (abelianPeriodLattice X →+ ℚ),
      ∀ x l, e x l = abelianPeriod X x l :=
  spec_abelianPeriod_equiv_aux X

example : Function.Injective (abelianPeriod X) := by
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv X
  intro x y hxy
  apply e.injective
  refine DFunLike.ext _ _ fun l => ?_
  rw [he, he, hxy]

/-- Complexified compatibility: there is a complex-linear isomorphism
`ℂ ⊗[ℚ] HQ X 1 ≃ Hom_ℝ(ℂ^g, ℂ)` whose restriction to the period lattice is the complexified
period map.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`Λ ⊗ ℝ = ℂ^g`) and §1.4. -/
theorem spec_complexAbelianPeriod_restriction :
    ∃ Φ : ℂ ⊗[ℚ] HQ X 1 ≃ₗ[ℂ] DegreeOneLatticeDual (dim X.left),
      ∀ ω, latticeRestriction X (Φ ω) = complexAbelianPeriod X ω :=
  spec_complexAbelianPeriod_restriction_aux X

example (c : ℂ) (x : HQ X 1) (l : abelianPeriodLattice X) :
    ∃ Φ : ℂ ⊗[ℚ] HQ X 1 ≃ₗ[ℂ] DegreeOneLatticeDual (dim X.left),
      Φ (c ⊗ₜ x) l = c * (abelianPeriod X x l : ℂ) := by
  obtain ⟨Φ, hΦ⟩ := spec_complexAbelianPeriod_restriction X
  refine ⟨Φ, ?_⟩
  have h := congrFun (hΦ (c ⊗ₜ x)) l
  rw [latticeRestriction] at h
  simpa [complexAbelianPeriod] using h

/-- The transported split: `ℂ ⊗[ℚ] HQ X 1` is the internal direct sum of the classes with
complex-linear periods and the classes with conjugate-linear periods.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1;
`spec_H1_lattice_split`, `spec_H1_lattice_disjoint`. -/
theorem spec_complexH1_split :
    complexHolomorphicH1 X ⊔ complexAntiholomorphicH1 X = ⊤ ∧
      Disjoint (complexHolomorphicH1 X) (complexAntiholomorphicH1 X) :=
  spec_complexH1_split_aux X

example : complexHolomorphicH1 X ⊔ complexAntiholomorphicH1 X = ⊤ :=
  (spec_complexH1_split X).1

/-- Each transported summand of `ℂ ⊗[ℚ] HQ X 1` has complex dimension `g = dim X.left`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 and Theorem 1.4.1;
`spec_H1_lattice_holomorphic_dimension`, `spec_H1_lattice_antiholomorphic_dimension`. -/
theorem spec_complexH1_dimension :
    Module.finrank ℂ (complexHolomorphicH1 X) = dim X.left ∧
      Module.finrank ℂ (complexAntiholomorphicH1 X) = dim X.left :=
  spec_complexH1_dimension_aux X

example : Module.finrank ℂ (complexAntiholomorphicH1 X) = dim X.left :=
  (spec_complexH1_dimension X).2

/-- Rational conjugation `HodgeBlocks.sigmaQ` (conjugating the scalar factor) carries the
transported holomorphic summand onto the antiholomorphic one, since periods are rational.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1;
`spec_H1_lattice_conjugation_exchanges`. -/
theorem spec_complexH1_conjugation_exchanges :
    (complexHolomorphicH1 X).map (HodgeBlocks.sigmaQ (HQ X 1)) = complexAntiholomorphicH1 X :=
  spec_complexH1_conjugation_exchanges_aux X

example (ω : ℂ ⊗[ℚ] HQ X 1) (hω : ω ∈ complexHolomorphicH1 X) :
    HodgeBlocks.sigmaQ (HQ X 1) ω ∈ complexAntiholomorphicH1 X := by
  rw [← spec_complexH1_conjugation_exchanges X]
  exact Submodule.mem_map_of_mem hω

end HodgeLean.Adapters
