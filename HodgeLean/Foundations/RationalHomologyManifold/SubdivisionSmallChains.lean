import HodgeLean.Foundations.RationalHomologyManifold.RationalChainLifts
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Subdivision.AffineSupport
import Mathlib.CategoryTheory.Functor.OfSequence

/-! Rational subdivision iterates and cover-small chains.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Extend each actual integral subdivision iterate to rational chains.
Source: Hatcher, Algebraic Topology, section 2.1, barycentric subdivision.
HC no distance; AV milestone no distance.
-/
def rationalSubdivisionIterate (X : TopCat.{0}) (m : ℕ) :
    SingularChainComplex ℚ X ⟶ SingularChainComplex ℚ X :=
  coefficientizeSimplicialChainMap ℚ (TopCat.toSSet.obj X) (TopCat.toSSet.obj X)
    (affineSingularSubdivisionIterate X m)

#print axioms rationalSubdivisionIterate
/-- Rational subdivision iterates retain the actual successor composition.
Source: Hatcher, Algebraic Topology, section 2.1, barycentric subdivision.
HC no distance; AV milestone no distance.
-/
theorem rationalSubdivisionIterate_succ (X : TopCat.{0}) (m : ℕ) :
    rationalSubdivisionIterate X (m + 1) =
      rationalSubdivisionIterate X m ≫ rationalSubdivision X := by
  unfold rationalSubdivisionIterate rationalSubdivision
  rw [affineSingularSubdivisionIterate_succ, coefficientizeSimplicialChainMap_comp]

#print axioms rationalSubdivisionIterate_succ
/-- Rational subdivision exponents add by composing their actual chain maps.
Source: Hatcher, Algebraic Topology, section 2.1, iterated subdivision.
HC no distance; AV milestone no distance.
-/
theorem rationalSubdivisionIterate_add (X : TopCat.{0}) (m r : ℕ) :
    rationalSubdivisionIterate X (m + r) =
      rationalSubdivisionIterate X m ≫ rationalSubdivisionIterate X r := by
  unfold rationalSubdivisionIterate
  rw [affineSingularSubdivisionIterate_add, coefficientizeSimplicialChainMap_comp]

#print axioms rationalSubdivisionIterate_add
/-- Actual rational subdivision of cover-small chains, obtained from the integral operator.
Source: Hatcher, Algebraic Topology, section 2.1, subdivision subordinate to a cover.
HC no distance; AV milestone no distance.
-/
def coverSmallRationalSubdivisionIterate {ι : Type} (X : TopCat.{0}) (U : ι → Set X) (m : ℕ) :
    CoverSmallCoefficientSingularChainComplex ℚ X U ⟶
      CoverSmallCoefficientSingularChainComplex ℚ X U :=
  coefficientizeSimplicialChainMap ℚ (coverSmallSingularSubcomplex X U : SSet)
    (coverSmallSingularSubcomplex X U : SSet) (coverSmallAffineSubdivisionIterate X U m)

#print axioms coverSmallRationalSubdivisionIterate
/-- Rational cover-small subdivision commutes with the actual small-chain inclusion.
Source: Hatcher, Algebraic Topology, section 2.1, subdivision subordinate to a cover.
HC no distance; AV milestone no distance.
-/
theorem coverSmallRationalSubdivisionIterate_comp_inclusion {ι : Type}
    (X : TopCat.{0}) (U : ι → Set X) (m : ℕ) :
    coverSmallRationalSubdivisionIterate X U m ≫ coverSmallCoefficientSingularChainInclusion ℚ X U =
      coverSmallCoefficientSingularChainInclusion ℚ X U ≫ rationalSubdivisionIterate X m := by
  have h := congrArg
    (coefficientizeSimplicialChainMap ℚ (coverSmallSingularSubcomplex X U : SSet)
      (TopCat.toSSet.obj X)) (coverSmallAffineSubdivisionIterate_comp_inclusion X U m)
  simpa only [coefficientizeSimplicialChainMap_comp,
    coverSmallIntegralSingularChainInclusion, coefficientizeSimplicialChainMap_chainComplexMap,
    coverSmallCoefficientSingularChainInclusion, coverSmallRationalSubdivisionIterate,
    rationalSubdivisionIterate] using h

#print axioms coverSmallRationalSubdivisionIterate_comp_inclusion
/-- Each finite rational singular chain becomes subordinate to an open cover at an actual subdivision stage.
Source: Hatcher, Algebraic Topology, section 2.1, the small-chain subdivision theorem.
HC no distance; AV milestone no distance.
-/
theorem rationalSubdivision_eventually_small {ι : Type} (X : TopCat.{0}) (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ)
    (n : ℕ) (z : (SingularChainComplex ℚ X).X n) :
    ∃ (m : ℕ) (w : (CoverSmallCoefficientSingularChainComplex ℚ X U).X n),
      (coverSmallCoefficientSingularChainInclusion ℚ X U).f n w =
        (rationalSubdivisionIterate X m).f n z := by
  obtain ⟨d, hd, y, hy⟩ := rationalChain_integral_multiple X n z
  obtain ⟨m, w, hw⟩ := coverSmallAffineSubdivisionEventuallySmall_of_openCover X U hUopen hUcover n y
  let S := (coverSmallSingularSubcomplex X U : SSet)
  let c : (CoverSmallCoefficientSingularChainComplex ℚ X U).X n :=
    (integralToCoefficientChainComponent ℚ S n).hom w
  have hinc := integralToCoefficientChainComponent_naturality ℚ S (TopCat.toSSet.obj X) n n
    ((coverSmallIntegralSingularChainInclusion X U).f n)
  simp only [coverSmallIntegralSingularChainInclusion,
    coefficientizeSimplicialChainComponent_chainComplexMap] at hinc
  have hinc' := ConcreteCategory.congr_hom hinc w
  change (coverSmallCoefficientSingularChainInclusion ℚ X U).f n c =
    (integralToCoefficientChainComponent ℚ (TopCat.toSSet.obj X) n).hom
      ((coverSmallIntegralSingularChainInclusion X U).f n w) at hinc'
  rw [hw] at hinc'
  have hsub := integralToCoefficientChainComponent_naturality ℚ (TopCat.toSSet.obj X)
    (TopCat.toSSet.obj X) n n ((affineSingularSubdivisionIterate X m).f n)
  have hsub' := ConcreteCategory.congr_hom hsub y
  change (rationalSubdivisionIterate X m).f n
      ((integralToCoefficientChainComponent ℚ (TopCat.toSSet.obj X) n).hom y) =
    (integralToCoefficientChainComponent ℚ (TopCat.toSSet.obj X) n).hom
      ((affineSingularSubdivisionIterate X m).f n y) at hsub'
  rw [hy] at hsub'
  refine ⟨m, (d : ℚ)⁻¹ • c, ?_⟩
  rw [map_smul, hinc', ← hsub', map_smul, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hd), one_smul]

#print axioms rationalSubdivision_eventually_small
/-- A chain already subordinate to a cover remains so after any additional subdivision depth.
Source: Hatcher, Algebraic Topology, section 2.1, subdivision subordinate to a cover.
HC no distance; AV milestone no distance.
-/
theorem rationalSubdivision_small_add {ι : Type} (X : TopCat.{0}) (U : ι → Set X)
    (n m r : ℕ) (z : (SingularChainComplex ℚ X).X n)
    (w : (CoverSmallCoefficientSingularChainComplex ℚ X U).X n)
    (hw : (coverSmallCoefficientSingularChainInclusion ℚ X U).f n w =
      (rationalSubdivisionIterate X m).f n z) :
    ∃ v : (CoverSmallCoefficientSingularChainComplex ℚ X U).X n,
      (coverSmallCoefficientSingularChainInclusion ℚ X U).f n v =
        (rationalSubdivisionIterate X (m + r)).f n z := by
  refine ⟨(coverSmallRationalSubdivisionIterate X U r).f n w, ?_⟩
  have h := congrArg (fun f => f.f n)
    (coverSmallRationalSubdivisionIterate_comp_inclusion X U r)
  have h' := ConcreteCategory.congr_hom h w
  change (coverSmallCoefficientSingularChainInclusion ℚ X U).f n
      ((coverSmallRationalSubdivisionIterate X U r).f n w) =
    (rationalSubdivisionIterate X r).f n
      ((coverSmallCoefficientSingularChainInclusion ℚ X U).f n w) at h'
  rw [hw] at h'
  rw [h', rationalSubdivisionIterate_add]
  rfl

#print axioms rationalSubdivision_small_add
/-- A finite family of rational chains becomes subordinate to a cover at one common actual subdivision stage.
Source: Hatcher, Algebraic Topology, section 2.1, the finite-chain subdivision argument.
HC no distance; AV milestone no distance.
-/
theorem rationalSubdivision_finite_eventually_small {ι κ : Type} [Fintype κ]
    (X : TopCat.{0}) (U : ι → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcover : ⋃ i, U i = Set.univ) (n : ℕ) (z : κ → (SingularChainComplex ℚ X).X n) :
    ∃ m : ℕ, ∀ k, ∃ w : (CoverSmallCoefficientSingularChainComplex ℚ X U).X n,
      (coverSmallCoefficientSingularChainInclusion ℚ X U).f n w =
        (rationalSubdivisionIterate X m).f n (z k) := by
  classical
  choose m w hw using fun k => rationalSubdivision_eventually_small X U hUopen hUcover n (z k)
  refine ⟨Finset.univ.sup m, fun k => ?_⟩
  have hk : m k ≤ Finset.univ.sup m := Finset.le_sup (Finset.mem_univ k)
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hk
  rw [hr]
  exact rationalSubdivision_small_add X U n (m k) r (z k) (w k) (hw k)

#print axioms rationalSubdivision_finite_eventually_small
/-- One actual subdivision depth works for finitely many rational chains and finitely many open covers.
Source: Hatcher, Algebraic Topology, section 2.1, the finite-chain subdivision argument.
HC no distance; AV milestone no distance.
-/
theorem rationalSubdivision_finite_covers_eventually_small {ι κ τ : Type}
    [Fintype κ] [Fintype τ] (X : TopCat.{0}) (U : τ → ι → Set X)
    (hUopen : ∀ j i, IsOpen (U j i)) (hUcover : ∀ j, ⋃ i, U j i = Set.univ)
    (n : ℕ) (z : κ → (SingularChainComplex ℚ X).X n) :
    ∃ m : ℕ, ∀ j k, ∃ w : (CoverSmallCoefficientSingularChainComplex ℚ X (U j)).X n,
      (coverSmallCoefficientSingularChainInclusion ℚ X (U j)).f n w =
        (rationalSubdivisionIterate X m).f n (z k) := by
  classical
  choose m w hw using fun j =>
    rationalSubdivision_finite_eventually_small X (U j) (hUopen j) (hUcover j) n z
  refine ⟨Finset.univ.sup m, fun j k => ?_⟩
  have hj : m j ≤ Finset.univ.sup m := Finset.le_sup (Finset.mem_univ j)
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hj
  rw [hr]
  exact rationalSubdivision_small_add X (U j) n (m j) r (z k) (w j k) (hw j k)

#print axioms rationalSubdivision_finite_covers_eventually_small
/-- The zero-depth rational subdivision is the actual identity chain map.
Source: Hatcher, Algebraic Topology, section 2.1, finite iteration of subdivision.
HC no distance; AV milestone no distance.
-/
theorem rationalSubdivisionIterate_zero (X : TopCat.{0}) :
    rationalSubdivisionIterate X 0 = 𝟙 _ := by
  unfold rationalSubdivisionIterate
  rw [affineSingularSubdivisionIterate_zero, coefficientizeSimplicialChainMap_id]
  rfl

#print axioms rationalSubdivisionIterate_zero
/-- The actual rational chain complex repeated with affine subdivision as its transition map.
Source: Hatcher, Algebraic Topology, section 2.1, iterated barycentric subdivision.
HC no distance; AV milestone no distance.
-/
def rationalSubdivisionDiagram (X : TopCat.{0}) :
    ℕ ⥤ ChainComplex (ModuleCat ℚ) ℕ :=
  Functor.ofSequence (X := fun _ : ℕ => SingularChainComplex ℚ X)
    (fun _ => rationalSubdivision X)

#print axioms rationalSubdivisionDiagram
/-- A transition across an actual rational subdivision sequence is the corresponding coefficient-extended integral iterate.
Source: Hatcher, Algebraic Topology, section 2.1, iterated barycentric subdivision.
HC no distance; AV milestone no distance.
-/
theorem rationalSubdivisionDiagram_map_add (X : TopCat.{0}) (m r : ℕ) :
    (rationalSubdivisionDiagram X).map (homOfLE (Nat.le_add_right m r)) =
      rationalSubdivisionIterate X r := by
  induction r with
  | zero =>
    have heq : homOfLE (Nat.le_add_right m 0) = 𝟙 m := Subsingleton.elim _ _
    rw [heq, (rationalSubdivisionDiagram X).map_id, rationalSubdivisionIterate_zero]
    rfl
  | succ r ih =>
    have heq : homOfLE (Nat.le_add_right m (r + 1)) =
        homOfLE (Nat.le_add_right m r) ≫ homOfLE (Nat.le_succ (m + r)) := Subsingleton.elim _ _
    have hs : (rationalSubdivisionDiagram X).map (homOfLE (Nat.le_succ (m + r))) =
        rationalSubdivision X := Functor.ofSequence_map_homOfLE_succ _ _
    rw [heq, (rationalSubdivisionDiagram X).map_comp, ih, hs, rationalSubdivisionIterate_succ]

#print axioms rationalSubdivisionDiagram_map_add
end HodgeLean.Foundations.RationalHomologyManifold
