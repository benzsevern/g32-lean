import HodgeLean.Foundations.Singular.Cup
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Sheaf.CochainSubdivision

/-!
# Cup product on cover-small singular cochains

Cover-small singular simplices form upstream's simplicial subcomplex. Its cochains
carry the Alexander–Whitney product, Leibniz rule, associativity and unit. Restriction
from singular cochains is linear, commutes with the coboundary, and preserves cup
products and the unit: it is a map of differential graded cochain algebras.
This supplies the cochain compatibility needed by S4 on the C7 torus track and
retires nothing yet. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory
open AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open scoped Simplicial

namespace HodgeLean.Foundations.Singular

variable {R : Type} [CommRing R] {ι : Type} (Y : TopCat.{0}) (U : ι → Set Y)

/-- Cochains on singular simplices whose images lie in a member of the family `U`.
No openness or covering assumption is needed to define this cochain algebra.
Source: upstream `HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Excision/CoverSmall.lean`
at `2ead713`, `coverSmallSingularSubcomplex`; Hatcher, *Algebraic Topology*, §3.1.
-/
abbrev SmallCochain (n : ℕ) := Cochain R (coverSmallSingularSubcomplex Y U : SSet) n

example (n : ℕ) (c : ChainGroup R (coverSmallSingularSubcomplex Y U : SSet) n) :
    (0 : SmallCochain (R := R) Y U n) c = 0 := rfl

/-- The Alexander–Whitney cup product on cover-small singular cochains.
Source: Hatcher, *Algebraic Topology*, §3.2, front/back definition of cup product.
-/
def smallCupCochain (p q : ℕ) :
    SmallCochain (R := R) Y U p →ₗ[R] SmallCochain (R := R) Y U q →ₗ[R]
      SmallCochain (R := R) Y U (p + q) :=
  HodgeLean.Foundations.Simplicial.cupCochain (coverSmallSingularSubcomplex Y U : SSet) p q

/-- Small-cochain cup product evaluates on the two faces of a small simplex.
Source: Hatcher, *Algebraic Topology*, §3.2, front/back definition of cup product.
-/
theorem smallCupCochain_apply_simplex (p q : ℕ)
    (φ : SmallCochain (R := R) Y U p) (ψ : SmallCochain (R := R) Y U q)
    (σ : (coverSmallSingularSubcomplex Y U : SSet) _⦋p + q⦌) :
    smallCupCochain Y U p q φ ψ (chainOfSimplex R σ) =
      φ (chainOfSimplex R (frontFace (coverSmallSingularSubcomplex Y U : SSet) σ)) *
        ψ (chainOfSimplex R (backFace (coverSmallSingularSubcomplex Y U : SSet) σ)) :=
  HodgeLean.Foundations.Simplicial.cupCochain_apply_simplex _ p q φ ψ σ

/-- The small-cochain unit is constant one on every small vertex.
Source: Hatcher, *Algebraic Topology*, §3.2, unit of the cup product.
-/
def smallUnitCochain : SmallCochain (R := R) Y U 0 :=
  HodgeLean.Foundations.Simplicial.unitCochain (coverSmallSingularSubcomplex Y U : SSet)

/-- Evaluation of the small-cochain unit.
Source: Hatcher, *Algebraic Topology*, §3.2, unit of the cup product.
-/
@[simp] theorem smallUnitCochain_apply_simplex
    (σ : (coverSmallSingularSubcomplex Y U : SSet) _⦋0⦌) :
    smallUnitCochain (R := R) Y U (chainOfSimplex R σ) = 1 :=
  HodgeLean.Foundations.Simplicial.unitCochain_apply_simplex _ σ

/-- The small-cochain unit is closed.
Source: Hatcher, *Algebraic Topology*, §3.2, unit of the cup product.
-/
@[simp] theorem coboundary_smallUnitCochain :
    coboundary R 0 (smallUnitCochain (R := R) Y U) = 0 :=
  HodgeLean.Foundations.Simplicial.coboundary_unitCochain _

/-- The Leibniz rule on small cochains, including the canonical degree reassociation.
Source: Hatcher, *Algebraic Topology*, §3.2, Lemma 3.6.
-/
theorem coboundary_smallCupCochain (p q : ℕ)
    (φ : SmallCochain (R := R) Y U p) (ψ : SmallCochain (R := R) Y U q) :
    coboundary R (p + q) (smallCupCochain Y U p q φ ψ) =
      (smallCupCochain Y U (p + 1) q (coboundary R p φ) ψ).comp (reassocChain R p q) +
        (-1 : R) ^ p • smallCupCochain Y U p (q + 1) φ (coboundary R q ψ) :=
  HodgeLean.Foundations.Simplicial.coboundary_cupCochain _ p q φ ψ

/-- Associativity on small cochains.
Source: Hatcher, *Algebraic Topology*, §3.2, associativity of the cup product.
-/
theorem smallCupCochain_assoc (p q r : ℕ)
    (φ : SmallCochain (R := R) Y U p) (ψ : SmallCochain (R := R) Y U q)
    (χ : SmallCochain (R := R) Y U r) :
    smallCupCochain Y U (p + q) r (smallCupCochain Y U p q φ ψ) χ =
      (smallCupCochain Y U p (q + r) φ (smallCupCochain Y U q r ψ χ)).comp
        (((coverSmallSingularSubcomplex Y U : SSet).chainComplex (ModuleCat.of R R)).XIsoOfEq
          (Nat.add_assoc p q r)).hom.hom :=
  HodgeLean.Foundations.Simplicial.cupCochain_assoc _ p q r φ ψ χ

/-- The right unit law on small cochains.
Source: Hatcher, *Algebraic Topology*, §3.2, unit of the cup product.
-/
theorem smallCupCochain_one (p : ℕ) (φ : SmallCochain (R := R) Y U p) :
    smallCupCochain Y U p 0 φ (smallUnitCochain Y U) = φ :=
  HodgeLean.Foundations.Simplicial.cupCochain_one _ p φ

/-- The left unit law on small cochains.
Source: Hatcher, *Algebraic Topology*, §3.2, unit of the cup product.
-/
theorem one_smallCupCochain (q : ℕ) (ψ : SmallCochain (R := R) Y U q) :
    smallCupCochain Y U 0 q (smallUnitCochain Y U) ψ =
      ψ.comp (((coverSmallSingularSubcomplex Y U : SSet).chainComplex (ModuleCat.of R R)).XIsoOfEq
        (Nat.zero_add q)).hom.hom :=
  HodgeLean.Foundations.Simplicial.one_cupCochain _ q ψ

/-- Small-cochain cup products are natural for maps of the small simplicial sets.
Source: Hatcher, *Algebraic Topology*, §3.2, naturality of the cup product.
-/
theorem smallCupCochain_naturality {κ : Type} {Z : TopCat.{0}} (V : κ → Set Z)
    (f : (coverSmallSingularSubcomplex Z V : SSet) ⟶ (coverSmallSingularSubcomplex Y U : SSet))
    (p q : ℕ) (φ : SmallCochain (R := R) Y U p) (ψ : SmallCochain (R := R) Y U q) :
    cochainMap R f (p + q) (smallCupCochain Y U p q φ ψ) =
      smallCupCochain Z V p q (cochainMap R f p φ) (cochainMap R f q ψ) :=
  HodgeLean.Foundations.Simplicial.cupCochain_naturality _ f p q φ ψ

/-- Restriction of singular cochains to the cover-small simplicial subcomplex.
Source: Hatcher, *Algebraic Topology*, §3.1, pullback of cochains; upstream
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Excision/CoverSmall.lean` at `2ead713`.
-/
def smallCochainRestriction (n : ℕ) :
    Cochain R (TopCat.toSSet.obj Y) n →ₗ[R] SmallCochain (R := R) Y U n :=
  cochainMap R (coverSmallSingularSubcomplex Y U).ι n

example : smallCochainRestriction (R := ℚ) (TopCat.of PUnit) (fun _ : PUnit => Set.univ) 0 0 = 0 :=
  map_zero _

/-- Restriction preserves cup products degree by degree.
Source: Hatcher, *Algebraic Topology*, §3.2, naturality of cup product.
-/
theorem smallCochainRestriction_cup (p q : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) p) (ψ : Cochain R (TopCat.toSSet.obj Y) q) :
    smallCochainRestriction Y U (p + q) (cupCochain Y p q φ ψ) =
      smallCupCochain Y U p q (smallCochainRestriction Y U p φ) (smallCochainRestriction Y U q ψ) :=
  HodgeLean.Foundations.Simplicial.cupCochain_naturality _ (coverSmallSingularSubcomplex Y U).ι p q φ ψ

/-- Restriction preserves the cochain unit.
Source: Hatcher, *Algebraic Topology*, §3.2, naturality of the cup unit.
-/
@[simp] theorem smallCochainRestriction_unit :
    smallCochainRestriction Y U 0 (unitCochain (R := R) Y) = smallUnitCochain Y U :=
  HodgeLean.Foundations.Simplicial.cochainMap_unitCochain _ (coverSmallSingularSubcomplex Y U).ι

/-- Restriction commutes with the differential, as a map of differential graded cochain algebras.
Source: Hatcher, *Algebraic Topology*, §3.1, induced maps on cochains.
-/
theorem smallCochainRestriction_coboundary (n : ℕ) (φ : Cochain R (TopCat.toSSet.obj Y) n) :
    smallCochainRestriction Y U (n + 1) (coboundary R n φ) =
      coboundary R n (smallCochainRestriction Y U n φ) :=
  (HodgeLean.Foundations.Simplicial.coboundary_cochainMap _
    (coverSmallSingularSubcomplex Y U).ι n φ).symm

example : smallCupCochain (TopCat.of PUnit) (fun _ : PUnit => Set.univ) 0 0
    ((2 : ℚ) • smallUnitCochain (R := ℚ) _ _) ((3 : ℚ) • smallUnitCochain (R := ℚ) _ _) =
      (6 : ℚ) • smallUnitCochain (R := ℚ) _ _ := by
  convert HodgeLean.Foundations.Simplicial.cupCochain_constants
    (coverSmallSingularSubcomplex (TopCat.of PUnit) (fun _ : PUnit => Set.univ) : SSet) (2 : ℚ) 3 using 1 <;>
    norm_num [smallCupCochain, smallUnitCochain]

example : smallCupCochain (R := ℚ) (TopCat.of PUnit) (fun _ : PUnit => Set.univ) 0 0
    (smallUnitCochain _ _) (smallUnitCochain _ _) = smallUnitCochain _ _ :=
  smallCupCochain_one _ _ 0 _

example : smallUnitCochain (R := ℚ) (TopCat.of PUnit) (fun _ : PUnit => Set.univ) ≠ 0 := by
  let P := TopCat.of PUnit
  let U : PUnit → Set P := fun _ => Set.univ
  let τ : (TopCat.toSSet.obj P) _⦋0⦌ :=
    (P.toSSetObjEquiv _).symm (ContinuousMap.const _ PUnit.unit)
  have ht : τ ∈ (coverSmallSingularSubcomplex P U).obj (Opposite.op ⦋0⦌) := by
    apply (mem_coverSmallSingularSubcomplex_iff_exists_preimage P U τ).mpr
    refine ⟨PUnit.unit, ((TopCat.of (U PUnit.unit)).toSSetObjEquiv _).symm
      (ContinuousMap.const _ ⟨PUnit.unit, Set.mem_univ _⟩), ?_⟩
    apply (P.toSSetObjEquiv _).injective
    ext x
  let σ : (coverSmallSingularSubcomplex P U : SSet) _⦋0⦌ := ⟨τ, ht⟩
  intro hz
  have hv := LinearMap.congr_fun hz (chainOfSimplex ℚ σ)
  simp at hv



/-! ## Axiom audit -/

#print axioms SmallCochain
#print axioms smallCupCochain
#print axioms smallCupCochain_apply_simplex
#print axioms smallUnitCochain
#print axioms smallUnitCochain_apply_simplex
#print axioms coboundary_smallUnitCochain
#print axioms coboundary_smallCupCochain
#print axioms smallCupCochain_assoc
#print axioms smallCupCochain_one
#print axioms one_smallCupCochain
#print axioms smallCupCochain_naturality
#print axioms smallCochainRestriction
#print axioms smallCochainRestriction_cup
#print axioms smallCochainRestriction_unit
#print axioms smallCochainRestriction_coboundary

end HodgeLean.Foundations.Singular
