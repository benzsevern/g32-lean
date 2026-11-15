import HodgeLean.Foundations.QuotientDuality.OrientationDefs
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance
import HodgeConjecture.Mathlib.Topology.Category.TopPair

/-! Orbit-complement pairs and the actual relative projection square. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

abbrev orbitComplementPair (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X]
    (y : orbitSpace G X) : TopPair :=
  TopPair.ofSubset (X := X) {x | orbitMap G X x ≠ y}

def orbitComplementPairMap (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X]
    (y : orbitSpace G X) : orbitComplementPair G X y ⟶ pointComplementPair y :=
  TopPair.ofHom (orbitMap G X)
    (TopCat.ofHom ⟨fun x => ⟨orbitMap G X x.1, x.2⟩,
      ((orbitMap G X).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩)
    (by ext x; rfl)

lemma relative_projection_naturality {P Q : TopPair.{0}} (f : P ⟶ Q)
    (n : ℕ) (c : Homology ℚ P.fst n) :
    relativeHomologyMap ℚ n f ((relativeHomologyProjection ℚ P n).hom c) =
      (relativeHomologyProjection ℚ Q n).hom
        (homologyMap ℚ n (TopPair.Hom.fst f) c) := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h c

lemma orbit_local_projection (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X]
    (y : orbitSpace G X) (n : ℕ) (c : Homology ℚ X n) :
    relativeHomologyMap ℚ n (orbitComplementPairMap G X y)
      ((relativeHomologyProjection ℚ (orbitComplementPair G X y) n).hom c) =
      localOrientation (orbitSpace G X) n (homologyMap ℚ n (orbitMap G X) c) y := by
  exact relative_projection_naturality (orbitComplementPairMap G X y) n c

def orbitComplementDeckMap (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X]
    [ContinuousConstSMul G X] (y : orbitSpace G X) (g : G) :
    orbitComplementPair G X y ⟶ orbitComplementPair G X y :=
  TopPair.ofSubsetHom (deckMap G X g) fun x hx => by
    change orbitMap G X (g⁻¹ • x) ≠ y
    rw [show orbitMap G X (g⁻¹ • x) = orbitMap G X x from
      MulAction.orbitRel.Quotient.quotient_smul_eq]
    exact hx

lemma orbit_relative_projection_preserved (G : Type) [Group G] (X : TopCat.{0})
    [MulAction G X] [ContinuousConstSMul G X] (y : orbitSpace G X)
    (g : G) (n : ℕ) (c : Homology ℚ X n)
    (hc : homologyMap ℚ n (deckMap G X g) c = c) :
    relativeHomologyMap ℚ n (orbitComplementDeckMap G X y g)
        ((relativeHomologyProjection ℚ (orbitComplementPair G X y) n).hom c) =
      (relativeHomologyProjection ℚ (orbitComplementPair G X y) n).hom c := by
  rw [relative_projection_naturality]
  change (relativeHomologyProjection ℚ (orbitComplementPair G X y) n).hom
      (homologyMap ℚ n (deckMap G X g) c) = _
  rw [hc]

def orbitComplementAction (G : Type) [Group G] (X : TopCat.{0})
    [MulAction G X] [ContinuousConstSMul G X] (y : orbitSpace G X) :
    G →* End (orbitComplementPair G X y) where
  toFun g := .of (orbitComplementDeckMap G X y g⁻¹)
  map_one' := by
    apply End.ext
    apply MorphismProperty.Arrow.Hom.ext <;> ext x <;>
      simp [orbitComplementDeckMap, TopPair.ofSubsetHom, deckMap] <;> rfl
  map_mul' g h := by
    apply End.ext
    apply MorphismProperty.Arrow.Hom.ext <;> ext x <;>
      simp [orbitComplementDeckMap, TopPair.ofSubsetHom, deckMap, mul_smul] <;> rfl

lemma orbitComplementAction_fixes_quotient (G : Type) [Group G] (X : TopCat.{0})
    [MulAction G X] [ContinuousConstSMul G X] (y : orbitSpace G X) (g : G) :
    (orbitComplementAction G X y g).asHom ≫ orbitComplementPairMap G X y =
      orbitComplementPairMap G X y := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext x
    apply Subtype.ext
    exact MulAction.orbitRel.Quotient.quotient_smul_eq
  · ext x
    exact MulAction.orbitRel.Quotient.quotient_smul_eq

end HodgeLean.Foundations.QuotientDuality
