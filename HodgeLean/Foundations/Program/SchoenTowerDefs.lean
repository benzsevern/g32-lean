import HodgeLean.Foundations.Program.SchoenCycleGeometryDefs
import Mathlib.AlgebraicGeometry.Normalization

/-! # Scheme preimages for the Schoen tower
The exceptional preimage and its induced action are actual fibre products.
These constructions accept specified cover and divisor maps; they do not select
blowups or normalized covers. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Relative normalization of a specified base in a specified generic source.
For the tower, the source must be the retained function field of W₀.
Source: Stacks Project, tag 035H; Schoen (1988), §2, p. 15. -/
def s2b_normalizationOver (B : Over (Spec ↧ℂ)) {T : Scheme}
    (η : T ⟶ B.left) [QuasiCompact η] [QuasiSeparated η] : Over (Spec ↧ℂ) :=
  Over.mk (η.fromNormalization ≫ B.hom)

example (B : Over (Spec ↧ℂ)) {T : Scheme}
    (η : T ⟶ B.left) [QuasiCompact η] [QuasiSeparated η] :
    (s2b_normalizationOver B η).left = η.normalization := rfl

/-- The structure map of the specified relative normalization.
Source: Stacks Project, tag 035H; Schoen (1988), §2, p. 15, βᵢ. -/
def s2b_normalizationMap (B : Over (Spec ↧ℂ)) {T : Scheme}
    (η : T ⟶ B.left) [QuasiCompact η] [QuasiSeparated η] :
    s2b_normalizationOver B η ⟶ B := Over.homMk η.fromNormalization

example (B : Over (Spec ↧ℂ)) {T : Scheme}
    (η : T ⟶ B.left) [QuasiCompact η] [QuasiSeparated η] :
    (s2b_normalizationMap B η).left = η.fromNormalization := rfl

/-- The scheme preimage of an exceptional divisor under the specified cover.
Source: G32 v0.16, §4.1, Lemma 4.3, `Fᵢ = Wᵢ ×_{Bᵢ} Eᵢ`. -/
def s2b_preimage {W B E : Over (Spec ↧ℂ)} (β : W ⟶ B) (j : E ⟶ B) :
    Over (Spec ↧ℂ) := pullback β j

example {W B E : Over (Spec ↧ℂ)} (β : W ⟶ B) (j : E ⟶ B) :
    s2b_preimage β j = pullback β j := rfl

/-- The inclusion of the exceptional preimage in the covering scheme.
Source: Schoen (1988), §2, p. 18, exceptional-preimage square. -/
def s2b_toCover {W B E : Over (Spec ↧ℂ)} (β : W ⟶ B) (j : E ⟶ B) :
    s2b_preimage β j ⟶ W := pullback.fst β j

example {W B E : Over (Spec ↧ℂ)} (β : W ⟶ B) (j : E ⟶ B) :
    s2b_toCover β j = pullback.fst β j := rfl

/-- The finite-cover projection to the exceptional divisor.
Source: G32 v0.16, §4.1, Lemma 4.3, restriction of βᵢ. -/
def s2b_toExceptional {W B E : Over (Spec ↧ℂ)} (β : W ⟶ B) (j : E ⟶ B) :
    s2b_preimage β j ⟶ E := pullback.snd β j

example {W B E : Over (Spec ↧ℂ)} (β : W ⟶ B) (j : E ⟶ B) :
    s2b_toCover β j ≫ β = s2b_toExceptional β j ≫ j := pullback.condition

/-- Restriction of the specified generator to the actual exceptional preimage.
Source: Schoen (1988), §2, pp. 15 and 18, lifted residual action. -/
def s2b_preimageDeck {W B E : Over (Spec ↧ℂ)} (β : W ⟶ B) (j : E ⟶ B)
    (d : W ⟶ W) (hd : d ≫ β = β) : s2b_preimage β j ⟶ s2b_preimage β j :=
  pullback.lift (s2b_toCover β j ≫ d) (s2b_toExceptional β j)
    (by rw [Category.assoc, hd]; exact pullback.condition)

example {W B E : Over (Spec ↧ℂ)} (β : W ⟶ B) (j : E ⟶ B)
    (d : W ⟶ W) (hd : d ≫ β = β) :
    s2b_preimageDeck β j d hd ≫ s2b_toCover β j = s2b_toCover β j ≫ d :=
  pullback.lift_fst _ _ _

/-- The covering fibre over a point of the centre of the blowup.
Source: G32 v0.16, §4.1, Lemma 4.3, fibres of `Fᵢ → Eᵢ → Kᵢ₋₁`. -/
def s2b_coveringFibre {W B E K : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (p : E ⟶ K)
    (k : AlgebraicGeometry.ComplexPoint K) : Over (Spec ↧ℂ) :=
  pullback (s2b_toExceptional β j ≫ p) k

example {W B E K : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (p : E ⟶ K)
    (k : AlgebraicGeometry.ComplexPoint K) :
    s2b_coveringFibre β j p k = pullback (s2b_toExceptional β j ≫ p) k := rfl

/-- Pullback by the actual induced generator on complex singular cohomology.
Source: G32 v0.16, §4.1, Lemma 4.3, the representation on `Hⁿ(Fᵢ, ℂ)`. -/
def s2b_preimageCohomologyDeck {W B E : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (d : W ⟶ W) (hd : d ≫ β = β) (n : ℕ) :
    Module.End ℂ (AlgebraicTopology.Singular.Cohomology ℂ
      (TopCat.of (AlgebraicGeometry.ComplexPoint (s2b_preimage β j))) n) :=
  AlgebraicTopology.Singular.cohomologyMap ℂ n
    (TopCat.ofHom (Point.continuousMap
      (s2b_preimageDeck β j d hd)))

example {W B E : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (d : W ⟶ W) (hd : d ≫ β = β) :
    s2b_preimageCohomologyDeck β j d hd 0 0 = 0 := map_zero _

end HodgeLean.Foundations.Program
