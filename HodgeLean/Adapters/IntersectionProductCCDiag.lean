import HodgeLean.Adapters.CycleClassDivisorLocalTransport
import HodgeLean.Adapters.IntersectionProductDiagonalTor
import HodgeLean.Adapters.IntersectionProductDefs

/-! # Diagonal constructions for the local intersection coefficient -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs TensorProduct

namespace HodgeLean.Adapters

universe u

/-- Diagonal Tor, regarded as a module over the first factor.
Source: Serre, *Algèbre locale, multiplicités*, V, B.3. -/
def a3cc2_diagonalTor (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (M N : ModuleCat.{u} A) [Module k N] [IsScalarTower k A N] (i : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (a3d_inl k A)).obj
    (((Tor (ModuleCat.{u} (A ⊗[k] A)) i).obj (a3d_XM k A N M)).obj (a3d_SD k A))

/-- Reduction to the diagonal preserves each Tor length over the first factor.
Source: Serre, *Algèbre locale, multiplicités*, V, B.3; `a3d_tor_diag`. -/
theorem a3cc2_diagonalTor_length (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (M N : ModuleCat.{u} A) [Module k N] [IsScalarTower k A N] (i : ℕ) :
    Module.length A (((Tor (ModuleCat.{u} A) i).obj M).obj N) =
      Module.length A (a3cc2_diagonalTor k A M N i) := by
  obtain ⟨e⟩ := a3d_tor_diag k A N M i
  exact e.toLinearEquiv.length_eq

/-- The truncated Euler characteristic of diagonal Tor over the first factor.
Source: Serre, *Algèbre locale, multiplicités*, V, B.3. -/
def a3cc2_diagonalEuler (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (M N : ModuleCat.{u} A) [Module k N] [IsScalarTower k A N] (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ i * ((Module.length A (a3cc2_diagonalTor k A M N i)).toNat : ℤ)

/-- Termwise reduction to the diagonal also preserves every truncation of the Euler sum.
Source: Serre, *Algèbre locale, multiplicités*, V, B.3. -/
theorem a3cc2_diagonalEuler_eq (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (M N : ModuleCat.{u} A) [Module k N] [IsScalarTower k A N] (n : ℕ) :
    a3cc2_diagonalEuler k A M N n =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        ((Module.length A (((Tor (ModuleCat.{u} A) i).obj M).obj N)).toNat : ℤ) := by
  unfold a3cc2_diagonalEuler
  apply Finset.sum_congr rfl
  intro i _
  rw [a3cc2_diagonalTor_length k A M N i]

/-- The actual Serre multiplicity is the diagonal Euler sum with the same cutoff.
Source: Serre, *Algèbre locale, multiplicités*, V, B.3. -/
theorem a3cc2_serreMult_eq_diagonalEuler (k : Type u) [Field k]
    (X : Scheme.{u}) (z x y : X) [Algebra k (X.presheaf.stalk z)] :
    a3i_serreMult X z x y =
      a3cc2_diagonalEuler k (X.presheaf.stalk z)
        (ModuleCat.of _ (X.presheaf.stalk z ⧸ a3i_stalkIdeal X z x))
        (ModuleCat.of _ (X.presheaf.stalk z ⧸ a3i_stalkIdeal X z y))
        (Order.coheight z).toNat := by
  rw [a3cc2_diagonalEuler_eq]
  rfl

/-- The relative exterior product on the topological square, with product support.
Source: Hatcher, *Algebraic Topology*, §3.2, cross products. -/
def a3cc2_relativeExternal (Y : TopCat.{0}) (S T : Closeds Y) (p q : ℕ)
    (u : RelativeCohomology ℚ (TopPair.ofSubset (S : Set Y)ᶜ) p)
    (v : RelativeCohomology ℚ (TopPair.ofSubset (T : Set Y)ᶜ) q) :
    RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (Y × Y))
      ((S.preimage (continuous_fst : Continuous (Prod.fst : Y × Y → Y)) ⊓
        T.preimage (continuous_snd : Continuous (Prod.snd : Y × Y → Y)) :
        Closeds (Y × Y)) : Set (Y × Y))ᶜ) (p + q) :=
  ccm15_relativeCup (TopCat.of (Y × Y)) _ _ p q
    (relativeCohomologyMap ℚ p
      (ccm17_preimagePair (TopCat.of (Y × Y)) Y ⟨Prod.fst, continuous_fst⟩ S) u)
    (relativeCohomologyMap ℚ q
      (ccm17_preimagePair (TopCat.of (Y × Y)) Y ⟨Prod.snd, continuous_snd⟩ T) v)

/-- The diagonal maps the complement of the intersection to the complement of the product.
Source: the set-theoretic inverse image of a product under the diagonal. -/
def a3cc2_diagonalPair (Y : TopCat.{0}) (S T : Closeds Y) :
    TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ ⟶
      TopPair.ofSubset (X := TopCat.of (Y × Y))
        ((S.preimage (continuous_fst : Continuous (Prod.fst : Y × Y → Y)) ⊓
          T.preimage (continuous_snd : Continuous (Prod.snd : Y × Y → Y)) :
          Closeds (Y × Y)) : Set (Y × Y))ᶜ :=
  ccm17_preimagePair Y (TopCat.of (Y × Y))
    ⟨fun a => (a, a), continuous_id.prodMk continuous_id⟩
    (S.preimage continuous_fst ⊓ T.preimage continuous_snd)

/-- Pulling the relative exterior product back along the diagonal gives the relative cup.
Source: Hatcher, *Algebraic Topology*, §3.2, cross products and cup products. -/
theorem a3cc2_diagonal_relativeExternal (Y : TopCat.{0}) (S T : Closeds Y) (p q : ℕ)
    (u : RelativeCohomology ℚ (TopPair.ofSubset (S : Set Y)ᶜ) p)
    (v : RelativeCohomology ℚ (TopPair.ofSubset (T : Set Y)ᶜ) q) :
    relativeCohomologyMap ℚ (p + q) (a3cc2_diagonalPair Y S T)
      (a3cc2_relativeExternal Y S T p q u v) = ccm15_relativeCup Y S T p q u v := by
  unfold a3cc2_relativeExternal a3cc2_diagonalPair
  erw [ccm17_relativeCup_pullback]
  apply congrArg₂ (fun u v => ccm15_relativeCup Y S T p q u v)
  · erw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
    change relativeCohomologyMap ℚ p (𝟙 _) u = u
    rw [relativeCohomologyMap_id]
    rfl
  · erw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
    change relativeCohomologyMap ℚ q (𝟙 _) v = v
    rw [relativeCohomologyMap_id]
    rfl

/-- The supported cup is the diagonal pullback of the exterior product of its comparisons.
Source: products with supports and the diagonal formula for the relative cup. -/
theorem a3cc2_supportedCup_diagonal (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S T : Closeds (ComplexPoint X)) (p q : ℕ)
    (u : H_[S]^p(X; ℚ)) (v : H_[T]^q(X; ℚ)) :
    ccm16_supportedComparison X (S ⊓ T) (p + q) (ccm16_supportedCup X S T p q u v) =
      relativeCohomologyMap ℚ (p + q)
        (a3cc2_diagonalPair (TopCat.of (ComplexPoint X)) S T)
        (a3cc2_relativeExternal (TopCat.of (ComplexPoint X)) S T p q
          (ccm16_supportedComparison X S p u) (ccm16_supportedComparison X T q v)) := by
  rw [a3cc2_diagonal_relativeExternal]
  exact (ccm16_supportedComparison X (S ⊓ T) (p + q)).apply_symm_apply _

/-- The supported cup germ is computed by the diagonal exterior product on any neighborhood.
Source: relative cup naturality and `ccm17_supportedCup_germ`. -/
theorem a3cc2_supportedCup_diagonal_germ (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S T : Closeds (ComplexPoint X)) (U : Opens (ComplexPoint X))
    (p q : ℕ) (a : ComplexPoint X) (ha : a ∈ U)
    (u : H_[S]^p(X; ℚ)) (v : H_[T]^q(X; ℚ)) :
    ccm5_supportGerm X (S ⊓ T) (p + q) a (ccm16_supportedCup X S T p q u v) =
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      ((S ⊓ T : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) (p + q) U a ha
      (relativeCohomologyMap ℚ (p + q)
        (a3cc2_diagonalPair (TopCat.of U)
          (S.preimage continuous_subtype_val) (T.preimage continuous_subtype_val))
        (a3cc2_relativeExternal (TopCat.of U)
        (S.preimage continuous_subtype_val) (T.preimage continuous_subtype_val) p q
        (relativeCohomologyMap ℚ p
          (ccm17_preimagePair (TopCat.of U) (TopCat.of (ComplexPoint X))
            ⟨Subtype.val, continuous_subtype_val⟩ S)
          (ccm16_supportedComparison X S p u))
        (relativeCohomologyMap ℚ q
          (ccm17_preimagePair (TopCat.of U) (TopCat.of (ComplexPoint X))
            ⟨Subtype.val, continuous_subtype_val⟩ T)
          (ccm16_supportedComparison X T q v)))) := by
  rw [a3cc2_diagonal_relativeExternal]
  exact ccm17_supportedCup_germ X S T U p q a ha u v

#print axioms a3cc2_diagonalTor
#print axioms a3cc2_diagonalTor_length
#print axioms a3cc2_diagonalEuler
#print axioms a3cc2_diagonalEuler_eq
#print axioms a3cc2_serreMult_eq_diagonalEuler
#print axioms a3cc2_relativeExternal
#print axioms a3cc2_diagonalPair
#print axioms a3cc2_diagonal_relativeExternal
#print axioms a3cc2_supportedCup_diagonal
#print axioms a3cc2_supportedCup_diagonal_germ

end HodgeLean.Adapters
