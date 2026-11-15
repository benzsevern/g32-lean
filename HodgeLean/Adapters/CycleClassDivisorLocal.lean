import HodgeLean.Adapters.CycleClassDivisorLocalProofs

/-! # Local complex orientation products: frozen primitives
The coordinate product has coefficient +1 relative to the fixed complex orientation.
Pullback compatibility gives an implication from continuous chart maps to local products.
Identification with global prime-cycle germs remains separate geometric work.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Adapters

/-- The coordinate divisor and complementary coordinate plane multiply to the
independently normalized intersection class, with coefficient +1.
Source: Bott–Tu, §6, Thom classes of direct sums; Bredon, Sheaf Theory, V,
orientation and duality; Griffiths–Harris, chapter 0 §4, complex orientation. -/
theorem ccm17_coordinate_product (q : ℕ) :
    ccm15_relativeCup (TopCat.of (Fin (q + 1) → ℂ))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q)) 2 (2 * q)
      (ccm17_normalClass (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
      (ccm17_normalClass (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q)) = ccm17_intersectionClass q :=
  ccm17_coordinate_product_aux q

/-- Pullback carries the actual relative product to the product on inverse-image supports.
Source: Hatcher, Algebraic Topology, §3.2, relative cup naturality;
Bredon, Sheaf Theory, V, products with supports. -/
theorem ccm17_relativeCup_pullback (Y Z : TopCat.{0}) (f : C(Y, Z))
    (S T : Closeds Z) (p q : ℕ)
    (u : RelativeCohomology ℚ (TopPair.ofSubset (S : Set Z)ᶜ) p)
    (v : RelativeCohomology ℚ (TopPair.ofSubset (T : Set Z)ᶜ) q) :
    relativeCohomologyMap ℚ (p + q) (ccm17_preimagePair Y Z f (S ⊓ T))
      (ccm15_relativeCup Z S T p q u v) =
    ccm15_relativeCup Y (S.preimage f.continuous) (T.preimage f.continuous) p q
      (relativeCohomologyMap ℚ p (ccm17_preimagePair Y Z f S) u)
      (relativeCohomologyMap ℚ q (ccm17_preimagePair Y Z f T) v) :=
  ccm17_relativeCup_pullback_aux Y Z f S T p q u v

/-- Two transverse complex axes, with both normal dimensions positive.
Source: the coordinate product with q = 1. -/
example : ccm15_relativeCup (TopCat.of (Fin 2 → ℂ))
    (ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_head 1))
    (ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_tail 1)) 2 2
    (ccm17_normalClass (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_head 1))
    (ccm17_normalClass (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_tail 1)) = ccm17_intersectionClass 1 :=
  ccm17_coordinate_product 1

/-- Pullback to a three-dimensional chart by forgetting the last coordinate.
Source: relative cup naturality on a concrete projection. -/
example :
    relativeCohomologyMap ℚ (2 + 2) (ccm17_preimagePair (TopCat.of (Fin 3 → ℂ)) (TopCat.of (Fin 2 → ℂ)) (⟨fun z i => z i.castSucc, by fun_prop⟩ : C(Fin 3 → ℂ, Fin 2 → ℂ)) ((ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_head 1)) ⊓ (ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_tail 1))))
      (ccm15_relativeCup (TopCat.of (Fin 2 → ℂ)) (ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_head 1)) (ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_tail 1)) 2 2 (ccm17_normalClass (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_head 1)) (ccm17_normalClass (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_tail 1))) =
    ccm15_relativeCup (TopCat.of (Fin 3 → ℂ)) ((ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_head 1)).preimage (⟨fun z i => z i.castSucc, by fun_prop⟩ : C(Fin 3 → ℂ, Fin 2 → ℂ)).continuous) ((ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_tail 1)).preimage (⟨fun z i => z i.castSucc, by fun_prop⟩ : C(Fin 3 → ℂ, Fin 2 → ℂ)).continuous) 2 2
      (relativeCohomologyMap ℚ 2 (ccm17_preimagePair (TopCat.of (Fin 3 → ℂ)) (TopCat.of (Fin 2 → ℂ)) (⟨fun z i => z i.castSucc, by fun_prop⟩ : C(Fin 3 → ℂ, Fin 2 → ℂ)) (ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_head 1))) (ccm17_normalClass (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_head 1)))
      (relativeCohomologyMap ℚ 2 (ccm17_preimagePair (TopCat.of (Fin 3 → ℂ)) (TopCat.of (Fin 2 → ℂ)) (⟨fun z i => z i.castSucc, by fun_prop⟩ : C(Fin 3 → ℂ, Fin 2 → ℂ)) (ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_tail 1))) (ccm17_normalClass (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_tail 1))) :=
  ccm17_relativeCup_pullback (TopCat.of (Fin 3 → ℂ))
    (TopCat.of (Fin 2 → ℂ))
    (⟨fun z i => z i.castSucc, by fun_prop⟩ : C(Fin 3 → ℂ, Fin 2 → ℂ))
    (ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_head 1))
    (ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_tail 1))
    2
    2
    (ccm17_normalClass (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_head 1))
    (ccm17_normalClass (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_tail 1))

end HodgeLean.Adapters
