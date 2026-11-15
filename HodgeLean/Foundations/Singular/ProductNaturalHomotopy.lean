import HodgeLean.Foundations.Singular.ProductHomotopyRecursion

/-! Chain homotopies between actual natural product-chain endomaps equal on vertices. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Singular

/-- Two natural product-chain-chain endomaps equal on vertices are chain homotopic.
Source: Hatcher, Algebraic Topology, §3.2, uniqueness in the acyclic-models comparison. -/
def productNaturalChainHomotopy
    (F G : ∀ X Y : TopCat.{0}, rationalProductChains X Y ⟶ rationalProductChains X Y)
    (hF : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalProductChainMap f g ≫ F X' Y' = F X Y ≫ rationalProductChainMap f g)
    (hG : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalProductChainMap f g ≫ G X' Y' = G X Y ≫ rationalProductChainMap f g)
    (h₀ : ∀ X Y : TopCat.{0}, (F X Y).f 0 = (G X Y).f 0) (X Y : TopCat.{0}) :
    Homotopy (F X Y) (G X Y) where
  hom i j := if h : i + 1 = j then by
    subst j
    exact ModuleCat.ofHom ((productHomotopyStages F G hF hG h₀ i).hom X Y)
    else 0
  zero i j hij := by
    rw [dif_neg]
    simpa using hij
  comm i := by
    cases i with
    | zero =>
      rw [dNext_eq_zero _ 0 (by simp),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 by simp)]
      simp only [dif_pos rfl]
      change (F X Y).f 0 = 0 + (0 : (rationalProductChains X Y).X 0 ⟶ _) ≫
        (rationalProductChains X Y).d 1 0 + (G X Y).f 0
      simpa only [zero_comp, zero_add] using h₀ X Y
    | succ n =>
      rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n by simp),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) by simp)]
      erw [dif_pos rfl, dif_pos rfl]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      have hb := LinearMap.congr_fun
        ((productHomotopyStages F G hF hG h₀ n).nextHom_boundary hF hG X Y) z
      change ((rationalProductChains X Y).d (n + 2) (n + 1)).hom
          ((productHomotopyStages F G hF hG h₀ (n + 1)).hom X Y z) =
        ((F X Y).f (n + 1)).hom z - ((G X Y).f (n + 1)).hom z -
          (productHomotopyStages F G hF hG h₀ n).hom X Y
            (((rationalProductChains X Y).d (n + 1) n).hom z) at hb
      change ((F X Y).f (n + 1)).hom z =
        (productHomotopyStages F G hF hG h₀ n).hom X Y
          (((rationalProductChains X Y).d (n + 1) n).hom z) +
        ((rationalProductChains X Y).d (n + 2) (n + 1)).hom
          ((productHomotopyStages F G hF hG h₀ (n + 1)).hom X Y z) +
        ((G X Y).f (n + 1)).hom z
      rw [hb]
      abel

#print axioms productNaturalChainHomotopy
end HodgeLean.Foundations.Singular
