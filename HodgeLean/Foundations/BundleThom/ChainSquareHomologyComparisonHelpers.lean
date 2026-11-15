import HodgeLean.Foundations.BundleThom.BiproductQuasiIsoHelpers

/-! # Homology comparison along a chain-square augmentation

HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits HomologicalComplex
namespace HodgeLean.Foundations.BundleThom

/-- An augmented intersection–union sequence detects the base homology when its middle domains are equivalent and the intersection has the required adjacent-degree maps.
Source: Hatcher, Algebraic Topology, §2.2, naturality and the five lemma for Mayer–Vietoris. -/
theorem i1_chainSquareAugmentation_homology_isIso
    {A B C D T : ChainComplex (ModuleCat ℚ) ℕ}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (sq : CommSq f g i j) (hs : sq.shortComplex.ShortExact)
    (pA : A ⟶ T) (pB : B ⟶ T) (pC : C ⟶ T) (pD : D ⟶ T)
    (hAB : f ≫ pB = pA) (hAC : g ≫ pC = pA)
    (hBD : i ≫ pD = pB) (hCD : j ≫ pD = pC)
    [QuasiIso pB] [QuasiIso pC] (n : ℕ)
    (ha : Epi (homologyMap pA n))
    (hl : ∀ m, (ComplexShape.down ℕ).Rel n m → IsIso (homologyMap pA m)) :
    IsIso (homologyMap pD n) := by
  let φ := i1_chainSquareAugmentation sq pA pB pC pD hAB hAC hBD hCD
  haveI : QuasiIso (biprod.map pB pC) := i1_biprodMap_quasiIso pB pC
  exact HomologySequence.isIso_homologyMap_τ₃ φ hs
    (i1_constantChainSquare_shortExact T) n ha
    (by change IsIso (homologyMap (biprod.map pB pC) n); infer_instance)
    hl (fun m _ => by
      change Mono (homologyMap (biprod.map pB pC) m)
      infer_instance)

end HodgeLean.Foundations.BundleThom
