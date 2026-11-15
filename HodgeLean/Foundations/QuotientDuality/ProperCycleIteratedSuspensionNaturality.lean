import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedBaseTransport

/-! # Naturality of actual composed signed support suspensions
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The composed actual signed support suspensions retain literal iterated base transport and its original relative homology map.
Source: properCycle_real_support_suspension_naturality; properCycle_iterated_real_point_complement_map.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_support_suspension_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (T : Set X) (U : Set Y)
    (h : Set.MapsTo f Tᶜ Uᶜ) (hT : IsClosed T) (hU : IsClosed U) (q n : ℕ) :
    HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
      (TopPair.ofSubsetHom (properCycle_iterated_real_base_map f n)
        (properCycle_iterated_real_point_complement_map f T U h n))) (q+n) ≫
      (properCycle_iterated_support_suspension_iso Y U hU q n).hom =
      (properCycle_iterated_support_suspension_iso X T hT q n).hom ≫
      HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f h)) q := by
  let B := HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f h)) q
  let M := fun n => HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
    (TopPair.ofSubsetHom (properCycle_iterated_real_base_map f n)
      (properCycle_iterated_real_point_complement_map f T U h n))) (q+n)
  induction n with
  | zero =>
    change B ≫ 𝟙 _ = 𝟙 _ ≫ B
    simp only [Category.comp_id, Category.id_comp]
  | succ n ih =>
    let fn := properCycle_iterated_real_base_map f n
    let Tn := properCycle_real_point_support X T n
    let Un := properCycle_real_point_support Y U n
    let hn := properCycle_iterated_real_point_complement_map f T U h n
    let hTn := properCycle_real_point_support_isClosed X T hT n
    let hUn := properCycle_real_point_support_isClosed Y U hU n
    let sX := properCycle_real_support_suspension_iso (properCycle_real_support_space X n) Tn hTn (q+n)
    let sY := properCycle_real_support_suspension_iso (properCycle_real_support_space Y n) Un hUn (q+n)
    let tX := properCycle_iterated_support_suspension_iso X T hT q n
    let tY := properCycle_iterated_support_suspension_iso Y U hU q n
    have hs := properCycle_real_support_suspension_naturality fn Tn Un hn hTn hUn (q+n)
    change M (n+1) ≫ sY.hom = sX.hom ≫ M n at hs
    change M n ≫ tY.hom = tX.hom ≫ B at ih
    change M (n+1) ≫ (sY.hom ≫ tY.hom) = (sX.hom ≫ tX.hom) ≫ B
    calc
      _ = (M (n+1) ≫ sY.hom) ≫ tY.hom := (Category.assoc _ _ _).symm
      _ = (sX.hom ≫ M n) ≫ tY.hom := by rw [hs]
      _ = sX.hom ≫ (M n ≫ tY.hom) := Category.assoc _ _ _
      _ = sX.hom ≫ (tX.hom ≫ B) := by rw [ih]
      _ = _ := (Category.assoc _ _ _).symm

/-- Every actual composed support suspension retains the exact specified standard local coefficient under literal iterated base transport.
Source: properCycle_iterated_support_suspension_naturality; properCycle_iterated_support_suspension_local_class.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_support_suspension_standard_map
    (Y : TopCat.{0}) (d : ℕ) (f : TopCat.of (Fin d → ℂ) ⟶ Y)
    (T : Set Y) (h : Set.MapsTo f ({0} : Set (Fin d → ℂ))ᶜ Tᶜ)
    (hT : IsClosed T) (n : ℕ) :
    (properCycle_iterated_support_suspension_iso Y T hT (d*2) n).hom.hom
      (relativeHomologyMap ℚ (d*2+n)
        (TopPair.ofSubsetHom (properCycle_iterated_real_base_map f n)
          (properCycle_iterated_real_point_complement_map f {0} T h n))
        (properCycle_iterated_real_local_class d n)) =
      (-1 : ℚ)^n • relativeHomologyMap ℚ (d*2) (TopPair.ofSubsetHom f h)
        (standardComplexLocalClassMul d) := by
  have he := ConcreteCategory.congr_hom
    (properCycle_iterated_support_suspension_naturality f {0} T h isClosed_singleton hT (d*2) n)
    (properCycle_iterated_real_local_class d n)
  change (properCycle_iterated_support_suspension_iso Y T hT (d*2) n).hom.hom
      (relativeHomologyMap ℚ (d*2+n)
        (TopPair.ofSubsetHom (properCycle_iterated_real_base_map f n)
          (properCycle_iterated_real_point_complement_map f {0} T h n))
        (properCycle_iterated_real_local_class d n)) =
    relativeHomologyMap ℚ (d*2) (TopPair.ofSubsetHom f h)
      ((properCycle_iterated_support_suspension_iso (TopCat.of (Fin d → ℂ)) {0}
        isClosed_singleton (d*2) n).hom.hom (properCycle_iterated_real_local_class d n)) at he
  rw [properCycle_iterated_support_suspension_local_class, map_smul] at he
  exact he

end HodgeLean.Foundations.QuotientDuality
