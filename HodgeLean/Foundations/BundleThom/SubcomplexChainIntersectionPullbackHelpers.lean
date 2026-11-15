import HodgeLean.Foundations.BundleThom.PushoutMonoPullbackHelpers

/-! # Actual pullback squares of rational subcomplex chains

The ambient inclusion is monic, so the intersection computed in union chains is also the ambient intersection.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- Postcomposing an actual pullback cospan by a monomorphism retains its pullback square.
Source: Mac Lane, Categories for the Working Mathematician, III.4, pullback universal property. -/
theorem i1_isPullback_postcompose_mono {C : Type*} [Category* C]
    {A B D E F : C} {t : A ⟶ B} {l : A ⟶ D} {r : B ⟶ E} {b : D ⟶ E}
    (h : IsPullback t l r b) (j : E ⟶ F) [Mono j] : IsPullback t l (r ≫ j) (b ≫ j) := by
  have hw : t ≫ (r ≫ j) = l ≫ (b ≫ j) := by rw [← Category.assoc, h.w, Category.assoc]
  let w (s : PullbackCone (r ≫ j) (b ≫ j)) : s.fst ≫ r = s.snd ≫ b :=
    (cancel_mono j).mp (by simpa only [Category.assoc] using s.condition)
  apply IsPullback.of_isLimit' ⟨hw⟩
  refine PullbackCone.IsLimit.mk _ (fun s => h.lift s.fst s.snd (w s))
    (fun s => h.lift_fst _ _ _) (fun s => h.lift_snd _ _ _) ?_
  intro s m hm hn
  apply h.hom_ext
  · exact hm.trans (h.lift_fst _ _ _).symm
  · exact hn.trans (h.lift_snd _ _ _).symm

/-- A pullback cospan after common postcomposition detects the original commuting square's pullback property.
Source: Mac Lane, Categories for the Working Mathematician, III.4, pullback universal property. -/
theorem i1_isPullback_of_postcompose {C : Type*} [Category* C]
    {A B D E F : C} {t : A ⟶ B} {l : A ⟶ D} {r : B ⟶ E} {b : D ⟶ E}
    (sq : CommSq t l r b) (j : E ⟶ F) (h : IsPullback t l (r ≫ j) (b ≫ j)) :
    IsPullback t l r b := by
  let w (s : PullbackCone r b) : s.fst ≫ (r ≫ j) = s.snd ≫ (b ≫ j) := by
    rw [← Category.assoc, s.condition, Category.assoc]
  apply IsPullback.of_isLimit' sq
  refine PullbackCone.IsLimit.mk _ (fun s => h.lift s.fst s.snd (w s))
    (fun s => h.lift_fst _ _ _) (fun s => h.lift_snd _ _ _) ?_
  intro s m hm hn
  apply h.hom_ext
  · exact hm.trans (h.lift_fst _ _ _).symm
  · exact hn.trans (h.lift_snd _ _ _).symm

/-- Actual rational intersection chains form the pullback of the two ambient subcomplex inclusions.
Source: Hatcher, Algebraic Topology, §2.2, intersection chains in Mayer–Vietoris. -/
theorem i1_subcomplexChainIntersections_isPullback (X : SSet) (U V : X.Subcomplex) :
    IsPullback
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : U ⊓ V ≤ V)) (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap U.ι (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap V.ι (ModuleCat.of ℚ ℚ)) := by
  haveI : Mono (SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.of ℚ ℚ)) := by
    dsimp [SSet.chainComplexMap, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  haveI : Mono (SSet.chainComplexMap (U ⊔ V).ι (ModuleCat.of ℚ ℚ)) := by
    dsimp [SSet.chainComplexMap, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  have h := i1_isPullback_of_isPushout_of_mono (i1_subcomplexChains_isPushout X U V)
  have hc := i1_isPullback_postcompose_mono h (SSet.chainComplexMap (U ⊔ V).ι (ModuleCat.of ℚ ℚ))
  convert hc using 1 <;> rw [← Functor.map_comp] <;> rfl

end HodgeLean.Foundations.BundleThom
