import HodgeLean.Foundations.BundleThom.SubcomplexMayerVietorisHelpers

/-! # Pullbacks from actual abelian pushouts of monomorphisms

The short exact difference–sum sequence supplies the actual pullback lift.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace HodgeLean.Foundations.BundleThom

/-- An actual pushout square in an abelian category is a pullback when its top map is monic.
Source: Mac Lane, Categories for the Working Mathematician, VIII.2, abelian squares. -/
theorem i1_isPullback_of_isPushout_of_mono
    {C : Type*} [Category* C] [Abelian C]
    {A B D E : C} {t : A ⟶ B} {l : A ⟶ D} {r : B ⟶ E} {b : D ⟶ E}
    (h : IsPushout t l r b) [Mono t] : IsPullback t l r b := by
  haveI : Mono h.shortComplex.f := by
    change Mono (biprod.lift t (-l))
    infer_instance
  have hS : h.shortComplex.ShortExact := {
    exact := h.exact_shortComplex
    mono_f := inferInstance
    epi_g := h.epi_shortComplex_g }
  let K := hS.fIsKernel
  let L (s : PullbackCone r b) := KernelFork.IsLimit.lift' K (biprod.lift s.fst (-s.snd)) (by
    change biprod.lift s.fst (-s.snd) ≫ biprod.desc r b = 0
    simp only [biprod.lift_desc, Preadditive.neg_comp, s.condition, add_neg_cancel])
  have hfst (s : PullbackCone r b) : (L s).1 ≫ t = s.fst := by
    have hh := congrArg (fun f => f ≫ biprod.fst) (L s).2
    simpa only [Category.assoc, KernelFork.ι_ofι, CommSq.shortComplex_f, biprod.lift_fst] using hh
  have hsnd (s : PullbackCone r b) : (L s).1 ≫ l = s.snd := by
    have hh := congrArg (fun f => f ≫ biprod.snd) (L s).2
    have hn : -((L s).1 ≫ l) = -s.snd := by
      simpa only [Category.assoc, KernelFork.ι_ofι, CommSq.shortComplex_f, biprod.lift_snd, Preadditive.comp_neg] using hh
    exact neg_injective hn
  apply IsPullback.of_isLimit' h.toCommSq
  refine PullbackCone.IsLimit.mk _ (fun s => (L s).1) hfst hsnd ?_
  intro s m hm hn
  apply (cancel_mono t).mp
  exact hm.trans (hfst s).symm

end HodgeLean.Foundations.BundleThom
