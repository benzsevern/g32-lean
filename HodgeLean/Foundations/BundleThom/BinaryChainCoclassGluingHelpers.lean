import HodgeLean.Foundations.BundleThom.ChainDualPullbackHelpers

/-! # Gluing the two individual rational coclasses across an actual chain pushout

Equality of intersection pullbacks gives a coclass on the union with both supplied restrictions.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace HodgeLean.Foundations.BundleThom

/-- Actual compatible rational coclasses on the two legs of a monic chain pushout extend to its union.
Source: Hatcher, Algebraic Topology, §3.1, Mayer–Vietoris cohomology gluing. -/
theorem i1_binaryChainCoclass_gluing
    {A B C D : ChainComplex (ModuleCat ℚ) ℕ}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (h : IsPushout t l r b) [Mono t] (n : ℕ)
    (u : B.linearDualCochainComplex.homology n) (v : C.linearDualCochainComplex.homology n)
    (huv : i1_chainDualPullback n t u = i1_chainDualPullback n l v) :
    ∃ z : D.linearDualCochainComplex.homology n,
      i1_chainDualPullback n r z = u ∧ i1_chainDualPullback n b z = v := by
  haveI : Mono h.shortComplex.f := by
    change Mono (biprod.lift t (-l))
    infer_instance
  have hS : h.shortComplex.ShortExact := {
    exact := h.exact_shortComplex
    mono_f := inferInstance
    epi_g := h.epi_shortComplex_g }
  let w := i1_chainDualPullback n (biprod.fst : B ⊞ C ⟶ B) u +
    i1_chainDualPullback n (biprod.snd : B ⊞ C ⟶ C) v
  have hw : HomologicalComplex.homologyMap
      (HomologicalComplex.linearDualMap h.shortComplex.f) n w = 0 := by
    change i1_chainDualPullback n (biprod.lift t (-l))
      (i1_chainDualPullback n biprod.fst u + i1_chainDualPullback n biprod.snd v) = 0
    rw [map_add, ← LinearMap.comp_apply, ← i1_chainDualPullback_comp, biprod.lift_fst,
      ← LinearMap.comp_apply, ← i1_chainDualPullback_comp, biprod.lift_snd,
      i1_chainDualPullback_neg, LinearMap.neg_apply, huv, add_neg_cancel]
  obtain ⟨z, hz⟩ := i1_rationalChainCoclass_gluing h.shortComplex hS n w hw
  change i1_chainDualPullback n (biprod.desc r b) z = w at hz
  refine ⟨z, ?_, ?_⟩
  · have hz₁ := congrArg (i1_chainDualPullback n (biprod.inl : B ⟶ B ⊞ C)) hz
    change i1_chainDualPullback n biprod.inl (i1_chainDualPullback n (biprod.desc r b) z) =
      i1_chainDualPullback n biprod.inl
        (i1_chainDualPullback n biprod.fst u + i1_chainDualPullback n biprod.snd v) at hz₁
    rw [← LinearMap.comp_apply, ← i1_chainDualPullback_comp, biprod.inl_desc, map_add,
      ← LinearMap.comp_apply, ← i1_chainDualPullback_comp, biprod.inl_fst,
      i1_chainDualPullback_id, LinearMap.id_apply,
      ← LinearMap.comp_apply, ← i1_chainDualPullback_comp, biprod.inl_snd,
      i1_chainDualPullback_zero, LinearMap.zero_apply, add_zero] at hz₁
    exact hz₁
  · have hz₂ := congrArg (i1_chainDualPullback n (biprod.inr : C ⟶ B ⊞ C)) hz
    change i1_chainDualPullback n biprod.inr (i1_chainDualPullback n (biprod.desc r b) z) =
      i1_chainDualPullback n biprod.inr
        (i1_chainDualPullback n biprod.fst u + i1_chainDualPullback n biprod.snd v) at hz₂
    rw [← LinearMap.comp_apply, ← i1_chainDualPullback_comp, biprod.inr_desc, map_add,
      ← LinearMap.comp_apply, ← i1_chainDualPullback_comp, biprod.inr_fst,
      i1_chainDualPullback_zero, LinearMap.zero_apply,
      ← LinearMap.comp_apply, ← i1_chainDualPullback_comp, biprod.inr_snd,
      i1_chainDualPullback_id, LinearMap.id_apply, zero_add] at hz₂
    exact hz₂

end HodgeLean.Foundations.BundleThom
