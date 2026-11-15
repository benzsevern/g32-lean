import HodgeLean.Foundations.BundleThom.ChainDualAdditivityHelpers
import HodgeLean.Foundations.BundleThom.ChainCoclassUniquenessHelpers

/-! # Actual binary coclass detection from lower intersection vanishing -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace HodgeLean.Foundations.BundleThom

/-- The actual two biproduct inclusions jointly detect rational dual coclasses.
Source: Hatcher, Algebraic Topology, §3.1, additivity of rational cohomology. -/
theorem i1_chainDualPullback_biprod_ext {B C : ChainComplex (ModuleCat ℚ) ℕ}
    (n : ℕ) (u v : (B ⊞ C).linearDualCochainComplex.homology n)
    (hl : i1_chainDualPullback n (biprod.inl : B ⟶ B ⊞ C) u =
      i1_chainDualPullback n biprod.inl v)
    (hr : i1_chainDualPullback n (biprod.inr : C ⟶ B ⊞ C) u =
      i1_chainDualPullback n biprod.inr v) : u = v := by
  have hs (w : (B ⊞ C).linearDualCochainComplex.homology n) :
      w = i1_chainDualPullback n biprod.fst (i1_chainDualPullback n biprod.inl w) +
        i1_chainDualPullback n biprod.snd (i1_chainDualPullback n biprod.inr w) := by
    have ht := congrArg (fun f : B ⊞ C ⟶ B ⊞ C => i1_chainDualPullback n f w)
      (biprod.total (X := B) (Y := C))
    rw [i1_chainDualPullback_add, LinearMap.add_apply,
      i1_chainDualPullback_comp, LinearMap.comp_apply,
      i1_chainDualPullback_comp, LinearMap.comp_apply,
      i1_chainDualPullback_id, LinearMap.id_apply] at ht
    exact ht.symm
  rw [hs u, hl, hr, ← hs v]

/-- In an actual monic chain pushout, lower intersection homology vanishing makes the two domain pullbacks jointly injective.
Source: Hatcher, Algebraic Topology, §3.1, Mayer–Vietoris uniqueness. -/
theorem i1_binaryChainCoclass_ext
    {A B C D : ChainComplex (ModuleCat ℚ) ℕ}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (h : IsPushout t l r b) [Mono t] (n : ℕ) (hzero : IsZero (A.homology n))
    (u v : D.linearDualCochainComplex.homology (n + 1))
    (hr : i1_chainDualPullback (n + 1) r u = i1_chainDualPullback (n + 1) r v)
    (hb : i1_chainDualPullback (n + 1) b u = i1_chainDualPullback (n + 1) b v) : u = v := by
  haveI : Mono h.shortComplex.f := by
    change Mono (biprod.lift t (-l))
    infer_instance
  have hS : h.shortComplex.ShortExact := {
    exact := h.exact_shortComplex
    mono_f := inferInstance
    epi_g := h.epi_shortComplex_g }
  apply i1_chainDualPullback_shortExact_injective h.shortComplex hS n hzero
  apply i1_chainDualPullback_biprod_ext
  · change i1_chainDualPullback (n + 1) biprod.inl
      (i1_chainDualPullback (n + 1) (biprod.desc r b) u) =
      i1_chainDualPullback (n + 1) biprod.inl
      (i1_chainDualPullback (n + 1) (biprod.desc r b) v)
    rw [← LinearMap.comp_apply, ← i1_chainDualPullback_comp, biprod.inl_desc,
      ← LinearMap.comp_apply, ← i1_chainDualPullback_comp, biprod.inl_desc]
    exact hr
  · change i1_chainDualPullback (n + 1) biprod.inr
      (i1_chainDualPullback (n + 1) (biprod.desc r b) u) =
      i1_chainDualPullback (n + 1) biprod.inr
      (i1_chainDualPullback (n + 1) (biprod.desc r b) v)
    rw [← LinearMap.comp_apply, ← i1_chainDualPullback_comp, biprod.inr_desc,
      ← LinearMap.comp_apply, ← i1_chainDualPullback_comp, biprod.inr_desc]
    exact hb

end HodgeLean.Foundations.BundleThom
