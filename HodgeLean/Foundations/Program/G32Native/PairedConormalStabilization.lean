import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic

/-! # Simultaneous stabilization of two quotients with the same target -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program.G32Native

/-- Two short exact sequences with a common quotient give two short exact
sequences on the same pullback, retaining both original kernel injections. -/
theorem paired_quotient_stabilization
    {C : Type*} [Category* C] [Abelian C]
    {A M I F T : C} (f : A ⟶ M) (g : M ⟶ T) (i : I ⟶ F) (q : F ⟶ T)
    (hfg : f ≫ g = 0) (hiq : i ≫ q = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    (hT : (ShortComplex.mk i q hiq).ShortExact) :
    ∃ (a : A ⟶ pullback g q) (b : I ⟶ pullback g q)
      (ha : a ≫ pullback.snd g q = 0) (hb : b ≫ pullback.fst g q = 0),
      a ≫ pullback.fst g q = f ∧ b ≫ pullback.snd g q = i ∧
      (ShortComplex.mk a (pullback.snd g q) ha).ShortExact ∧
      (ShortComplex.mk b (pullback.fst g q) hb).ShortExact := by
  letI : Mono f := hS.mono_f
  letI : Epi g := hS.epi_g
  letI : Mono i := hT.mono_f
  letI : Epi q := hT.epi_g
  let a : A ⟶ pullback g q := pullback.lift f 0 (by rw [hfg, zero_comp])
  let b : I ⟶ pullback g q := pullback.lift 0 i (by rw [hiq, zero_comp])
  have haf : a ≫ pullback.fst g q = f := pullback.lift_fst _ _ _
  have hbi : b ≫ pullback.snd g q = i := pullback.lift_snd _ _ _
  have ha : a ≫ pullback.snd g q = 0 := pullback.lift_snd _ _ _
  have hb : b ≫ pullback.fst g q = 0 := pullback.lift_fst _ _ _
  haveI : Mono (a ≫ pullback.fst g q) := by rw [haf]; infer_instance
  haveI : Mono a := mono_of_mono a (pullback.fst g q)
  haveI : Mono (b ≫ pullback.snd g q) := by rw [hbi]; infer_instance
  haveI : Mono b := mono_of_mono b (pullback.snd g q)
  have hka : IsLimit (KernelFork.ofι a ha) := by
    apply KernelFork.IsLimit.ofι'
    intro Z k hk
    have hkg : (k ≫ pullback.fst g q) ≫ g = 0 := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hk, zero_comp]
    refine ⟨hS.exact.lift (k ≫ pullback.fst g q) hkg, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, haf, hS.exact.lift_f]
    · rw [Category.assoc, ha, comp_zero, hk]
  have hkb : IsLimit (KernelFork.ofι b hb) := by
    apply KernelFork.IsLimit.ofι'
    intro Z k hk
    have hkq : (k ≫ pullback.snd g q) ≫ q = 0 := by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hk, zero_comp]
    refine ⟨hT.exact.lift (k ≫ pullback.snd g q) hkq, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hb, comp_zero, hk]
    · rw [Category.assoc, hbi, hT.exact.lift_f]
  exact ⟨a, b, ha, hb, haf, hbi,
    ⟨(ShortComplex.mk a (pullback.snd g q) ha).exact_of_f_is_kernel hka⟩,
    ⟨(ShortComplex.mk b (pullback.fst g q) hb).exact_of_f_is_kernel hkb⟩⟩

end HodgeLean.Foundations.Program.G32Native
