import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-! Compact graph relations with unique fibers determine actual continuous sections. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_compact_graph_section {E : Type*} [TopologicalSpace E] [T2Space E]
    (A : Set E) (R : Set (E × ℝ)) (hR : IsCompact R)
    (hproj : Prod.fst '' R = A)
    (hunique : ∀ a ∈ A, Set.Subsingleton {t : ℝ | (a, t) ∈ R}) :
    ∃ g : A → ℝ, Continuous g ∧ ∀ a : A, ∀ t : ℝ, (a.val, t) ∈ R ↔ t = g a := by
  have hbase : ∀ p : R, p.val.1 ∈ A := fun p => hproj ▸ ⟨p.val, p.property, rfl⟩
  let φ : R → A := fun p => ⟨p.val.1, hbase p⟩
  have hinj : Function.Injective φ := by
    intro p q hpq
    have he : p.val.1 = q.val.1 := congrArg Subtype.val hpq
    apply Subtype.ext
    apply Prod.ext he
    apply hunique p.val.1 (hbase p) p.property
    exact he.symm ▸ q.property
  have hsurj : Function.Surjective φ := by
    intro a
    have ha : a.val ∈ Prod.fst '' R := hproj.symm ▸ a.property
    obtain ⟨p, hp, hpa⟩ := ha
    exact ⟨⟨p, hp⟩, Subtype.ext hpa⟩
  letI : CompactSpace R := isCompact_iff_compactSpace.mp hR
  let e₀ := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  have he₀ : Continuous e₀ := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  let e : R ≃ₜ A := he₀.homeoOfEquivCompactToT2
  let g : A → ℝ := fun a => (e.symm a).val.2
  have hfst : ∀ a : A, (e.symm a).val.1 = a.val := fun a =>
    congrArg Subtype.val (e.apply_symm_apply a)
  refine ⟨g, continuous_snd.comp (continuous_subtype_val.comp e.symm.continuous), ?_⟩
  intro a t
  constructor
  · intro hat
    let p : R := ⟨(a.val, t), hat⟩
    have hep : e p = a := Subtype.ext rfl
    have hpa : e.symm a = p := (congrArg e.symm hep.symm).trans (e.symm_apply_apply p)
    exact (congrArg (fun p : R => p.val.2) hpa).symm
  · rintro rfl
    have hp : (a.val, g a) = (e.symm a).val := Prod.ext (hfst a).symm rfl
    exact hp.symm ▸ (e.symm a).property

end HodgeLean.Foundations.Program
