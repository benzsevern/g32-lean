import Mathlib.Topology.Homeomorph.Lemmas
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBandInterpolation
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact

/-! Quotient parametrizations of compact bands with collapsing fibers. -/
noncomputable section
namespace HodgeLean.Foundations.Program
open Topology

theorem s2v_hardt6rb_band_quotient {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (a b : X → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ x, a x ≤ b x) :
    ∃ p : X × Set.Icc (0 : ℝ) 1 →
        {z : X × ℝ | z.2 ∈ Set.Icc (a z.1) (b z.1)},
      IsQuotientMap p ∧
      (∀ z, (p z).val = (z.1, (1 - z.2.val) * a z.1 + z.2.val * b z.1)) ∧
      (∀ z w, p z = p w ↔ z.1 = w.1 ∧ (z.2 = w.2 ∨ a z.1 = b z.1)) := by
  let p : X × Set.Icc (0 : ℝ) 1 →
      {z : X × ℝ | z.2 ∈ Set.Icc (a z.1) (b z.1)} := fun z =>
    ⟨(z.1, (1 - z.2.val) * a z.1 + z.2.val * b z.1),
      s2v_hardt6rb_band_interpolation_mem (hab z.1) z.2.property⟩
  have hp : Continuous p := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk
      (((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
        (ha.comp continuous_fst)).add
        ((continuous_subtype_val.comp continuous_snd).mul (hb.comp continuous_fst)))
  have hs : Function.Surjective p := by
    intro y
    obtain ⟨t, ht, he⟩ := s2v_hardt6rb_band_interpolation_surjective (hab y.val.1) y.property
    refine ⟨(y.val.1, ⟨t, ht⟩), ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl he
  refine ⟨p, hp.isClosedMap.isQuotientMap hp hs, fun _ => rfl, ?_⟩
  intro z w
  change (⟨(z.1, (1 - z.2.val) * a z.1 + z.2.val * b z.1), _⟩ :
    {z : X × ℝ | z.2 ∈ Set.Icc (a z.1) (b z.1)}) =
    ⟨(w.1, (1 - w.2.val) * a w.1 + w.2.val * b w.1), _⟩ ↔ _
  rw [Subtype.ext_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨hx, ?_⟩
    rw [← hx] at hy
    rcases (s2v_hardt6rb_band_interpolation_eq_iff _ _ _ _).mp hy with ht | hab'
    · exact Or.inl (Subtype.ext ht)
    · exact Or.inr hab'
  · rintro ⟨hx, ht⟩
    refine ⟨hx, ?_⟩
    rw [← hx]
    apply (s2v_hardt6rb_band_interpolation_eq_iff _ _ _ _).mpr
    exact ht.imp (fun h => congrArg Subtype.val h) id

end HodgeLean.Foundations.Program
