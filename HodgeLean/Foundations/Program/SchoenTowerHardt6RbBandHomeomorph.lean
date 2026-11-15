import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBandQuotient
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Quotient

/-! Fresh band parametrizations respecting coincident boundary sections. -/
noncomputable section
namespace HodgeLean.Foundations.Program
open Topology

theorem s2v_hardt6rb_band_homeomorph {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (a b c d : X → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d)
    (hab : ∀ x, a x ≤ b x) (hcd : ∀ x, c x ≤ d x)
    (hzero : ∀ x, a x = b x ↔ c x = d x) :
    ∃ h : {z : X × ℝ | z.2 ∈ Set.Icc (a z.1) (b z.1)} ≃ₜ
        {z : X × ℝ | z.2 ∈ Set.Icc (c z.1) (d z.1)},
      ∀ x (t : Set.Icc (0 : ℝ) 1),
        (h ⟨(x, (1 - t.val) * a x + t.val * b x),
          s2v_hardt6rb_band_interpolation_mem (hab x) t.property⟩).val =
            (x, (1 - t.val) * c x + t.val * d x) := by
  obtain ⟨p, hp, hpf, hpk⟩ := s2v_hardt6rb_band_quotient a b ha hb hab
  obtain ⟨q, hq, hqf, hqk⟩ := s2v_hardt6rb_band_quotient c d hc hd hcd
  let pc : C(X × Set.Icc (0 : ℝ) 1,
      {z : X × ℝ | z.2 ∈ Set.Icc (a z.1) (b z.1)}) := ⟨p, hp.continuous⟩
  let qc : C(X × Set.Icc (0 : ℝ) 1,
      {z : X × ℝ | z.2 ∈ Set.Icc (c z.1) (d z.1)}) := ⟨q, hq.continuous⟩
  have hpc : IsQuotientMap pc := hp
  have hqc : IsQuotientMap qc := hq
  have hker : ∀ z w, Setoid.ker pc z w ↔ Setoid.ker qc z w := by
    intro z w
    change p z = p w ↔ q z = q w
    rw [hpk, hqk, hzero]
  let e := Homeomorph.Quotient.congrRight hker
  let h := (hpc.homeomorph.symm.trans e).trans hqc.homeomorph
  have hh (z : X × Set.Icc (0 : ℝ) 1) : h (p z) = q z := by
    have hpz : hpc.homeomorph (Quotient.mk _ z) = p z := rfl
    rw [← hpz]
    simp only [h, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    rfl
  refine ⟨h, ?_⟩
  intro x t
  have hpxt : p (x, t) = ⟨(x, (1 - t.val) * a x + t.val * b x),
      s2v_hardt6rb_band_interpolation_mem (hab x) t.property⟩ :=
    Subtype.ext (hpf (x, t))
  rw [← hpxt, hh]
  exact hqf (x, t)

end HodgeLean.Foundations.Program
