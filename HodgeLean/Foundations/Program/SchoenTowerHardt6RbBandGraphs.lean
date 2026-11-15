import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBandHomeomorph

/-! An equation for the actual band homeomorphism, valid at collapsed fibers. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_band_homeomorph_graph {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (a b c d : X → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d)
    (hab : ∀ x, a x ≤ b x) (hcd : ∀ x, c x ≤ d x)
    (hzero : ∀ x, a x = b x ↔ c x = d x) :
    ∃ h : {z : X × ℝ | z.2 ∈ Set.Icc (a z.1) (b z.1)} ≃ₜ
        {z : X × ℝ | z.2 ∈ Set.Icc (c z.1) (d z.1)},
      ∀ x y v (hy : y ∈ Set.Icc (a x) (b x)) (hv : v ∈ Set.Icc (c x) (d x)),
        h ⟨(x, y), hy⟩ = ⟨(x, v), hv⟩ ↔
          (y - a x) * (d x - c x) = (v - c x) * (b x - a x) := by
  obtain ⟨h, hh⟩ := s2v_hardt6rb_band_homeomorph a b c d ha hb hc hd hab hcd hzero
  refine ⟨h, ?_⟩
  intro x y v hy hv
  rw [s2v_hardt6rb_band_interpolation_cross_iff (hab x) (hcd x) (hzero x) hy hv]
  constructor
  · intro he
    obtain ⟨t, ht, hty⟩ := s2v_hardt6rb_band_interpolation_surjective (hab x) hy
    refine ⟨t, ht, hty, ?_⟩
    have hcoord := hh x ⟨t, ht⟩
    have hin : (⟨(x, (1 - t) * a x + t * b x),
        s2v_hardt6rb_band_interpolation_mem (hab x) ht⟩ :
        {z : X × ℝ | z.2 ∈ Set.Icc (a z.1) (b z.1)}) = ⟨(x, y), hy⟩ :=
      Subtype.ext (Prod.ext rfl hty)
    rw [hin, he] at hcoord
    exact (congrArg Prod.snd hcoord).symm
  · rintro ⟨t, ht, hty, htv⟩
    apply Subtype.ext
    have hcoord := hh x ⟨t, ht⟩
    have hin : (⟨(x, (1 - t) * a x + t * b x),
        s2v_hardt6rb_band_interpolation_mem (hab x) ht⟩ :
        {z : X × ℝ | z.2 ∈ Set.Icc (a z.1) (b z.1)}) = ⟨(x, y), hy⟩ :=
      Subtype.ext (Prod.ext rfl hty)
    rw [hin] at hcoord
    exact hcoord.trans (Prod.ext rfl htv)

theorem s2v_hardt6rb_band_homeomorph_full_graph {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (a b c d : X → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d)
    (hab : ∀ x, a x ≤ b x) (hcd : ∀ x, c x ≤ d x)
    (hzero : ∀ x, a x = b x ↔ c x = d x) :
    ∃ h : {z : X × ℝ | z.2 ∈ Set.Icc (a z.1) (b z.1)} ≃ₜ
        {z : X × ℝ | z.2 ∈ Set.Icc (c z.1) (d z.1)},
      ∀ z w, h z = w ↔ z.val.1 = w.val.1 ∧
        (z.val.2 - a z.val.1) * (d z.val.1 - c z.val.1) =
          (w.val.2 - c z.val.1) * (b z.val.1 - a z.val.1) := by
  obtain ⟨h, hh⟩ := s2v_hardt6rb_band_homeomorph_graph a b c d ha hb hc hd hab hcd hzero
  have hbase (z : {z : X × ℝ | z.2 ∈ Set.Icc (a z.1) (b z.1)}) :
      (h z).val.1 = z.val.1 := by
    obtain ⟨t, ht, hty⟩ := s2v_hardt6rb_band_interpolation_surjective (hab z.val.1) z.property
    let v := (1 - t) * c z.val.1 + t * d z.val.1
    have hv : v ∈ Set.Icc (c z.val.1) (d z.val.1) :=
      s2v_hardt6rb_band_interpolation_mem (hcd z.val.1) ht
    have hrel : (z.val.2 - a z.val.1) * (d z.val.1 - c z.val.1) =
        (v - c z.val.1) * (b z.val.1 - a z.val.1) := by
      rw [← hty]
      dsimp only [v]
      ring
    have he := (hh z.val.1 z.val.2 v z.property hv).mpr hrel
    exact congrArg (fun w => w.val.1) he
  refine ⟨h, ?_⟩
  rintro ⟨⟨x, y⟩, hy⟩ ⟨⟨x', v⟩, hv⟩
  constructor
  · intro he
    have hx := hbase ⟨(x, y), hy⟩
    rw [he] at hx
    change x' = x at hx
    subst x'
    exact ⟨rfl, (hh x y v hy hv).mp he⟩
  · rintro ⟨hx, hrel⟩
    change x = x' at hx
    subst x'
    exact (hh x y v hy hv).mpr hrel

end HodgeLean.Foundations.Program
