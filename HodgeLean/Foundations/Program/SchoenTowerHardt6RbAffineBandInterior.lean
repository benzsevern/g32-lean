import HodgeLean.Foundations.Program.SchoenTowerHardt6RbStrictBandInterior
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAffineInteriorPositive
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAffineInteriorImage

/-! Exact intrinsic interiors of affine bands with at least one noncollapsed fiber. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_affine_band_interior {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hC : Convex ℝ C) (l u : E →ᵃ[ℝ] ℝ)
    (hl : Continuous l) (hu : Continuous u) (hlu : ∀ x ∈ C, l x ≤ u x)
    (hne : ∃ y ∈ C, l y < u y) :
    intrinsicInterior ℝ {p : E × ℝ | p.1 ∈ C ∧ l p.1 ≤ p.2 ∧ p.2 ≤ u p.1} =
      {p : E × ℝ | p.1 ∈ intrinsicInterior ℝ C ∧ l p.1 < p.2 ∧ p.2 < u p.1} := by
  let B : Set (E × ℝ) := {p | p.1 ∈ C ∧ l p.1 ≤ p.2 ∧ p.2 ≤ u p.1}
  let f : E × ℝ →ᵃ[ℝ] E := (LinearMap.fst ℝ E ℝ).toAffineMap
  let g : E × ℝ →ᵃ[ℝ] ℝ := (LinearMap.snd ℝ E ℝ).toAffineMap
  have himage : f '' B = C := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp.1
    · intro hx
      exact ⟨(x, l x), ⟨hx, le_rfl, hlu x hx⟩, rfl⟩
  obtain ⟨y, hy, hylt⟩ := hne
  ext p
  constructor
  · intro hp
    have hbase := s2v_hardt6rb_affine_interior_image B f (himage.symm ▸ hC) hp
    rw [himage] at hbase
    refine ⟨hbase, ?_, ?_⟩
    · have hh := s2v_hardt6rb_affine_interior_positive B (g - l.comp f)
        (fun q hq => sub_nonneg.mpr hq.2.1)
        ⟨(y, u y), ⟨hy, hylt.le, le_rfl⟩, sub_pos.mpr hylt⟩ hp
      exact sub_pos.mp hh
    · have hh := s2v_hardt6rb_affine_interior_positive B (u.comp f - g)
        (fun q hq => sub_nonneg.mpr hq.2.2)
        ⟨(y, l y), ⟨hy, le_rfl, hylt.le⟩, sub_pos.mpr hylt⟩ hp
      exact sub_pos.mp hh
  · rintro ⟨hp, hlo, hup⟩
    exact s2v_hardt6rb_strict_band_interior C l u hl hu hp hlo hup

end HodgeLean.Foundations.Program
