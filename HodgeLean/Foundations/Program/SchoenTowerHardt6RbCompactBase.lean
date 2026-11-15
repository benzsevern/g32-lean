import HodgeLean.Foundations.Program.SchoenTowerHardt2
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBandCoordinates

/-! The height projection of a compact Boolean carrier has an actual compact Boolean base. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_compact_base {n : ℕ}
    (f : s2v_t11b_Formula (n + 1)) (hf : IsCompact f.realize) :
    ∃ P : s2v_t11b_Formula n, IsCompact P.realize ∧
      P.realize = (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
        WithLp.toLp 2 (fun v : Fin n => y v.succ)) '' f.realize ∧
      ∀ x, x ∈ P.realize ↔ ∃ t : ℝ,
        WithLp.toLp 2 (Fin.cons t (fun v => x v)) ∈ f.realize := by
  obtain ⟨P, hP⟩ := s2v_hardt2_projection f
  obtain ⟨e, _, _, _, hes⟩ := s2v_hardt6rb_band_coordinate_equiv n
  have hπ : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
      WithLp.toLp 2 (fun v : Fin n => y v.succ)) := by
    convert continuous_fst.comp e.symm.continuous using 1
    funext y
    ext v
    exact (hes y v).symm
  have himage : P.realize = (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
      WithLp.toLp 2 (fun v : Fin n => y v.succ)) '' f.realize := by
    ext x
    rw [hP x]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨WithLp.toLp 2 (Fin.cons t (fun v => x v)), ht, by ext v; rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y 0, ?_⟩
      convert hy using 1
      ext v
      exact Fin.cases rfl (fun _ => rfl) v
  exact ⟨P, himage.symm ▸ hf.image hπ, himage, hP⟩

end HodgeLean.Foundations.Program
