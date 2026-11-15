import HodgeLean.Foundations.Program.G32SelectedRealizationEmbeddingIndex
import HodgeLean.Foundations.Program.G32SelectedRealizationCharacterHolo

noncomputable section
open HodgeLean.Foundations HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem g32y_root_residue_angle (S : g32p_Supplier) (u : (ZMod S.m)ˣ) (a : ZMod S.m) :
    g32h_angle ((g32p_root S.m ^ (u : ZMod S.m).val) ^ a.val) =
      (((u : ZMod S.m) * a).val : ℝ) / S.m := by
  have hz := g32p_root_primitive S
  have hm (n : ℕ) : g32p_root S.m ^ (n % S.m) = g32p_root S.m ^ n := by
    simpa only [← hz.eq_orderOf] using pow_mod_orderOf (g32p_root S.m) n
  rw [← pow_mul]
  have he : g32p_root S.m ^ ((u : ZMod S.m).val * a.val) =
      g32p_root S.m ^ (((u : ZMod S.m) * a).val) := by
    rw [ZMod.val_mul]
    exact (hm _).symm
  rw [he]
  exact b4_angle_exp_power (NeZero.pos S.m) (ZMod.val_lt _)

theorem g32y_fieldValue_residue_angle (S : g32p_Supplier)
    (σ : cyc_Field S.m →ₐ[ℚ] ℂ) :
    ∃ u : (ZMod S.m)ˣ, ∀ h : S.H,
      g32h_angle (σ (g32p_fieldValue S h)) =
        (((u : ZMod S.m) * Multiplicative.toAdd (S.χ h)).val : ℝ) / S.m := by
  obtain ⟨u, hu⟩ := g32y_embedding_root_index S σ
  refine ⟨u, fun h ↦ ?_⟩
  rw [g32p_fieldValue, map_pow, hu]
  exact g32y_root_residue_angle S u _

end HodgeLean.Foundations.Program
