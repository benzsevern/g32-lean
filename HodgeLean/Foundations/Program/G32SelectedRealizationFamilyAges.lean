import HodgeLean.Foundations.Program.G32SelectedRealizationCoverAges
import HodgeLean.Foundations.Program.G32SelectedRealizationNielsenAges
import HodgeLean.Foundations.Program.G32SelectedRealizationUnbranchedStabilizer
import HodgeLean.Foundations.Program.G32SelectedRealizationDefs

noncomputable section
open Manifold HodgeLean.Papers
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.fibreFaithful
  b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

theorem g32y_family_exponent_weights {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (S : g32p_Supplier) (w : ZMod S.m → ℝ) (hw : w 0 = 0)
    (r : b65z_fibre c D.C t → S.H) (hr : ∀ y, b4_IsRotGen ℂ y (r y)) :
    (∑ᶠ y : b65z_fibre c D.C t,
      (Nat.card (MulAction.stabilizer S.H y) : ℝ) / Nat.card S.H *
        w (Multiplicative.toAdd (S.χ (r y)))) =
      ((g32p_exponents S).map fun a : ℕ ↦ w (a : ZMod S.m)).sum := by
  classical
  letI : NeZero S.m := ⟨by have := S.three_le; omega⟩
  choose x hx hrot using D.hrot t
  let p := b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Set.Subset.refl _) t
  have hfree (y : b65z_fibre c D.C t) (hy : p y ∉ Set.range (b6_branch t.val)) :
      MulAction.stabilizer b4b_Group y = ⊥ := by
    apply g32y_stabilizer_trivial_off_branch (by simp : Module.finrank ℂ ℂ = 1)
      (by simp : Module.finrank ℂ ℂ = 1) (D.hG t) p (D.hk t) (D.hgal t) y
    rwa [D.hbranch t]
  have hb : Function.Injective (b6_branch t.val) :=
    (b6t_polydisc_neighbourhood c D.atlas.hb).2.2.2 t.property
  calc
    _ = ∑ i, ((papersExps S.H S.χ (g i)).map w).sum :=
      g32y_cover_exponent_weights (by simp : Module.finrank ℂ ℂ = 1)
        (D.hG t) S.H S.χ w hw r hr p (D.hgal t) (b6_branch t.val) hb x hx g hrot hfree
    _ = _ := g32y_nielsen_exponent_weights (D.hG t) S.H S.χ w hw r hr g hg x hrot

end HodgeLean.Foundations.Program
