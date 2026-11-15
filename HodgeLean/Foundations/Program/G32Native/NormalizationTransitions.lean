import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationMapHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationSourceHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Relative normalization transports a base transition and its retained source. -/
theorem g32w_normalization_transition {T : Scheme} (X Y : Over (Spec ↧ℂ))
    (b : X ⟶ Y) (f : T ⟶ X.left) (g : T ⟶ Y.left)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (h : f ≫ b.left = g) :
    ∃ w : s2b_normalizationOver X f ⟶ s2b_normalizationOver Y g,
      f.toNormalization ≫ w.left = g.toNormalization ∧
      w ≫ s2b_normalizationMap Y g = s2b_normalizationMap X f ≫ b := by
  let v := pullback.lift f g.toNormalization
    (h.trans g.toNormalization_fromNormalization.symm)
  let p : pullback b.left g.fromNormalization ⟶ X.left := pullback.fst _ _
  have hv : f = v ≫ p := (pullback.lift_fst _ _ _).symm
  let u := f.normalizationDesc v p hv
  let w := u ≫ pullback.snd b.left g.fromNormalization
  have hw : f.toNormalization ≫ w = g.toNormalization := by
    rw [← Category.assoc, f.toNormalization_normalizationDesc]
    exact pullback.lift_snd _ _ _
  have hb : w ≫ g.fromNormalization = f.fromNormalization ≫ b.left := by
    dsimp only [w]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      f.normalizationDesc_comp]
  refine ⟨Over.homMk w ?_, hw, ?_⟩
  · change w ≫ (g.fromNormalization ≫ Y.hom) = f.fromNormalization ≫ X.hom
    rw [← Category.assoc, hb, Category.assoc, Over.w b]
  · apply Over.OverMorphism.ext
    exact hb

end HodgeLean.Foundations.Program
