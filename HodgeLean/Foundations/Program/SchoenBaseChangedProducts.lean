import HodgeLean.Foundations.Program.SchoenTerminalBaseChange
import HodgeLean.Foundations.Program.SchoenFiniteSchemeProducts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A family of morphisms over a base gives its actual lift to the base change of the finite terminal-scheme product. -/
def s2_baseChangedProductLift (S : Scheme.{0}) (n : ℕ) (Y : Fin n → Scheme.{0})
    {T : Over S} (f : ∀ i, T ⟶ (s2_terminalBaseChange S).obj (Y i)) :
    T ⟶ (s2_terminalBaseChange S).obj (s2_schemeProduct n Y) :=
  Over.homMk (pullback.lift T.hom
    (s2_schemeProductLift n Y (fun i => (f i).left ≫
      pullback.snd (terminal.from S) (terminal.from (Y i))))
    (terminal.hom_ext _ _)) (pullback.lift_fst _ _ _)

/-- Morphisms to an actual base-changed finite product are determined by all base-changed coordinate projections. -/
theorem s2_baseChangedProduct_hom_ext (S : Scheme.{0}) (n : ℕ) (Y : Fin n → Scheme.{0})
    {T : Over S} (f g : T ⟶ (s2_terminalBaseChange S).obj (s2_schemeProduct n Y))
    (h : ∀ i, f ≫ (s2_terminalBaseChange S).map (s2_schemeProductπ n Y i) =
      g ≫ (s2_terminalBaseChange S).map (s2_schemeProductπ n Y i)) : f = g := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (Over.w f).trans (Over.w g).symm
  · apply s2_schemeProduct_hom_ext n Y
    intro i
    have H := congrArg
      (fun u : T ⟶ (s2_terminalBaseChange S).obj (Y i) =>
        u.left ≫ pullback.snd (terminal.from S) (terminal.from (Y i))) (h i)
    simpa only [Over.comp_left, Category.assoc, s2_terminalBaseChange_map_snd] using H

/-- The actual lift to a base-changed finite product recovers every specified coordinate morphism over the base. -/
theorem s2_baseChangedProductLift_π (S : Scheme.{0}) (n : ℕ) (Y : Fin n → Scheme.{0})
    {T : Over S} (f : ∀ i, T ⟶ (s2_terminalBaseChange S).obj (Y i)) (i : Fin n) :
    s2_baseChangedProductLift S n Y f ≫
      (s2_terminalBaseChange S).map (s2_schemeProductπ n Y i) = f i := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (Over.w (s2_baseChangedProductLift S n Y f ≫
      (s2_terminalBaseChange S).map (s2_schemeProductπ n Y i))).trans (Over.w (f i)).symm
  · simp only [Over.comp_left, Category.assoc, s2_terminalBaseChange_map_snd,
      s2_baseChangedProductLift, Over.homMk_left, pullback.lift_snd_assoc,
      s2_schemeProductLift_π]

end HodgeLean.Foundations.Program
