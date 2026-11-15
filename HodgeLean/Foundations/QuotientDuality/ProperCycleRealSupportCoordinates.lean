import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedCapSuspension
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Actual finite coordinates for iterated tangential support spaces -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual first real coordinate and remaining finite real coordinates assemble by the literal tuple constructor.
Source: Munkres, Topology, section 19, finite product topology.
HC no distance; AV milestone no distance. -/
def properCycle_real_cons_homeomorph (n : ℕ) :
    (ℝ × (Fin n → ℝ)) ≃ₜ (Fin (n + 1) → ℝ) where
  toEquiv := Fin.consEquiv (fun _ => ℝ)
  continuous_toFun := Continuous.finCons (A := fun _ : Fin (n + 1) => ℝ) continuous_fst continuous_snd
  continuous_invFun := (continuous_apply 0).prodMk
    (continuous_pi (fun i => continuous_apply i.succ))

/-- The actual iterated real product space has its literal finite real coordinates and original base coordinate.
Source: Munkres, Topology, section 19, finite product topology.
HC no distance; AV milestone no distance. -/
def properCycle_real_support_coordinates (Y : TopCat.{0}) :
    (n : ℕ) → properCycle_real_support_space Y n ≃ₜ ((Fin n → ℝ) × Y)
  | 0 => (Homeomorph.uniqueProd (Fin 0 → ℝ) Y).symm
  | n + 1 => ((Homeomorph.refl ℝ).prodCongr (properCycle_real_support_coordinates Y n)).trans
      ((Homeomorph.prodAssoc ℝ (Fin n → ℝ) Y).symm.trans
        ((properCycle_real_cons_homeomorph n).prodCongr (Homeomorph.refl Y)))

/-- The actual finite coordinate identification retains the original normal support as the inverse image along the base projection.
Source: Munkres, Topology, section 19, product subspaces.
HC no distance; AV milestone no distance. -/
lemma properCycle_real_support_coordinates_normal
    (Y : TopCat.{0}) (S : Set Y) (n : ℕ) :
    (properCycle_real_support_coordinates Y n) ⁻¹' (Prod.snd ⁻¹' S) =
      properCycle_real_normal_support Y S n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext z
    change (properCycle_real_support_coordinates Y n z.2).2 ∈ S ↔
      z.2 ∈ properCycle_real_normal_support Y S n
    exact Set.ext_iff.mp ih z.2

/-- The actual finite coordinate identification sends the iterated tangential support to the zero real coordinates times the original support.
Source: Munkres, Topology, section 19, product subspaces.
HC no distance; AV milestone no distance. -/
lemma properCycle_real_support_coordinates_point
    (Y : TopCat.{0}) (T : Set Y) (n : ℕ) :
    (properCycle_real_support_coordinates Y n) ⁻¹'
      {z : (Fin n → ℝ) × Y | z.1 = 0 ∧ z.2 ∈ T} =
        properCycle_real_point_support Y T n := by
  induction n with
  | zero =>
    ext z
    change ((properCycle_real_support_coordinates Y 0 z).1 = 0 ∧
      (properCycle_real_support_coordinates Y 0 z).2 ∈ T) ↔ z ∈ T
    rw [show (properCycle_real_support_coordinates Y 0 z).1 = 0 from Subsingleton.elim _ _]
    exact and_iff_right rfl
  | succ n ih =>
    ext z
    change (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) z.1 (properCycle_real_support_coordinates Y n z.2).1 = 0 ∧
        (properCycle_real_support_coordinates Y n z.2).2 ∈ T) ↔
      z.1 = 0 ∧ z.2 ∈ properCycle_real_point_support Y T n
    have hc : Fin.cons (α := fun _ : Fin (n + 1) => ℝ) z.1 (properCycle_real_support_coordinates Y n z.2).1 = 0 ↔
        z.1 = 0 ∧ (properCycle_real_support_coordinates Y n z.2).1 = 0 := by
      constructor
      · intro h
        exact ⟨congrFun h 0, funext (fun i => congrFun h i.succ)⟩
      · rintro ⟨hz, hf⟩
        rw [hz, hf]
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
    rw [hc, and_assoc]
    exact and_congr Iff.rfl (Set.ext_iff.mp ih z.2)

end HodgeLean.Foundations.QuotientDuality
