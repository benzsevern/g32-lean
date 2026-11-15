import HodgeLean.Foundations.QuotientDuality.LocalRepresentedFamilyCoefficients

/-! Dense calibration determines a coherent orientation on every component. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Topology TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem coherent_orientation_generators_eq_of_dense
    (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (o₁ o₂ : LocalRationalOrientation X n) (S : Set X) (hS : Dense S)
    (heq : ∀ x ∈ S, o₁.generator x = o₂.generator x) :
    ∀ x, o₁.generator x = o₂.generator x := by
  obtain ⟨f, hflc, hf⟩ := locally_represented_family_coefficients X n o₁ X
    id continuous_id o₂.generator o₂.coherent
  intro x
  have hopen : IsOpen {y : X | f y = f x} := hflc.isOpen_fiber (f x)
  obtain ⟨y, hy, hyS⟩ := hS.inter_open_nonempty _ hopen ⟨x, rfl⟩
  have hfy : f y = 1 := (o₁.generates y).1 (by
    change f y • o₁.generator y = (1 : ℚ) • o₁.generator y
    exact (hf y).symm.trans ((heq y hyS).symm.trans (one_smul ℚ _).symm))
  have hfx : f x = 1 := hy.symm.trans hfy
  exact ((hf x).trans (by rw [hfx, one_smul]; rfl)).symm

#print axioms coherent_orientation_generators_eq_of_dense
end HodgeLean.Foundations.QuotientDuality
