import HodgeLean.Foundations.Program.SchoenCycleC1ActualLocalActionHelpers
import Mathlib.GroupTheory.OrderOfElement
import HodgeLean.Foundations.Program.SchoenCycleStep1InvariantSections

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- An eigenidentity for the specified full-order generator determines the
exact complex character of every original cyclic scheme action. -/
theorem s2e_c1_cyclic_rational_eigencharacter
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (G : Type) [Group G] [Finite G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (g : G) (hg : orderOf g = Nat.card G) (χ : G →* ℂˣ)
    (z : X.left.functionField)
    (heig : letI := s2e_step1_action_isIso X G a ha1 hamul g
      s2e_step1_fieldPullback X.left (a g).left z =
        HodgeLean.Foundations.Curves.stalkC (genericPoint X.left) (χ g : ℂ) * z) :
    ∀ u : G, letI := s2e_step1_action_isIso X G a ha1 hamul u
      s2e_step1_fieldPullback X.left (a u).left z =
        HodgeLean.Foundations.Curves.stalkC (genericPoint X.left) (χ u : ℂ) * z := by
  letI : ∀ u, IsIso (a u) := s2e_step1_action_isIso X G a ha1 hamul
  let C := HodgeLean.Foundations.Curves.stalkC (genericPoint X.left)
  have hscalar (c : ℂ) :
      s2e_step1_fieldPullback X.left (a g).left (C c) = C c :=
    s2e_fixed_point_stalkPullback_scalars X (a g) (genericPoint X.left)
      (genericPoint_eq_of_isOpenImmersion (a g).left) c
  have hp (n : ℕ) : s2e_step1_fieldPullback X.left (a (g ^ n)).left z =
      C (χ (g ^ n) : ℂ) * z := by
    induction n with
    | zero =>
      simp only [pow_zero, ha1, Over.id_left, s2e_c1_fieldPullback_id, RingHom.id_apply,
        map_one, Units.val_one, one_mul]
    | succ n ih =>
      have hcomp : (a (g ^ (n + 1))).left = (a g).left ≫ (a (g ^ n)).left := by
        rw [pow_succ, hamul]
        rfl
      have hpb : s2e_step1_fieldPullback X.left (a (g ^ (n + 1))).left =
          s2e_step1_fieldPullback X.left ((a g).left ≫ (a (g ^ n)).left) := by
        congr 1
      rw [hpb, s2e_c1_fieldPullback_comp, RingHom.comp_apply, ih, map_mul, hscalar, heig]
      change C (χ (g ^ n) : ℂ) * (C (χ g : ℂ) * z) = C (χ (g ^ (n + 1)) : ℂ) * z
      rw [pow_succ, map_mul, Units.val_mul, map_mul, mul_assoc]
  have htop : Subgroup.zpowers g = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hg])
  intro u
  have hu : u ∈ Subgroup.zpowers g := by rw [htop]; trivial
  obtain ⟨n, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hu
  exact hp n

end HodgeLean.Foundations.Program
