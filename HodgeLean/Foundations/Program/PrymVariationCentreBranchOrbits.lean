import HodgeLean.Foundations.Program.PrymVariationCentreOrbit

noncomputable section
open HodgeLean.Papers
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

section Surface
variable (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
  [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [MulAction b4b_Group C] [FaithfulSMul b4b_Group C]
  (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
  (p : C → OnePoint ℂ) (hp : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω p)
  (hgal : b4_IsGaloisCover b4b_Group p)
include hp hgal

theorem b63d_rotation_ne_one_mem_branch (x : C)
    (hx : b63d_rotationGenerator C hG x ≠ 1) : p x ∈ b4_branchSet ℂ ℂ p := by
  have hr := b63d_rotationGenerator_isRotGen C hG x
  have ho : 2 ≤ orderOf (b63d_rotationGenerator C hG x) := by
    have hpos := orderOf_pos (b63d_rotationGenerator C hG x)
    have hne : orderOf (b63d_rotationGenerator C hG x) ≠ 1 := by
      exact fun he ↦ hx (orderOf_eq_one_iff.mp he)
    omega
  refine ⟨x, ?_, rfl⟩
  change 2 ≤ b4_ramIndex ℂ ℂ p x
  rw [b4cov_ramIndex_galois (by simp) (by simp) hG p hp hgal x, ← hr.2.1]
  exact ho

theorem b63d_branch_weighted_sum {n : ℕ} (q : Fin n → OnePoint ℂ)
    (hq : Function.Injective q) (r : Fin n → b4b_Group)
    (hbranch : b4_branchSet ℂ ℂ p = Set.range q)
    (hrot : ∀ i, ∃ x : C, p x = q i ∧ b4_IsRotGen ℂ x (r i))
    (a : b4b_Group → ℝ) (ha1 : a 1 = 0)
    (hac : ∀ g h : b4b_Group, a (g * h * g⁻¹) = a h) :
    (∑ᶠ x : C, (Nat.card (MulAction.stabilizer b4b_Group x) : ℝ) /
      Fintype.card b4b_Group * a (b63d_rotationGenerator C hG x)) = ∑ i, a (r i) := by
  classical
  choose x hpx hrx using hrot
  have hxrot (i : Fin n) : b63d_rotationGenerator C hG (x i) = r i :=
    b63d_rotationGenerator_eq C hG (x i) (r i) (hrx i)
  have hd : Pairwise (fun i j ↦ Disjoint (MulAction.orbit b4b_Group (x i)) (MulAction.orbit b4b_Group (x j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro y hyi hyj
    obtain ⟨g, rfl⟩ := hyi
    obtain ⟨h, hh⟩ := hyj
    apply hij
    apply hq
    calc
      q i = p (x i) := (hpx i).symm
      _ = p (g • x i) := (hgal.1 g (x i)).symm
      _ = p (h • x j) := congrArg p hh.symm
      _ = p (x j) := hgal.1 h (x j)
      _ = q j := hpx j
  have hs : Function.support (fun y : C ↦ a (b63d_rotationGenerator C hG y)) ⊆
      ⋃ i, MulAction.orbit b4b_Group (x i) := by
    intro y hy
    have hyne : b63d_rotationGenerator C hG y ≠ 1 := by
      intro he
      apply hy
      change a (b63d_rotationGenerator C hG y) = 0
      rw [he, ha1]
    have hb := b63d_rotation_ne_one_mem_branch C hG p hp hgal y hyne
    rw [hbranch] at hb
    obtain ⟨i, hi⟩ := hb
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    exact hgal.2 (x i) y ((hpx i).trans hi)
  have h := b63d_weighted_orbits_sum
    (fun y : C ↦ a (b63d_rotationGenerator C hG y))
    (fun g y ↦ by rw [b63d_rotationGenerator_smul C hG y g, hac]) x hd hs
  simpa only [hxrot] using h

end Surface
end HodgeLean.Foundations.Program
