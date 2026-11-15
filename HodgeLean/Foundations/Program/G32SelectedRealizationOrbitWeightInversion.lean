import HodgeLean.Foundations.Program.G32SelectedRealizationOrbitInversion
import HodgeLean.Foundations.Program.G32SelectedRealizationOrbitWeights

noncomputable section
namespace HodgeLean.Foundations.Program

theorem g32y_finite_group_orbit {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (x : X) : Finite (MulAction.orbit G x) :=
  (Set.finite_range (fun g : G ↦ g • x)).to_subtype

theorem g32y_weighted_group_orbit_sum {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (H : Subgroup G) (x : X) (g : G)
    (hg : MulAction.stabilizer G x = Subgroup.zpowers g)
    (F : X → ℝ) (hF : ∀ (h : H) (y : X), F (h • y) = F y) :
    letI : Finite (MulAction.orbit G x) := g32y_finite_group_orbit x
    letI : Fintype (MulAction.orbit G x) := Fintype.ofFinite _
    letI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) :=
      Fintype.ofFinite _
    ∑ y : MulAction.orbit G x,
      (Nat.card (MulAction.stabilizer H (y : X)) : ℝ) / Nat.card H * F y =
        ∑ z : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)),
          F (z.out.out⁻¹ • x) := by
  classical
  let Y := MulAction.orbit G x
  let Q₁ := Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))
  let Q₂ := Quotient (MulAction.orbitRel H Y)
  letI : Finite Y := g32y_finite_group_orbit x
  letI : Fintype Y := Fintype.ofFinite Y
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype Q₁ := Fintype.ofFinite Q₁
  letI : Fintype Q₂ := Fintype.ofFinite Q₂
  obtain ⟨e, he⟩ := g32y_orbit_inversion_equiv H x g hg
  have hstab (y : Y) : Nat.card (MulAction.stabilizer H y) =
      Nat.card (MulAction.stabilizer H (y : X)) := by
    have hh : MulAction.stabilizer H y = MulAction.stabilizer H (y : X) := by
      ext h
      change (h • y = y) ↔ h • (y : X) = (y : X)
      exact Subtype.ext_iff
    rw [hh]
  have hw := g32y_weighted_orbit_sum (fun y : Y ↦ F (y : X))
    (fun h y ↦ hF h (y : X))
  simp_rw [hstab] at hw
  have hv (z : Q₁) : F ((e z).out : X) = F (z.out.out⁻¹ • x) := by
    let a := z.out.out
    let y : Y := ⟨a⁻¹ • x, MulAction.mem_orbit_iff.mpr ⟨a⁻¹, rfl⟩⟩
    have hp : (Quotient.mk'' (a : G ⧸ H) : Q₁) = z := by
      change (Quotient.mk'' (Quotient.mk'' z.out.out : G ⧸ H) : Q₁) = z
      rw [Quotient.out_eq', Quotient.out_eq']
    have hy : e z = (Quotient.mk'' y : Q₂) := by
      simpa only [hp] using he a
    have hr : MulAction.orbitRel H Y (e z).out y :=
      Quotient.exact ((Quotient.out_eq' (e z)).trans hy)
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hr
    exact (congrArg F (congrArg Subtype.val hh).symm).trans (hF h (y : X))
  calc
    _ = ∑ z : Q₂, F (z.out : X) := hw
    _ = ∑ z : Q₁, F ((e z).out : X) := (Equiv.sum_comp e _).symm
    _ = _ := Finset.sum_congr rfl fun z _ ↦ hv z

end HodgeLean.Foundations.Program
