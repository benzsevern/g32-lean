import HodgeLean.Foundations.Program.G32SelectedRealizationFiniteSupportSum
import HodgeLean.Foundations.Program.G32SelectedRealizationOrbitWeightInversion

noncomputable section
namespace HodgeLean.Foundations.Program

theorem g32y_finsum_disjoint_orbits {G X I : Type*} [Group G] [Finite G]
    [MulAction G X] [Fintype I] (x : I → X)
    (hdis : ∀ i j, MulAction.orbitRel G X (x i) (x j) → i = j)
    (w : X → ℝ) (hw : ∀ y, (∀ i, y ∉ MulAction.orbit G (x i)) → w y = 0) :
    letI : ∀ i, Finite (MulAction.orbit G (x i)) := fun i ↦ g32y_finite_group_orbit (x i)
    letI : ∀ i, Fintype (MulAction.orbit G (x i)) := fun _ ↦ Fintype.ofFinite _
    ∑ᶠ y, w y = ∑ i, ∑ y : MulAction.orbit G (x i), w y := by
  classical
  letI : ∀ i, Finite (MulAction.orbit G (x i)) := fun i ↦ g32y_finite_group_orbit (x i)
  letI : ∀ i, Fintype (MulAction.orbit G (x i)) := fun _ ↦ Fintype.ofFinite _
  let Y := (i : I) × MulAction.orbit G (x i)
  let p : Y → X := fun z ↦ z.2.val
  have hp : Function.Injective p := by
    rintro ⟨i, u⟩ ⟨j, v⟩ hab
    change (u : X) = (v : X) at hab
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp u.property
    obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp v.property
    have hij : i = j := hdis i j (MulAction.mem_orbit_iff.mpr ⟨a⁻¹ * b, by
      rw [mul_smul, hb, ← hab, ← ha, inv_smul_smul]⟩)
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext hab)
  have hz (y : X) (hy : y ∉ Set.range p) : w y = 0 := by
    apply hw y
    intro i hi
    exact hy ⟨⟨i, ⟨y, hi⟩⟩, rfl⟩
  have hh := g32y_finsum_eq_sum_injective p hp w hz
  simpa only [Y, p, Fintype.sum_sigma] using hh

end HodgeLean.Foundations.Program
