import HodgeLean.Foundations.Program.G32SelectedRealizationSingleOrbitAges
import HodgeLean.Foundations.Program.G32SelectedRealizationDisjointOrbitSum

noncomputable section
open Manifold HodgeLean.Papers
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem g32y_cover_exponent_weights
    {E C G B : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ a : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun y : C ↦ a • y))
    (H : Subgroup G) {m n : ℕ} (χ : H →* Multiplicative (ZMod m))
    (w : ZMod m → ℝ) (hw : w 0 = 0)
    (r : C → H) (hr : ∀ y, b4_IsRotGen E y (r y))
    (f : C → B) (hgal : b4_IsGaloisCover G f)
    (b : Fin n → B) (hb : Function.Injective b)
    (x : Fin n → C) (hx : ∀ i, f (x i) = b i)
    (g : Fin n → G) (hg : ∀ i, b4_IsRotGen E (x i) (g i))
    (hfree : ∀ y, f y ∉ Set.range b → MulAction.stabilizer G y = ⊥) :
    ∑ᶠ y : C, (Nat.card (MulAction.stabilizer H y) : ℝ) / Nat.card H *
      w (Multiplicative.toAdd (χ (r y))) =
      ∑ i, ((papersExps H χ (g i)).map w).sum := by
  classical
  let W : C → ℝ := fun y ↦
    (Nat.card (MulAction.stabilizer H y) : ℝ) / Nat.card H *
      w (Multiplicative.toAdd (χ (r y)))
  have hdis : ∀ i j, MulAction.orbitRel G C (x i) (x j) → i = j := by
    intro i j hij
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hij
    apply hb
    rw [← hx i, ← hx j, ← ha, hgal.1]
  have hz (y : C) (hy : ∀ i, y ∉ MulAction.orbit G (x i)) : W y = 0 := by
    have hnot : f y ∉ Set.range b := by
      rintro ⟨i, hi⟩
      obtain ⟨a, ha⟩ := hgal.2 (x i) y ((hx i).trans hi)
      exact hy i (MulAction.mem_orbit_iff.mpr ⟨a, ha⟩)
    have hfix : (r y : G) ∈ MulAction.stabilizer G y := (hr y).1
    rw [hfree y hnot, Subgroup.mem_bot] at hfix
    have he : r y = 1 := Subtype.ext hfix
    simp [W, he, hw]
  letI : ∀ i, Finite (MulAction.orbit G (x i)) := fun i ↦ g32y_finite_group_orbit (x i)
  letI : ∀ i, Fintype (MulAction.orbit G (x i)) := fun _ ↦ Fintype.ofFinite _
  calc
    _ = ∑ i, ∑ y : MulAction.orbit G (x i), W y :=
      g32y_finsum_disjoint_orbits x hdis W hz
    _ = _ := Finset.sum_congr rfl (fun i _ ↦
      g32y_single_orbit_exponent_weights hE hG H (x i) (g i) (hg i) χ w hw r hr)

end HodgeLean.Foundations.Program
