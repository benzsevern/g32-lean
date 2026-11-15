import HodgeLean.Foundations.Program.SchoenSelectedGeometryBranchIndex
import HodgeLean.Foundations.Program.SchoenSelectedGeometryOrbitCoverage
import HodgeLean.Foundations.Program.SchoenSelectedGeometryOrbitCharacter
import HodgeLean.Foundations.Program.SchoenSelectedGeometryMonodromy
import HodgeLean.Foundations.Program.G32SelectedRealizationSingleOrbitAges

noncomputable section
set_option maxHeartbeats 400000
open Manifold HodgeLean.Papers
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- A point above a residual branch index, before taking the kernel quotient. -/
def s0_branchLift {G C : Type} [Group G] [Finite G] [MulAction G C] {m n : ℕ}
    (H : Subgroup G) (χ : H →* Multiplicative (ZMod m)) (g : Fin n → G)
    (x : Fin n → C) (a : s0_BranchIndex H χ g) : C :=
  a.val.2.out.out⁻¹ • x a.val.1

/-- Local monodromy indices enumerate precisely the residual branch orbits. -/
theorem s0_branch_representatives {C G B : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
    (hG : ∀ a : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : C ↦ a • z))
    {m n : ℕ} (H : Subgroup G) (χ : H →* Multiplicative (ZMod m))
    (f : C → B) (hgal : b4_IsGaloisCover G f)
    (b : Fin n → B) (hb : Function.Injective b)
    (x : Fin n → C) (hx : ∀ i, f (x i) = b i)
    (g : Fin n → G) (hg : ∀ i, b4_IsRotGen ℂ (x i) (g i))
    (hfree : ∀ z, f z ∉ Set.range b → MulAction.stabilizer G z = ⊥) :
    Function.Injective (fun a : s0_BranchIndex H χ g ↦ rsq_proj H C (s0_branchLift H χ g x a)) ∧
      ∀ z : C, MulAction.stabilizer (H ⧸ χ.ker) (rsq_proj χ.ker C z) ≠ ⊥ ↔
        ∃ a : s0_BranchIndex H χ g, rsq_proj H C z = rsq_proj H C (s0_branchLift H χ g x a) := by
  classical
  have hlocal (a : s0_BranchIndex H χ g) :
      b4_IsRotGen ℂ (s0_branchLift H χ g x a) (papersLocalMonodromy H (g a.val.1) a.val.2) :=
    g32y_papers_monodromy_rotGen (Module.finrank_self ℂ) hG H _ _ (hg a.val.1) a.val.2
  constructor
  · intro a a' he
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact he)
    have hi : a.val.1 = a'.val.1 := by
      apply hb
      have hp := congrArg f hh
      simpa only [s0_branchLift, Subgroup.smul_def, hgal.1, hx] using hp.symm
    apply Subtype.ext
    rcases a with ⟨⟨i, q⟩, ha⟩
    rcases a' with ⟨⟨i', q'⟩, ha'⟩
    dsimp at hi
    subst i'
    have hq := s0_orbit_representatives_injective H (x i) (g i)
      (RiemannRochTop_rotGen_zpowers _ _ (hg i)).symm he
    exact Sigma.ext rfl (heq_of_eq hq)
  · intro z
    obtain ⟨r, hr⟩ := b4_exists_rotGen (Module.finrank_self ℂ) (fun h : H ↦ hG h) z
    rw [s0_residual_branch_iff_character χ z r
      (RiemannRochTop_rotGen_zpowers _ _ hr).symm]
    constructor
    · intro hχ
      have hbz : f z ∈ Set.range b := by
        by_contra hn
        have hf : (r : G) ∈ MulAction.stabilizer G z := hr.1
        rw [hfree z hn, Subgroup.mem_bot] at hf
        have h1 : r = 1 := Subtype.ext hf
        exact hχ (by rw [h1, map_one])
      obtain ⟨i, hi⟩ := hbz
      obtain ⟨u, hu⟩ := hgal.2 (x i) z ((hx i).trans hi)
      obtain ⟨q, hq⟩ := s0_orbit_representatives_cover H (x i) (g i)
        (RiemannRochTop_rotGen_zpowers _ _ (hg i)).symm z
        (MulAction.mem_orbit_iff.mpr ⟨u, hu⟩)
      have hrot := g32y_papers_monodromy_rotGen (Module.finrank_self ℂ) hG H _ _ (hg i) q
      have hc := s0_rotation_character_orbit (fun h : H ↦ hG h) χ z _ r _ hr hrot hq
      exact ⟨⟨⟨i, q⟩, fun h ↦ hχ (hc.trans h)⟩, hq⟩
    · rintro ⟨a, ha⟩
      have hc := s0_rotation_character_orbit (fun h : H ↦ hG h) χ z _ r _ hr (hlocal a) ha
      exact fun h ↦ a.property (hc.symm.trans h)

#print axioms s0_branch_representatives
end HodgeLean.Foundations.Program
