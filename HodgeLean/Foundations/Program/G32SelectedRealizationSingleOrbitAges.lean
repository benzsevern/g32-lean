import HodgeLean.Foundations.Program.G32SelectedRealizationLocalMonodromy
import HodgeLean.Foundations.Program.G32SelectedRealizationRotationCharacter
import HodgeLean.Foundations.Program.G32SelectedRealizationOrbitWeightInversion
import HodgeLean.Foundations.Program.G32SelectedRealizationExponentWeights

noncomputable section
open Manifold HodgeLean.Papers
open scoped ContDiff
namespace HodgeLean.Foundations.Program

section
variable {E C G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
  (hE : Module.finrank ℂ E = 1)
  (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
  (H : Subgroup G) (x : C) (g : G) (hg : b4_IsRotGen E x g)

include hE hG hg

theorem g32y_papers_monodromy_rotGen
    (q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) :
    b4_IsRotGen E (q.out.out⁻¹ • x) (papersLocalMonodromy H g q) := by
  have hh := g32y_local_monodromy_rotGen hE hG H x g hg q.out.out
  have he : (q.out.out : G ⧸ H) = q.out := Quotient.out_eq' q.out
  simpa only [he, papersLocalMonodromy] using hh

theorem g32y_single_orbit_exponent_weights {m : ℕ}
    (χ : H →* Multiplicative (ZMod m)) (w : ZMod m → ℝ) (hw : w 0 = 0)
    (r : C → H) (hr : ∀ y, b4_IsRotGen E y (r y)) :
    letI : Finite (MulAction.orbit G x) := g32y_finite_group_orbit x
    letI : Fintype (MulAction.orbit G x) := Fintype.ofFinite _
    ∑ y : MulAction.orbit G x,
      (Nat.card (MulAction.stabilizer H (y : C)) : ℝ) / Nat.card H *
        w (Multiplicative.toAdd (χ (r y))) = ((papersExps H χ g).map w).sum := by
  classical
  letI : Finite (MulAction.orbit G x) := g32y_finite_group_orbit x
  letI : Fintype (MulAction.orbit G x) := Fintype.ofFinite _
  letI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) :=
    Fintype.ofFinite _
  let F : C → ℝ := fun y ↦ w (Multiplicative.toAdd (χ (r y)))
  have hF (h : H) (y : C) : F (h • y) = F y :=
    congrArg (fun z : Multiplicative (ZMod m) ↦ w (Multiplicative.toAdd z))
      (g32y_rotation_character_invariant hE (fun h : H ↦ hG h) r hr χ h y)
  have hW := g32y_weighted_group_orbit_sum H x g
    (RiemannRochTop_rotGen_zpowers x g hg).symm F hF
  have hlocal (q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) :
      r (q.out.out⁻¹ • x) = papersLocalMonodromy H g q :=
    b4_rotGen_unique hE (fun h : H ↦ hG h) _ _ _ (hr _)
      (g32y_papers_monodromy_rotGen hE hG H x g hg q)
  calc
    _ = ∑ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)),
        F (q.out.out⁻¹ • x) := hW
    _ = ∑ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)),
        w (Multiplicative.toAdd (χ (papersLocalMonodromy H g q))) := by
      apply Finset.sum_congr rfl
      intro q _
      exact congrArg (fun h : H ↦ w (Multiplicative.toAdd (χ h))) (hlocal q)
    _ = _ := (g32y_papers_local_exponent_weight H χ g w hw).symm

end
end HodgeLean.Foundations.Program
