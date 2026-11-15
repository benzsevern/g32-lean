import HodgeLean.Foundations.TubularEuler.LocalNormalInverseHelpers
import HodgeLean.Foundations.TubularEuler.ZeroSectionSourceHelpers
import HodgeLean.Foundations.TubularEuler.PartialHomeomorphRestrictionHelpers
import HodgeLean.Foundations.TubularEuler.NormalBlockDerivativeHelpers
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic

/-! # Analytic local inverses fixing the zero section

The inverse function construction retains the supplied coordinate map and exact support.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Topology TopologicalSpace
namespace HodgeLean.Foundations.TubularEuler

theorem analytic_zero_section_local_inverse
    {B N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
    (f : B × N → B × N) (D : Set (B × N)) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ⊤ f D)
    (hfix : ∀ b, (b, (0 : N)) ∈ D → f (b, 0) = (b, 0))
    (x : B) (hx : (x, (0 : N)) ∈ D)
    (A : (B × N) ≃L[ℝ] (B × N))
    (hA : HasFDerivAt f A.toContinuousLinearMap (x, 0)) :
    ∃ L : OpenPartialHomeomorph (B × N) (B × N),
      (x, (0 : N)) ∈ L.source ∧ L.source ⊆ D ∧ (L : B × N → B × N) = f ∧
      ContDiffOn ℝ ⊤ L L.source ∧ ContDiffOn ℝ ⊤ L.symm L.target ∧
      ∀ z ∈ L.source, (L z).2 = 0 ↔ z.2 = 0 := by
  have hf0 := hf.contDiffAt (hD.mem_nhds hx)
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  let L0 := hf0.toOpenPartialHomeomorph f hA hn
  have hL0 : (L0 : B × N → B × N) = f := rfl
  have hx0 : (x, (0 : N)) ∈ L0.source := hf0.mem_toOpenPartialHomeomorph_source hA hn
  have hxT : f (x, (0 : N)) ∈ L0.target := hf0.image_mem_toOpenPartialHomeomorph_target hA hn
  have hleft : L0.symm (f (x, (0 : N))) = (x, 0) := by
    change L0.symm (L0 (x, 0)) = (x, 0)
    exact L0.left_inv hx0
  have hi : ContDiffAt ℝ ⊤ L0.symm (f (x, (0 : N))) := by
    apply L0.contDiffAt_symm (f₀' := A) hxT
    · simpa only [hleft, hL0] using hA
    · simpa only [hleft, hL0] using hf0
  obtain ⟨T, hT, hTi⟩ := hi.contDiffOn le_rfl (fun _ => rfl)
  obtain ⟨V, hVT, hVo, hpV⟩ := mem_nhds_iff.mp hT
  let R : Opens (B × N) := ⟨D ∩ f ⁻¹' V,
    hf.continuousOn.isOpen_inter_preimage hD hVo⟩
  let L1 := L0.restrOpen R R.isOpen
  have hx1 : (x, (0 : N)) ∈ L1.source := ⟨hx0, hx, hpV⟩
  have hfix1 : ∀ b, (b, (0 : N)) ∈ L1.source → L1 (b, 0) = (b, 0) := by
    intro b hb
    exact hfix b hb.2.1
  obtain ⟨U, hxU, hUL1, hsupp⟩ := localInverse_zero_support_shrinking L1 hfix1 x hx1
  let L := L1.restrOpen U U.isOpen
  refine ⟨L, ⟨hx1, hxU⟩, (fun _ hz => hz.1.2.1), rfl, ?_, ?_, ?_⟩
  · exact hf.mono (fun _ hz => hz.1.2.1)
  · have ht : L.target ⊆ T := by
      intro y hy
      have hyV : y ∈ V := by
        have hz := (L.map_target hy).1.2.2
        change L (L.symm y) ∈ V at hz
        rwa [L.right_inv hy] at hz
      exact hVT hyV
    exact hTi.mono ht
  · intro z hz
    exact hsupp z hz.2

theorem analytic_transverse_local_inverse
    {B N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
    (f : B × N → B × N) (D : Set (B × N)) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ⊤ f D)
    (hfix : ∀ b, (b, (0 : N)) ∈ D → f (b, 0) = (b, 0))
    (x : B) (hx : (x, (0 : N)) ∈ D)
    (A : N ≃L[ℝ] N)
    (hA : HasFDerivAt (fun n : N => (f (x, n)).2) A.toContinuousLinearMap 0) :
    ∃ L : OpenPartialHomeomorph (B × N) (B × N),
      (x, (0 : N)) ∈ L.source ∧ L.source ⊆ D ∧ (L : B × N → B × N) = f ∧
      ContDiffOn ℝ ⊤ L L.source ∧ ContDiffOn ℝ ⊤ L.symm L.target ∧
      ∀ z ∈ L.source, (L z).2 = 0 ↔ z.2 = 0 := by
  have hd : DifferentiableAt ℝ f (x, (0 : N)) :=
    (hf.contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp)
  let F := fderiv ℝ f (x, (0 : N))
  let C := normalBlockContinuousLinearEquiv
    ((ContinuousLinearMap.fst ℝ B N).comp (F.comp (ContinuousLinearMap.inr ℝ B N))) A
  have hC : HasFDerivAt f C.toContinuousLinearMap (x, 0) :=
    hasFDerivAt_normalBlock f D hD hfix x hx F hd.hasFDerivAt A hA
  exact analytic_zero_section_local_inverse f D hD hf hfix x hx C hC

theorem analytic_complex_transverse_local_inverse
    {B N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [NormedSpace ℂ N]
    [IsScalarTower ℝ ℂ N] [CompleteSpace N]
    (f : B × N → B × N) (D : Set (B × N)) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ⊤ f D)
    (hfix : ∀ b, (b, (0 : N)) ∈ D → f (b, 0) = (b, 0))
    (x : B) (hx : (x, (0 : N)) ∈ D)
    (A : N ≃L[ℂ] N)
    (hA : HasFDerivAt (fun n : N => (f (x, n)).2) A.toContinuousLinearMap 0) :
    ∃ L : OpenPartialHomeomorph (B × N) (B × N),
      (x, (0 : N)) ∈ L.source ∧ L.source ⊆ D ∧ (L : B × N → B × N) = f ∧
      ContDiffOn ℝ ⊤ L L.source ∧ ContDiffOn ℝ ⊤ L.symm L.target ∧
      (∀ z ∈ L.source, (L z).2 = 0 ↔ z.2 = 0) ∧
      HasFDerivAt (fun n : N => (L (x, n)).2) A.toContinuousLinearMap 0 := by
  obtain ⟨L, hp, hsub, heq, hLf, hLg, hs⟩ :=
    analytic_transverse_local_inverse f D hD hf hfix x hx (A.restrictScalars ℝ)
      (hA.restrictScalars ℝ)
  refine ⟨L, hp, hsub, heq, hLf, hLg, hs, ?_⟩
  rw [heq]
  exact hA

theorem analytic_complex_transverse_local_inverse_stable
    {B N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [NormedSpace ℂ N]
    [IsScalarTower ℝ ℂ N] [CompleteSpace N]
    (f : B × N → B × N) (D : Set (B × N)) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ⊤ f D)
    (hfix : ∀ b, (b, (0 : N)) ∈ D → f (b, 0) = (b, 0))
    (x : B) (hx : (x, (0 : N)) ∈ D)
    (A : N ≃L[ℂ] N)
    (hA : HasFDerivAt (fun n : N => (f (x, n)).2) A.toContinuousLinearMap 0) :
    ∃ L : OpenPartialHomeomorph (B × N) (B × N),
      (x, (0 : N)) ∈ L.source ∧ L.source ⊆ D ∧ (L : B × N → B × N) = f ∧
      ContDiffOn ℝ ⊤ L L.source ∧ ContDiffOn ℝ ⊤ L.symm L.target ∧
      (∀ z ∈ L.source, (L z).2 = 0 ↔ z.2 = 0) ∧
      (∀ z ∈ L.source, (z.1, (0 : N)) ∈ L.source) ∧
      HasFDerivAt (fun n : N => (L (x, n)).2) A.toContinuousLinearMap 0 := by
  obtain ⟨L0, hp, hsub, heq, hLf, hLg, hs, hLA⟩ :=
    analytic_complex_transverse_local_inverse f D hD hf hfix x hx A hA
  let L := zeroSectionSourceRestriction L0
  have hsource : L.source ⊆ L0.source := fun _ hz => hz.1
  obtain ⟨hcf, hcg⟩ := partialHomeomorph_contDiffOn_of_compatible L L0 hsource
    (fun _ _ => rfl) hLf hLg
  exact ⟨L, ⟨hp, hp, hp⟩, (fun z hz => hsub (hsource hz)), heq, hcf, hcg,
    (fun z hz => hs z (hsource hz)), zeroSectionSourceRestriction_source_zero L0, hLA⟩

theorem analytic_complex_normal_inverse_on_source
    {B N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [NormedSpace ℂ N]
    [IsScalarTower ℝ ℂ N] [CompleteSpace N]
    (f : B × N → B × N) (D : Set (B × N)) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ⊤ f D)
    (hfix : ∀ b, (b, (0 : N)) ∈ D → f (b, 0) = (b, 0))
    (hnormal : ∀ b, (b, (0 : N)) ∈ D → ∃ A : N ≃L[ℂ] N,
      HasFDerivAt (fun n : N => (f (b, n)).2) A.toContinuousLinearMap 0)
    (x : B) (hx : (x, (0 : N)) ∈ D) :
    ∃ L : OpenPartialHomeomorph (B × N) (B × N),
      (x, (0 : N)) ∈ L.source ∧ L.source ⊆ D ∧ (L : B × N → B × N) = f ∧
      ContDiffOn ℝ ⊤ L L.source ∧ ContDiffOn ℝ ⊤ L.symm L.target ∧
      (∀ z ∈ L.source, (L z).2 = 0 ↔ z.2 = 0) ∧
      (∀ z ∈ L.source, (z.1, (0 : N)) ∈ L.source) ∧
      ∀ z ∈ L.source, ∃ A : N ≃L[ℂ] N,
        HasFDerivAt (fun n : N => (L (z.1, n)).2) A.toContinuousLinearMap 0 := by
  obtain ⟨A, hA⟩ := hnormal x hx
  obtain ⟨L, hp, hsub, heq, hLf, hLg, hs, hz0, _⟩ :=
    analytic_complex_transverse_local_inverse_stable f D hD hf hfix x hx A hA
  refine ⟨L, hp, hsub, heq, hLf, hLg, hs, hz0, ?_⟩
  intro z hz
  obtain ⟨Az, hAz⟩ := hnormal z.1 (hsub (hz0 z hz))
  refine ⟨Az, ?_⟩
  rw [heq]
  exact hAz

#print axioms analytic_zero_section_local_inverse
#print axioms analytic_transverse_local_inverse
#print axioms analytic_complex_transverse_local_inverse
#print axioms analytic_complex_transverse_local_inverse_stable
#print axioms analytic_complex_normal_inverse_on_source

end HodgeLean.Foundations.TubularEuler
