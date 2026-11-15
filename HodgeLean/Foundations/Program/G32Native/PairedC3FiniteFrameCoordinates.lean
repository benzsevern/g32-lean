import HodgeLean.Foundations.Program.G32Native.PairedC3LocalModuleComparison
import Mathlib.LinearAlgebra.Pi

/-! # Coefficients of finite families of original section generators -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
variable {X : Scheme.{0}} {M : X.Modules} {σ : Type} [Fintype σ]

/-- Synthesis in a finite family of actual sections on a specified open. -/
def pairedC3FiniteFrameSynthesis {U : X.Opens} (g : σ → Γ(M, U))
    (V : X.Opens) (h : V ≤ U) :
    (σ → Γ(X, V)) →ₗ[Γ(X, V)] Γ(M, V) where
  toFun c := ∑ b, c b • pairedC3ModuleRestrict M h (g b)
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- Synthesis commutes with the original structure and module restrictions. -/
theorem paired_c3_finite_frame_synthesis_restrict {U : X.Opens}
    (g : σ → Γ(M, U)) (V W : X.Opens) (hV : V ≤ U) (h : W ≤ V)
    (c : σ → Γ(X, V)) :
    pairedC3ModuleRestrict M h (pairedC3FiniteFrameSynthesis g V hV c) =
      pairedC3FiniteFrameSynthesis g W (h.trans hV)
        (fun b => X.presheaf.map (homOfLE h).op (c b)) := by
  change M.presheaf.map (homOfLE h).op (∑ b, c b • _) = _
  rw [map_sum]
  simp only [Scheme.Modules.map_smul, paired_c3_module_restrict_comp,
    pairedC3FiniteFrameSynthesis, LinearMap.coe_mk, AddHom.coe_mk]

/-- A free finite family gives coefficients in its original section generators. -/
def pairedC3FiniteFrameCoordinate {U : X.Opens} (g : σ → Γ(M, U))
    (V : X.Opens) (hV : V ≤ U)
    (hg : Function.Bijective (pairedC3FiniteFrameSynthesis g V hV)) :
    Γ(M, V) ≃ₗ[Γ(X, V)] (σ → Γ(X, V)) :=
  (LinearEquiv.ofBijective (pairedC3FiniteFrameSynthesis g V hV) hg).symm

/-- The coefficients of restricted sections are the restricted coefficients. -/
theorem paired_c3_finite_frame_coordinate_restrict {U : X.Opens}
    (g : σ → Γ(M, U)) (V W : X.Opens) (hV : V ≤ U) (h : W ≤ V)
    (hgV : Function.Bijective (pairedC3FiniteFrameSynthesis g V hV))
    (hgW : Function.Bijective (pairedC3FiniteFrameSynthesis g W (h.trans hV)))
    (s : Γ(M, V)) :
    pairedC3FiniteFrameCoordinate g W (h.trans hV) hgW
        (pairedC3ModuleRestrict M h s) =
      fun b => X.presheaf.map (homOfLE h).op
        (pairedC3FiniteFrameCoordinate g V hV hgV s b) := by
  apply hgW.injective
  change (LinearEquiv.ofBijective (pairedC3FiniteFrameSynthesis g W (h.trans hV)) hgW)
    ((LinearEquiv.ofBijective (pairedC3FiniteFrameSynthesis g W (h.trans hV)) hgW).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  rw [← paired_c3_finite_frame_synthesis_restrict g V W hV h]
  exact congrArg (pairedC3ModuleRestrict M h)
    ((LinearEquiv.ofBijective (pairedC3FiniteFrameSynthesis g V hV) hgV).apply_symm_apply s).symm

/-- A scalar multiplying the old generators multiplies the new coefficients
in the same order. No inversion or choice of unlabelled free frame occurs. -/
theorem paired_c3_finite_frame_coordinate_transition {U T : X.Opens}
    (g : σ → Γ(M, U)) (f : σ → Γ(M, T)) (V : X.Opens)
    (hU : V ≤ U) (hT : V ≤ T)
    (hg : Function.Bijective (pairedC3FiniteFrameSynthesis g V hU))
    (hf : Function.Bijective (pairedC3FiniteFrameSynthesis f V hT))
    (a : Γ(X, V))
    (hgf : ∀ b, pairedC3ModuleRestrict M hU (g b) =
      a • pairedC3ModuleRestrict M hT (f b)) (s : Γ(M, V)) :
    pairedC3FiniteFrameCoordinate f V hT hf s =
      a • pairedC3FiniteFrameCoordinate g V hU hg s := by
  apply hf.injective
  change (LinearEquiv.ofBijective (pairedC3FiniteFrameSynthesis f V hT) hf)
    ((LinearEquiv.ofBijective (pairedC3FiniteFrameSynthesis f V hT) hf).symm s) = _
  rw [LinearEquiv.apply_symm_apply]
  have hs := (LinearEquiv.ofBijective (pairedC3FiniteFrameSynthesis g V hU) hg).apply_symm_apply s
  change (∑ b, pairedC3FiniteFrameCoordinate g V hU hg s b •
    pairedC3ModuleRestrict M hU (g b)) = s at hs
  conv_lhs => rw [← hs]
  change (∑ b : σ, pairedC3FiniteFrameCoordinate g V hU hg s b •
    pairedC3ModuleRestrict M hU (g b)) =
    ∑ b : σ, (a • pairedC3FiniteFrameCoordinate g V hU hg s) b •
      pairedC3ModuleRestrict M hT (f b)
  apply Finset.sum_congr rfl
  intro b _
  rw [hgf, ← mul_smul]
  change (_ * a) • _ = (a * _) • _
  rw [mul_comm]

#print axioms paired_c3_finite_frame_coordinate_restrict
#print axioms paired_c3_finite_frame_coordinate_transition
end HodgeLean.Foundations.Program.G32Native
