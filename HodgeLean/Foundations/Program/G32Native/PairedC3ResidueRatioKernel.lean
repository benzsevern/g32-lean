import HodgeLean.Foundations.Program.G32Native.PairedC3ResidueCoordinates

/-! # Retained ratio equations on the full residue hyperplane -/

noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native
variable {K : Type*} [Field K] {s : ℕ}

/-- The first s ratio equations, with the last pair omitted. -/
def pairedC3RetainedRatioEquations (t : Fin s → K) :
    pencilResidueSpace K (s + 1) →ₗ[K] (Fin s → K) where
  toFun v i := (v.val i.castSucc).1 - t i * (v.val i.castSucc).2
  map_add' v w := by
    funext i
    change ((v.val i.castSucc).1 + (w.val i.castSucc).1) -
      t i * ((v.val i.castSucc).2 + (w.val i.castSucc).2) =
      ((v.val i.castSucc).1 - t i * (v.val i.castSucc).2) +
      ((w.val i.castSucc).1 - t i * (w.val i.castSucc).2)
    ring
  map_smul' c v := by
    funext i
    change c * (v.val i.castSucc).1 - t i * (c * (v.val i.castSucc).2) =
      c * ((v.val i.castSucc).1 - t i * (v.val i.castSucc).2)
    ring

/-- Arbitrary retained ratios leave the positive residues and one
last-pair residue as independent coordinates in the full residue space.
Source: Schoen, Compositio Mathematica 65 (1988), proof of Lemma 2.4,
first r−1 pencil equations on the fixed full linear system. -/
def pairedC3ResidueRatioKernelEquiv (t : Fin s → K) :
    LinearMap.ker (pairedC3RetainedRatioEquations t) ≃ₗ[K]
      ((Fin s → K) × K) where
  toFun v := ((pairedC3ResidueCoordinates s v.val).2)
  invFun a := ⟨(pairedC3ResidueCoordinates s).symm
      (fun i => t i * a.1 i, a), by
    change pairedC3RetainedRatioEquations t _ = 0
    funext i
    simp [pairedC3RetainedRatioEquations, pairedC3ResidueCoordinates]⟩
  left_inv v := by
    apply Subtype.ext
    apply (pairedC3ResidueCoordinates s).injective
    rw [LinearEquiv.apply_symm_apply]
    refine Prod.ext ?_ (by rfl)
    funext i
    have h := congrFun v.property i
    change (v.val.val i.castSucc).1 - t i * (v.val.val i.castSucc).2 = 0 at h
    exact (sub_eq_zero.mp h).symm
  right_inv a := congrArg Prod.snd ((pairedC3ResidueCoordinates s).apply_symm_apply _)
  map_add' v w := rfl
  map_smul' c v := rfl

/-- Every retained equation can be varied independently even with the
total residue constrained to zero. -/
theorem paired_c3_retained_ratio_surjective (t : Fin s → K) :
    Function.Surjective (pairedC3RetainedRatioEquations t) := by
  intro a
  refine ⟨(pairedC3ResidueCoordinates s).symm (a, (0, 0)), ?_⟩
  funext i
  simp [pairedC3RetainedRatioEquations, pairedC3ResidueCoordinates]

/-- The full residue kernel has one coordinate per marked pair. -/
theorem paired_c3_residue_ratio_kernel_finrank (t : Fin s → K) :
    Module.finrank K (LinearMap.ker (pairedC3RetainedRatioEquations t)) = s + 1 := by
  rw [(pairedC3ResidueRatioKernelEquiv t).finrank_eq,
    Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]

#print axioms pairedC3RetainedRatioEquations
#print axioms pairedC3ResidueRatioKernelEquiv
#print axioms paired_c3_retained_ratio_surjective
#print axioms paired_c3_residue_ratio_kernel_finrank
end HodgeLean.Foundations.Program.G32Native
