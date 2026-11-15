import HodgeLean.Foundations.Program.G32Native.PairedC3LocalModuleComparison

/-! # Comparisons from matching section coordinate transformations -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

variable {X : Scheme.{0}} {M N : X.Modules} {ι σ : Type} {U : ι → X.Opens}

/-- Equal coordinate transition laws identify the original sections on every
common subopen. The scalar is the coefficient transition in the stated order. -/
theorem paired_c3_matching_coordinate_agreement
    (cM : (i : ι) → (V : X.Opens) → V ≤ U i →
      Γ(M, V) ≃ₗ[Γ(X, V)] (σ → Γ(X, V)))
    (cN : (i : ι) → (V : X.Opens) → V ≤ U i →
      Γ(N, V) ≃ₗ[Γ(X, V)] (σ → Γ(X, V)))
    (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j)
    (a : Γ(X, V))
    (hM : ∀ s, cM j V hj s = a • cM i V hi s)
    (hN : ∀ t, cN j V hj t = a • cN i V hi t)
    (s : Γ(M, V)) :
    (cN i V hi).symm (cM i V hi s) =
      (cN j V hj).symm (cM j V hj s) := by
  apply (cN j V hj).injective
  rw [LinearEquiv.apply_symm_apply, hN, LinearEquiv.apply_symm_apply, hM]

/-- Matching natural coordinate systems give a comparison on the specified
cover, retaining all subopens and the original coefficient transition. -/
def pairedC3ComparisonOfMatchingCoordinates
    (cM : (i : ι) → (V : X.Opens) → V ≤ U i →
      Γ(M, V) ≃ₗ[Γ(X, V)] (σ → Γ(X, V)))
    (cN : (i : ι) → (V : X.Opens) → V ≤ U i →
      Γ(N, V) ≃ₗ[Γ(X, V)] (σ → Γ(X, V)))
    (resM : ∀ i V W (h : W ≤ V) (hi : V ≤ U i) s,
      cM i W (h.trans hi) (pairedC3ModuleRestrict M h s) =
        fun b => X.presheaf.map (homOfLE h).op (cM i V hi s b))
    (resN : ∀ i V W (h : W ≤ V) (hi : V ≤ U i) t,
      cN i W (h.trans hi) (pairedC3ModuleRestrict N h t) =
        fun b => X.presheaf.map (homOfLE h).op (cN i V hi t b))
    (a : (i j : ι) → (V : X.Opens) → V ≤ U i → V ≤ U j → Γ(X, V))
    (transM : ∀ i j V hi hj s,
      cM j V hj s = a i j V hi hj • cM i V hi s)
    (transN : ∀ i j V hi hj t,
      cN j V hj t = a i j V hi hj • cN i V hi t) :
    PairedC3LocalModuleComparison M N U where
  equiv i V hi := (cM i V hi).trans (cN i V hi).symm
  restrict i V W h hi s := by
    apply (cN i W (h.trans hi)).injective
    change cN i W (h.trans hi) ((cN i W (h.trans hi)).symm
      (cM i W (h.trans hi) (pairedC3ModuleRestrict M h s))) =
      cN i W (h.trans hi) (pairedC3ModuleRestrict N h
        ((cN i V hi).symm (cM i V hi s)))
    rw [LinearEquiv.apply_symm_apply, resM i V W h hi, resN i V W h hi,
      LinearEquiv.apply_symm_apply]
  agree i j V hi hj s :=
    paired_c3_matching_coordinate_agreement cM cN i j V hi hj
      (a i j V hi hj) (transM i j V hi hj) (transN i j V hi hj) s

#print axioms paired_c3_matching_coordinate_agreement
#print axioms pairedC3ComparisonOfMatchingCoordinates
end HodgeLean.Foundations.Program.G32Native
