import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNInitial
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNStep
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNSplitting

/-! # Route N along the strict prefix of the retained tower -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29

/-- The strict-prefix induction excludes the last blow-up and keeps its
own pair's reduced hyperplane at each preceding step.
Open: uses the three named Route N steps. -/
theorem paired_c3_route_n_stage
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (n : ℕ) (hn : n < R.r) :
    Nonempty (pairedC3StageConormal P ⟨n, by omega⟩ ≅
      pairedC3SplitBundle R.P.k (R.P.k + 1 - R.r + n) (R.r - 1 - n)) := by
  have hrk : R.r ≤ R.P.k + 1 := by
    have h := Fintype.card_le_of_injective _ P.C.residue.indices.injective
    simpa only [Fintype.card_fin] using h
  induction n with
  | zero =>
    have hz : (⟨0, by omega⟩ : Fin (R.r + 1)) = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
    rw [hz]
    simpa only [Nat.add_zero, Nat.sub_zero] using
      paired_c3_route_n_initial_aux R P (by omega)
  | succ n ih =>
    let i : Fin R.r := ⟨n, by omega⟩
    obtain ⟨en⟩ := ih (by omega)
    obtain ⟨E, hE, hqc, hframes, e₁, e₂, _, ⟨e₃⟩⟩ :=
      paired_c3_route_n_step_aux R P i (by dsimp [i]; omega)
    have he₁ : E.X₁ ≅ pairedC3SplitBundle R.P.k
        (R.P.k + 1 - R.r + n) ((R.r - 1 - (n + 1)) + 1) := by
      have hb : R.r - 1 - n = (R.r - 1 - (n + 1)) + 1 := by omega
      exact e₁ ≪≫ en ≪≫ eqToIso (congrArg
        (pairedC3SplitBundle R.P.k (R.P.k + 1 - R.r + n)) hb)
    obtain ⟨es⟩ := paired_c3_route_n_splitting_aux R.P.k
      (R.P.k + 1 - R.r + n) (R.r - 1 - (n + 1)) (by omega) (by omega)
      (P.C.residue.indices i) E hE hqc hframes he₁ e₃
    have ha : R.P.k + 1 - R.r + n + 1 = R.P.k + 1 - R.r + (n + 1) := by omega
    exact ⟨e₂.symm ≪≫ es ≪≫ eqToIso (congrArg
      (fun a => pairedC3SplitBundle R.P.k a (R.r - 1 - (n + 1))) ha)⟩

/-- At stage r−1 the negative-twist summands have all been exchanged.
Open: uses the three named Route N steps through the strict-prefix induction. -/
theorem paired_c3_route_n_penultimate_frame
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (last : Fin R.r) (hlast : last.val + 1 = R.r) :
    Nonempty (pairedC3StageConormal P last.castSucc ≅
      (SheafOfModules.free (Fin R.P.k) : (pairedC3Proj R.P.k).Modules)) := by
  have hrk : R.r ≤ R.P.k + 1 := by
    have h := Fintype.card_le_of_injective _ P.C.residue.indices.injective
    simpa only [Fintype.card_fin] using h
  have hzero : R.r - 1 - last.val = 0 := by omega
  have hrank : R.P.k + 1 - R.r + last.val = R.P.k := by omega
  have hindex : (⟨last.val, by omega⟩ : Fin (R.r + 1)) = last.castSucc :=
    Fin.ext rfl
  have h := paired_c3_route_n_stage R P last.val last.isLt
  rw [hindex, hzero, hrank] at h
  exact h

end HodgeLean.Foundations.Program.G32Native
