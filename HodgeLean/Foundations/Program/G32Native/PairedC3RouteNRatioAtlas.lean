import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNRulingParameters
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineRatioData

/-! # The supplied data underlying the selected local ratio maps -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

attribute [local instance] G32JointSlicedComponent.sliceImmersion
open HodgeLean.Foundations.Program.G32Native



open AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A cover storing only the local equations and their specified maps.
There is no overlap, smoothness or marked-square assertion in these data. -/
structure PairedC3RouteNRatioAtlas {X Q : Scheme} (Y : Over (Spec ↧ℂ))
    (p : Y.left ⟶ X) (i : Q ⟶ X) (D₀ D₁ : X.IdealSheafData) where
  Index : Type
  chart : Index → PairedC3AffineRatioData Y p i D₀ D₁
  covers : (⨆ j, (((D₀ ⊔ D₁) ⊔ i.ker).comap p).subschemeι ⁻¹ᵁ (chart j).V.1) = ⊤

/-- Retain the actual selected Rees equations together with their entire
normalized residual cover.
Source: Hartshorne, Algebraic Geometry, II.3 and II.7.13. -/
def pairedC3RouteNRatioAtlas
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    PairedC3RouteNRatioAtlas (P.T.B i.succ) (P.T.b i).left
      (P.C.slices i.castSucc).left
      (P.T.D i.castSucc ⟨2 * i.val, by omega⟩)
      (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩) := by
  classical
  let A := pairedC3RouteNRulingParameters R P i
  let U := A.U
  let V := A.V
  let u := A.u
  let v := A.v
  let α := A.α
  let h₀ := A.h₀
  let h₁ := A.h₁
  let s := A.s
  let t := A.t
  let hdata := A.equations
  let ht := A.covers
  let idx := {x : ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ) //
      x ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support}
  let C : idx × Fin 2 → PairedC3AffineRatioData (P.T.B i.succ) (P.T.b i).left
      (P.C.slices i.castSucc).left
      (P.T.D i.castSucc ⟨2 * i.val, by omega⟩)
      (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩) := by
    rintro ⟨x, k⟩
    refine Fin.cases ?_ (fun l => ?_) k
    · refine ⟨U x, V x 0, h₀ x, u x, v x, α x, 0, s x,
        (hdata x).1, (hdata x).2.1, ?_, (hdata x).2.2.2.2.1, ?_⟩
      · rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
        exact (hdata x).2.2.1
      · exact (hdata x).2.2.2.2.2.1
    · have hl : l = 0 := Subsingleton.elim _ _
      subst l
      refine ⟨U x, V x 1, h₁ x, u x, v x, α x, 1, t x,
        (hdata x).1, (hdata x).2.1, ?_, (hdata x).2.2.2.2.1, ?_⟩
      · rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
        exact (hdata x).2.2.1
      · exact (hdata x).2.2.2.2.2.2.1

  refine ⟨idx × Fin 2, C, ?_⟩
  have hCV (j : idx × Fin 2) : (C j).V = V j.1 j.2 := by
    rcases j with ⟨x, k⟩
    fin_cases k <;> rfl
  simp_rw [hCV]
  exact ht

#print axioms pairedC3RouteNRatioAtlas
end HodgeLean.Foundations.Program.ResidueSelected
