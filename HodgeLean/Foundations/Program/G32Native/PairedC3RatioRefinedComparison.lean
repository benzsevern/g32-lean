import HodgeLean.Foundations.Program.G32Native.PairedC3RatioParameterRestriction
import HodgeLean.Foundations.Program.G32Native.PairedC3AmbientSliceRegular

/-! # Comparing the chosen ratios on simultaneous affine refinements -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native

/-- A chosen generator still generates the original ideal on an affine
restriction. -/
theorem pairedC3_affine_generator_restriction
    {X : Scheme} (D : X.IdealSheafData) (U W : X.affineOpens) (hWU : W.1 ≤ U.1)
    (u : Γ(X, U)) (hu : D.ideal U = Ideal.span {u}) :
    D.ideal W = Ideal.span {(X.presheaf.map (homOfLE hWU).op).hom u} := by
  have h := D.map_ideal (U := W) (V := U) hWU
  rw [hu, Ideal.map_span, Set.image_singleton] at h
  exact h.symm

namespace PairedC3AffineRatioData
variable {X Q : Scheme} {Y : Over (Spec ↧ℂ)} {p : Y.left ⟶ X} {i : Q ⟶ X}
  {D₀ D₁ : X.IdealSheafData}

/-- Two supplied charts agree on a simultaneous affine refinement of their
base opens and source opens. Both original normalization units are retained. -/
theorem refined_comparison [IsIntegral X] [IsIntegral Q] [IsIntegral Y.left]
    [IsClosedImmersion i] [IsDominant p] [QuasiCompact p]
    (hproper₀ : (D₀.comap i).support ≠ ⊤) (hproper₁ : (D₁.comap i).support ≠ ⊤)
    (A B : PairedC3AffineRatioData Y p i D₀ D₁)
    (U : X.affineOpens) (W : Y.left.affineOpens)
    [Nonempty (i ⁻¹ᵁ U.1)] [Nonempty W.1]
    (hUA : U.1 ≤ A.U.1) (hUB : U.1 ≤ B.U.1)
    (hWA : W.1 ≤ A.V.1) (hWB : W.1 ≤ B.V.1) (hW : W.1 ≤ p ⁻¹ᵁ U.1) :
    Spec.map (CommRingCat.ofHom (pairedC3AffineResidualRestriction
      (((D₀ ⊔ D₁) ⊔ i.ker).comap p) A.V W hWA)) ≫ A.map.left =
    Spec.map (CommRingCat.ofHom (pairedC3AffineResidualRestriction
      (((D₀ ⊔ D₁) ⊔ i.ker).comap p) B.V W hWB)) ≫ B.map.left := by
  let D := (D₀ ⊔ D₁) ⊔ i.ker
  let M := D.comap p
  let rA := (X.presheaf.map (homOfLE hUA).op).hom
  let rB := (X.presheaf.map (homOfLE hUB).op).hom
  let sA := (Y.left.presheaf.map (homOfLE hWA).op).hom
  let sB := (Y.left.presheaf.map (homOfLE hWB).op).hom
  let f := (p.appLE U.1 W.1 hW).hom
  let q := Ideal.Quotient.mk (M.ideal W)
  let FA := pairedC3AffineResidualCoefficient p D A.U W (hWA.trans A.liesOver)
  let FB := pairedC3AffineResidualCoefficient p D B.U W (hWB.trans B.liesOver)
  let βA := Units.map FA.toMonoidHom A.unit.unit
  let βB := Units.map FB.toMonoidHom B.unit.unit
  have genA₀ := pairedC3_affine_generator_restriction D₀ A.U U hUA A.u A.ideal₀
  have genA₁ := pairedC3_affine_generator_restriction D₁ A.U U hUA A.v A.ideal₁
  have genB₀ := pairedC3_affine_generator_restriction D₀ B.U U hUB B.u B.ideal₀
  have genB₁ := pairedC3_affine_generator_restriction D₁ B.U U hUB B.v B.ideal₁
  have hu := pairedC3_ambient_branch_regular_near_slice i D₀ hproper₀ U (rA A.u) genA₀
  have hv := pairedC3_ambient_branch_regular_near_slice i D₁ hproper₁ U (rA A.v) genA₁
  have huf := pairedC3_dominant_affine_coefficient_regular p U W hW (rA A.u) hu
  have hvf := pairedC3_dominant_affine_coefficient_regular p U W hW (rA A.v) hv
  have hqu := pairedC3_slice_quotient_branch_regular i D₀ hproper₀ U (rA A.u) genA₀
  have hu' : Ideal.span {rA A.u} = Ideal.span {rB B.u} := genA₀.symm.trans genB₀
  have hv' : Ideal.span {rA A.v} = Ideal.span {rB B.v} := genA₁.symm.trans genB₁
  have hαA : rA A.v - rA A.α * rA A.u ∈ i.ker.ideal U := by
    rw [← map_mul, ← map_sub]
    exact i.ker.ideal_le_comap_ideal hUA A.slice
  have hαB : rB B.v - rB B.α * rB B.u ∈ i.ker.ideal U := by
    rw [← map_mul, ← map_sub]
    exact i.ker.ideal_le_comap_ideal hUB B.slice
  have natA (a : Γ(X, A.U)) : sA ((p.appLE A.U.1 A.V.1 A.liesOver).hom a) = f (rA a) :=
    congrArg (fun F => F a) (pairedC3_affine_overlap_coefficient_square p A.U.1 U.1
      A.V.1 W.1 hUA hWA A.liesOver hW)
  have natB (a : Γ(X, B.U)) : sB ((p.appLE B.U.1 B.V.1 B.liesOver).hom a) = f (rB a) :=
    congrArg (fun F => F a) (pairedC3_affine_overlap_coefficient_square p B.U.1 U.1
      B.V.1 W.1 hUB hWB B.liesOver hW)
  have htA : if A.k = 0 then f (rA A.u) = sA A.t * f (rA A.v)
      else f (rA A.v) = sA A.t * f (rA A.u) := by
    by_cases hk : A.k = 0
    · have hre := A.rees
      rw [ite_eq_left hk] at hre
      simpa only [hk, ite_true, map_mul, natA] using congrArg sA hre
    · have hre := A.rees
      rw [ite_eq_right hk] at hre
      simpa only [hk, ite_false, map_mul, natA] using congrArg sA hre
  have htB : if B.k = 0 then f (rB B.u) = sB B.t * f (rB B.v)
      else f (rB B.v) = sB B.t * f (rB B.u) := by
    by_cases hk : B.k = 0
    · have hre := B.rees
      rw [ite_eq_left hk] at hre
      simpa only [hk, ite_true, map_mul, natB] using congrArg sB hre
    · have hre := B.rees
      rw [ite_eq_right hk] at hre
      simpa only [hk, ite_false, map_mul, natB] using congrArg sB hre
  have hI : i.ker.ideal U ≤ RingHom.ker (q.comp f) := by
    intro a ha
    change pairedC3AffineResidualCoefficient p D U W hW
      (Ideal.Quotient.mk (D.ideal U) a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ((le_sup_right : i.ker ≤ D) U ha), map_zero]
  have hβA : (βA : Γ(Y.left, W) ⧸ M.ideal W) = q (f (rA A.α)) := by
    change FA (A.unit.unit : Γ(X, A.U) ⧸ D.ideal A.U) = _
    rw [IsUnit.unit_spec]
    change q ((p.appLE A.U.1 W.1 (hWA.trans A.liesOver)).hom A.α) = _
    exact congrArg q (congrArg (fun F => F.hom A.α)
      (p.map_appLE hW (homOfLE hUA).op)).symm
  have hβB : (βB : Γ(Y.left, W) ⧸ M.ideal W) = q (f (rB B.α)) := by
    change FB (B.unit.unit : Γ(X, B.U) ⧸ D.ideal B.U) = _
    rw [IsUnit.unit_spec]
    change q ((p.appLE B.U.1 W.1 (hWB.trans B.liesOver)).hom B.α) = _
    exact congrArg q (congrArg (fun F => F.hom B.α)
      (p.map_appLE hW (homOfLE hUB).op)).symm
  rw [A.map_restriction W hWA, B.map_restriction W hWB,
    A.parameter_restriction W hWA, B.parameter_restriction W hWB]
  letI := pairedC3SpecAlgebra (M.subschemeCover.f W ≫ M.subschemeι ≫ Y.hom)
  simp only [apply_ite]
  change (projectiveLineChart A.k ((if A.k = 0 then ↑βA else ↑βA⁻¹) * q (sA A.t))).left =
    (projectiveLineChart B.k ((if B.k = 0 then ↑βB else ↑βB⁻¹) * q (sB B.t))).left
  exact congrArg Over.Hom.left (pairedC3_projective_generator_overlap (i.ker.ideal U) f q hI
    (rA A.u) (rA A.v) (rB B.u) (rB B.v) (rA A.α) (rB B.α)
    (sA A.t) (sB B.t) A.k B.k hu hv huf hvf hqu hu' hv' htA htB
    hαA hαB βA βB hβA hβB).symm

end PairedC3AffineRatioData
#print axioms pairedC3_affine_generator_restriction
#print axioms PairedC3AffineRatioData.refined_comparison
end HodgeLean.Foundations.Program.G32Native
