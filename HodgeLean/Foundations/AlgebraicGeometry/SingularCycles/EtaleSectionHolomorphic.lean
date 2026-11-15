import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.EtaleSectionRegular

/-! # Holomorphic local sections of étale maps

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open Set Filter Topology HodgeLean.Foundations.Analytic
namespace AlgebraicGeometry.SingularCycles

/-- Continuous local sections of étale maps preserve all holomorphic functions in F4.
Source: SGA 1, Exposé XII, §1; standard étale presentations and reduced analytic atlases. -/
theorem etale_section_holFun {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (f : X ⟶ Z) [Etale f.left] {U : Set (ComplexPoint Z)} (hU : IsOpen U)
    (s : U → ComplexPoint X) (hs : Continuous s)
    (hsection : ∀ y, Point.map f (s y) = (y : ComplexPoint Z))
    {D : Set (ComplexPoint X)} (g : D → ℂ) (hg : (f4_analytification X).IsHolFun g)
    (hsD : ∀ y, s y ∈ D) :
    (f4_analytification Z).IsHolFun (fun y => g ⟨s y, hsD y⟩) := by
  apply holFun_of_local (f4_analytification Z)
  intro x
  obtain ⟨j, hxj⟩ := (f4_analytification X).atlas.covers (s x)
  let c := (f4_analytification X).atlas.chart j
  obtain ⟨N, hNo, hxN, G, hG, hgeq⟩ := hg ⟨s x, hsD x⟩ j hxj
  obtain ⟨R, hR, hRo, hxR⟩ := eventually_nhds_iff.mp hG.eventually_analyticAt
  let C : Set (ComplexPoint X) := N ∩ (c.dom ∩ c.toFun ⁻¹' R)
  have hCo : IsOpen C := hNo.inter
    ((anb_continuousOn_toFun c).isOpen_inter_preimage c.isOpen_dom hRo)
  have hxC : s x ∈ C := ⟨hxN, hxj, hxR⟩
  let W : Set U := s ⁻¹' C
  let V : Set (ComplexPoint Z) := Subtype.val '' W
  have hVU : V ⊆ U := fun z ⟨z', _, heq⟩ => heq ▸ z'.2
  have hVo : IsOpen V := hU.isOpenMap_subtype_val W (hCo.preimage hs)
  have hxV : (x : ComplexPoint Z) ∈ V := ⟨x, hxC, rfl⟩
  refine ⟨V, hVU, hVo, hxV, ?_⟩
  let sV : V → ComplexPoint X := fun y => s ⟨y, hVU y.2⟩
  have hsV : Continuous sV := hs.comp (continuous_subtype_val.subtype_mk fun y => hVU y.2)
  have hsVC : ∀ y : V, sV y ∈ C := by
    intro y
    obtain ⟨y', hy', heq⟩ := y.2
    have hyy : (⟨y, hVU y.2⟩ : U) = y' := Subtype.ext heq.symm
    change s ⟨y, hVU y.2⟩ ∈ C
    rw [hyy]
    exact hy'
  have hcoords : ∀ k, (f4_analytification Z).IsHolFun (fun y : V => c.toFun (sV y) k) := by
    intro k
    change (f4_analytification Z).IsHolFun
      (fun y : V => Point.evaluate j.1.U.1 (j.1.coord k) (sV y))
    exact etale_section_regular_evaluation f hVo sV hsV
      (fun y => hsection ⟨y, hVU y.2⟩) j.1.U.1
      (fun y => (hsVC y).2.1) (j.1.coord k)
  have hcomp := holFun_analytic_comp (f4_analytification Z)
    (fun y : V => c.toFun (sV y)) hcoords G (fun y => hR _ (hsVC y).2.2)
  have heq : (fun y : V => g ⟨sV y, hsD ⟨y, hVU y.2⟩⟩) =
      (fun y : V => G (c.toFun (sV y))) := by
    funext y
    exact hgeq ⟨sV y, hsD ⟨y, hVU y.2⟩⟩ ⟨(hsVC y).1, (hsVC y).2.1⟩
  change (f4_analytification Z).IsHolFun
    (fun y : V => g ⟨sV y, hsD ⟨y, hVU y.2⟩⟩)
  rw [heq]
  exact hcomp

end AlgebraicGeometry.SingularCycles
