import HodgeLean.Foundations.Program.SchoenTowerL1aIdealOpenRestriction
import HodgeLean.Foundations.Program.SchoenTowerL1bAffineGeneratorRefinement
import Mathlib.Topology.Bases

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An affine coordinate neighborhood can be refined to avoid every absent ideal in a finite family. -/
theorem s2v_l1b_absent_branch_refinement
    (X : Over (Spec ↧ℂ)) {ι κ : Type} [Fintype κ]
    (I : κ → X.left.IdealSheafData) (p : ComplexPoint X)
    (U : X.left.affineOpens) (hp : p.underlying ∈ U.1)
    (z : ι → Γ(X.left, U))
    (hEt : (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ U.1 le_top).hom z).Etale) :
    ∃ (V : X.left.affineOpens) (hV : V.1 ≤ U.1),
      p.underlying ∈ V.1 ∧
      (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ V.1 le_top).hom
        (fun i => (X.left.presheaf.map (homOfLE hV).op).hom (z i))).Etale ∧
      ∀ t, p.underlying ∉ (I t).support → (I t).ideal V = ⊤ := by
  classical
  let A := {t : κ // p.underlying ∉ (I t).support}
  let O : X.left.Opens := U.1 ⊓ ⨅ t : A, ⟨((I t.val).support : Set X.left)ᶜ, (I t.val).support.isClosed.isOpen_compl⟩
  have hpO : p.underlying ∈ O := by
    refine ⟨hp, ?_⟩
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr (fun t => t.property)
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hpV, hVO⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open hpO O.2
  let V : X.left.affineOpens := ⟨V₀, hV₀⟩
  have hVU : V.1 ≤ U.1 := hVO.trans inf_le_left
  refine ⟨V, hVU, hpV, s2v_l1b_affine_coordinate_restriction X U V hVU z hEt, ?_⟩
  intro t ht
  have hdis : ∀ y : V.1.toScheme, y.val ∉ (I t).support := by
    intro y
    have hy : y.val ∈ O := hVO y.property
    have H := hy.2
    rw [TopologicalSpace.Opens.coe_iInf] at H
    exact (Set.mem_iInter.mp H) ⟨t, ht⟩
  have hsupport : ((I t).comap V.1.ι).support = ⊥ := by
    rw [Scheme.IdealSheafData.support_comap]
    ext y
    exact iff_false_intro (hdis y)
  have htop := (Scheme.IdealSheafData.support_eq_bot_iff _).mp hsupport
  have H := congrArg (fun J : V.1.toScheme.IdealSheafData =>
    J.ideal ⟨⊤, @isAffineOpen_top _ V.2⟩) htop
  rw [s2v_l1a_open_ideal_top] at H
  let e := V.1.topIso.symm.commRingCatIsoToRingEquiv
  have H' := congrArg (Ideal.map e.symm.toRingHom) H
  change Ideal.map e.symm.toRingHom (((I t).ideal V).comap e.symm.toRingHom) =
    Ideal.map e.symm.toRingHom ⊤ at H'
  rw [Ideal.map_comap_of_surjective e.symm.toRingHom e.symm.surjective,
    Ideal.map_top] at H'
  exact H'

end HodgeLean.Foundations.Program
