import HodgeLean.Foundations.Program.G32Native.PairedBlowupIteration
import HodgeLean.Foundations.Program.SchoenTowerConormalDefs

/-! Regularity induction on T5's actual stages, with no new tower choices. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem joint_paired_stages_regularity
    (hstep :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Over (Spec ↧ℂ))
    [Smooth B.hom] [IsProjective B.hom] [IsIntegral B.left]
    (D : ι → B.left.IdealSheafData) (u v : ι) (huv : u ≠ v)
    (hintersections : ∀ J : Finset ι,
      Smooth (s2c_subscheme B (J.sup D)).hom ∧
      ∀ x : (s2c_subscheme B (J.sup D)).left,
        ∃ U : (s2c_subscheme B (J.sup D)).left.Opens, x ∈ U ∧
          Nonempty (Scheme.Modules.restrict
            (s2c_conormal (s2c_subschemeι B (J.sup D)).left) U.ι ≅
            (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) :
              U.toScheme.Modules))),
    let K := D u ⊔ D v
    let B' : Over (Spec ↧ℂ) := Over.mk (K.blowUpπ ≫ B.hom)
    let D' := fun j => s2c_strictTransform K.blowUpπ (D j) K
    (Smooth B'.hom ∧ IsProjective B'.hom ∧ IsIntegral B'.left) ∧
    ∀ J : Finset ι,
      Smooth (s2c_subscheme B' (J.sup D')).hom ∧
      ∀ x : (s2c_subscheme B' (J.sup D')).left,
        ∃ U : (s2c_subscheme B' (J.sup D')).left.Opens, x ∈ U ∧
          Nonempty (Scheme.Modules.restrict
            (s2c_conormal (s2c_subschemeι B' (J.sup D')).left) U.ι ≅
            (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) :
              U.toScheme.Modules)) )
    {r : ℕ}
    (A : g32t5_BranchStage (Spec ↧ℂ) r)
    (hbase : Smooth A.1.hom ∧ IsProjective A.1.hom ∧ IsIntegral A.1.left)
    (hintersections : ∀ J : Finset (Fin (2 * r)),
      Smooth (s2c_subscheme A.1 (J.sup A.2)).hom ∧
      ∀ x : (s2c_subscheme A.1 (J.sup A.2)).left,
        ∃ U : (s2c_subscheme A.1 (J.sup A.2)).left.Opens, x ∈ U ∧
          Nonempty (Scheme.Modules.restrict
            (s2c_conormal (s2c_subschemeι A.1 (J.sup A.2)).left) U.ι ≅
            (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) :
              U.toScheme.Modules))) :
    ∀ i : Fin (r + 1),
      let C := g32t5_stages A i
      (Smooth C.1.hom ∧ IsProjective C.1.hom ∧ IsIntegral C.1.left) ∧
      ∀ J : Finset (Fin (2 * r)),
        Smooth (s2c_subscheme C.1 (J.sup C.2)).hom ∧
        ∀ x : (s2c_subscheme C.1 (J.sup C.2)).left,
          ∃ U : (s2c_subscheme C.1 (J.sup C.2)).left.Opens, x ∈ U ∧
            Nonempty (Scheme.Modules.restrict
              (s2c_conormal (s2c_subschemeι C.1 (J.sup C.2)).left) U.ι ≅
              (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) :
                U.toScheme.Modules)) := by
  intro i
  induction i using Fin.induction with
  | zero =>
    simp only [g32t5_stages, Fin.induction_zero]
    exact ⟨hbase, hintersections⟩
  | succ i ih =>
    rw [g32t5_stages_succ]
    generalize hC : g32t5_stages A i.castSucc = C at ih ⊢
    haveI := ih.1.1
    haveI := ih.1.2.1
    haveI := ih.1.2.2
    exact hstep C.1 C.2
      ⟨2 * i.val, by omega⟩ ⟨2 * i.val + 1, by omega⟩
      (by intro h; have := congrArg Fin.val h; dsimp at this; omega) ih.2

#print axioms joint_paired_stages_regularity
end HodgeLean.Foundations.Program
