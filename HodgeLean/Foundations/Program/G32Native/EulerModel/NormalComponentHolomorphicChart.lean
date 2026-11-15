import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalNativePointSupport

/-! # The actual native point chart on the specified component -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Program HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual native holomorphic point chart transported through the specified component isomorphism. -/
def normalComponentPointChart
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :
    OpenPartialHomeomorph (ComplexPoint Q) ((Fin 0 → ℂ) × (Fin k → ℂ)) :=
  (Point.isoMapHomeomorph eQ).toOpenPartialHomeomorph.trans (normalSchemePointChart k)

/-- The transported native point chart retains the exact original normal parameters. -/
theorem normalComponentPointChart_param
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (z : Fin k → ℂ) :
    normalComponentPointChart k eQ
      (normalComponentHomeomorph k eQ (normalProjectiveChart k z)) = (0, z) := by
  change normalSchemePointChart k
    (Point.map eQ.hom (normalComponentHomeomorph k eQ (normalProjectiveChart k z))) = (0, z)
  have he : Point.map eQ.hom
      (normalComponentHomeomorph k eQ (normalProjectiveChart k z)) =
        normalSchemeAffineParam k z := by
    exact (Point.isoMapHomeomorph eQ.symm).symm_apply_apply _
  rw [he, normalSchemePointChart_param]

#print axioms normalComponentPointChart
#print axioms normalComponentPointChart_param
/-- The transported point chart retains the exact inverse image of the native chart source. -/
theorem normalComponentPointChart_source
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :
    (normalComponentPointChart k eQ).source =
      Point.map eQ.hom ⁻¹' (normalSchemePointChart k).source := by
  simp only [normalComponentPointChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.univ_inter]
  rfl

#print axioms normalComponentPointChart_source
/-- The same actual chart on the selected component satisfies the native holomorphic chart predicate. -/
theorem normalComponentPointChart_holomorphic
    {Q : Over (Spec ↧ℂ)} [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
    (k : ℕ) (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :
    a3b4_IsHolChart Q.hom (normalComponentPointChart k eQ) := by
  haveI : LocallyOfFiniteType (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) := by
    change LocallyOfFiniteType (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom
    rw [← Over.w eQ.inv]
    infer_instance
  haveI : QuasiCompact (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) := by
    change QuasiCompact (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom
    rw [← Over.w eQ.inv]
    infer_instance
  haveI : IsSeparated (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) := by
    change IsSeparated (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom
    rw [← Over.w eQ.inv]
    infer_instance
  constructor
  · intro j
    exact j.elim0
  · intro j
    have hpull := (f4_map_isHom eQ.hom).2 (normalSchemePointChart k).source
      (normalSchemePointChart k).open_source
      (fun q : (normalSchemePointChart k).source => (normalSchemePointChart k q).2 j)
      ((normalSchemePointChart_holomorphic k).2 j)
    have hsub : (normalComponentPointChart k eQ).source ⊆
        Point.map eQ.hom ⁻¹' (normalSchemePointChart k).source := by
      rw [normalComponentPointChart_source]
    exact anb_isHolFun_restrict (f4_analytification Q).atlas hsub hpull

#print axioms normalComponentPointChart_holomorphic
/-- The actual native chart on the selected component has exactly its literal coordinate-point cycle as zero support. -/
theorem normalComponentPointChart_support
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left]
    (q : ComplexPoint Q) (hq : q ∈ (normalComponentPointChart k eQ).source) :
    q ∈ a3b4_cycleSupport Q.hom (s2e_componentCycle (s2c_subschemeι Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) ↔
      (normalComponentPointChart k eQ q).2 = 0 := by
  rw [normalComponentPointChart_source, normalSchemePointChart_source,
    normalSchemeAffineChart_source] at hq
  obtain ⟨z, hz⟩ := hq
  have he : normalComponentHomeomorph k eQ (normalProjectiveChart k z) = q := by
    apply (Point.isoMapHomeomorph eQ).injective
    change Point.map eQ.hom (normalComponentHomeomorph k eQ (normalProjectiveChart k z)) = _
    have hc : Point.map eQ.hom
        (normalComponentHomeomorph k eQ (normalProjectiveChart k z)) =
          normalSchemeAffineParam k z := by
      exact (Point.isoMapHomeomorph eQ.symm).symm_apply_apply _
    rw [hc]
    exact hz
  rw [← he, normalComponentPointChart_param]
  exact (normalComponentHomeomorph_cycle_support k eQ (normalProjectiveChart k z)).trans
    (normalProjectiveChart_eq_base_iff k z)

#print axioms normalComponentPointChart_support
end HodgeLean.Foundations.Program.G32Native.EulerModel
