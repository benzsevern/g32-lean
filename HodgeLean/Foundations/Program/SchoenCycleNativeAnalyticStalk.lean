import HodgeLean.Foundations.Program.SchoenCycleNativeAnalyticSections

/-! # The actual stalk map to native analytic germs -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Compatible centered-chart section evaluations induce a ring map from
an actual algebraic stalk to the native analytic germ ring.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6;
Mathlib, TopCat.Presheaf.stalk. -/
def s2e_stalk_nativeAnalyticGerm
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) :
    X.left.presheaf.stalk p.underlying →+* s2e_nativeAnalyticGermRing d := by
  refine (colimit.desc ((OpenNhds.inclusion p.underlying).op ⋙ X.left.presheaf)
    { pt := CommRingCat.of (s2e_nativeAnalyticGermRing d)
      ι := { app := fun U =>
               CommRingCat.ofHom
                 (s2e_regularSection_nativeAnalyticGerm X d p U.unop.1 U.unop.2)
             naturality := ?_ } }).hom
  intro U V f
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  exact (s2e_regularSection_nativeAnalyticGerm_restrict X d p
    U.unop.1 V.unop.1 f.unop.le V.unop.2 s).symm

#print axioms s2e_stalk_nativeAnalyticGerm
/-- The actual stalk comparison sends each algebraic section germ to its
centered-chart analytic germ.
Source: Mathlib, CategoryTheory.Limits.colimit.ι_desc. -/
theorem s2e_stalk_nativeAnalyticGerm_germ
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U)
    (s : Γ(X.left, U)) :
    s2e_stalk_nativeAnalyticGerm X d p (X.left.presheaf.germ U p.underlying hp s) =
      s2e_regularSection_nativeAnalyticGerm X d p U hp s := by
  change (X.left.presheaf.germ U p.underlying hp ≫
    CommRingCat.ofHom (s2e_stalk_nativeAnalyticGerm X d p)) s = _
  simp only [TopCat.Presheaf.germ, s2e_stalk_nativeAnalyticGerm,
    CommRingCat.ofHom_hom, colimit.ι_desc]
  rfl

#print axioms s2e_stalk_nativeAnalyticGerm_germ
/-- Evaluation at the origin after the native analytic comparison agrees
with the residue evaluation of the actual algebraic stalk.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6. -/
theorem s2e_stalk_nativeAnalyticGerm_value
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (a : X.left.presheaf.stalk p.underlying) :
    s2e_nativeAnalyticGerm_value d (s2e_stalk_nativeAnalyticGerm X d p a) =
      p.stalkHom a := by
  obtain ⟨U, hp, s, rfl⟩ := X.left.presheaf.exists_germ_eq a
  rw [s2e_stalk_nativeAnalyticGerm_germ, s2e_regularSection_nativeAnalyticGerm_value]
  simp only [Point.evaluate, dif_pos hp]

#print axioms s2e_stalk_nativeAnalyticGerm_value
/-- The actual algebraic-to-native-analytic stalk comparison reflects units.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6. -/
instance s2e_stalk_nativeAnalyticGerm_isLocalHom
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) : IsLocalHom (s2e_stalk_nativeAnalyticGerm X d p) where
  map_nonunit a ha := by
    have hv := (s2e_nativeAnalyticGerm_isUnit_iff_value_ne_zero d _).mp ha
    rw [s2e_stalk_nativeAnalyticGerm_value] at hv
    exact isUnit_of_map_unit p.stalkHom.hom a (isUnit_iff_ne_zero.mpr hv)

#print axioms s2e_stalk_nativeAnalyticGerm_isLocalHom
end HodgeLean.Foundations.Program
