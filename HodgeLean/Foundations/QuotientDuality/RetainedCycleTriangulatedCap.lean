import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothGenericNeighborhood
import HodgeLean.Foundations.RationalHomologyManifold.Basic
import HodgeLean.Foundations.QuotientDuality.RetainedCycleMiddleCapPerfect
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveMarkedTriangulation

/-! # Actual middle cap duality from the existing finite triangulated duality

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- A global class with generating and concentrated localizations gives the existing coherent local orientation. -/
def retainedGlobalLocalOrientation (X : TopCat.{0}) (n : ℕ)
    (c : Homology ℚ X n)
    (ho : ∀ x, Function.Bijective (orientationLine X n c x))
    (hv : ∀ j : ℕ, j ≠ n → ∀ x : X, Subsingleton (orientationGroup X j x)) :
    LocalRationalOrientation X n where
  generator := localOrientation X n c
  generates := ho
  vanishes := fun x j hj => hv j hj x
  coherent := by
    intro x
    refine ⟨⊤, Set.mem_univ x,
      (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) (((⊤ : TopologicalSpace.Opens X) : Set X)ᶜ)) n).hom c, ?_⟩
    intro y hy
    have h := relativeHomologyProjection_map n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hy)) c
    have hid : homologyMap ℚ n
        (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hy)).hom.right c = c := by
      change homologyMap ℚ n (𝟙 X) c = c
      exact LinearMap.congr_fun (homologyMap_id ℚ X n) c
    exact h.trans (congrArg (relativeHomologyProjection ℚ (pointComplementPair y) n).hom hid)

/-- The existing triangulated cap map is the actual retained cap map in the same degree. -/
theorem retained_cap_eq_localTraceCap (X : TopCat.{0}) (p q : ℕ)
    (c : Homology ℚ X (p + q)) :
    retainedCapWithOrientation X p q c = localTraceCap X p q c := rfl


/-- Finite triangulated duality applies to the specified global orientation without a replacement cap map. -/
theorem retained_triangulated_cap_bijective (X : TopCat.{0})
    [CompactSpace X] [T2Space X] [ConnectedSpace X]
    (t : HodgeLean.Foundations.RationalHomologyManifold.FiniteTriangulation X)
    (p q : ℕ) (c : Homology ℚ X (p + q))
    (ho : ∀ x, Function.Bijective (orientationLine X (p + q) c x))
    (hv : ∀ j : ℕ, j ≠ p + q → ∀ x : X, Subsingleton (orientationGroup X j x)) :
    Function.Bijective (retainedCapWithOrientation X p q c) := by
  rw [retained_cap_eq_localTraceCap]
  exact HodgeLean.Foundations.RationalHomologyManifold.cap_duality X t p q
    (retainedGlobalLocalOrientation X (p + q) c ho hv) c rfl

/-- Projective complex points have a finite triangulation in the existing global duality interface. -/
def retainedProjectiveTriangulation (X : Over (Spec ↧ℂ)) [IsProjective X.hom] :
    HodgeLean.Foundations.RationalHomologyManifold.FiniteTriangulation (a3b4_an X.hom) := by
  let Z : Fin 0 → Over (Spec ↧ℂ) := fun j => Fin.elim0 j
  let i : ∀ j, Z j ⟶ X := fun j => Fin.elim0 j
  letI : ∀ j, IsClosedImmersion (i j).left := fun j => Fin.elim0 j
  let h := properCycle_projective_marked_triangulation X Z i
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2.choose⟩

/-- The specified orientation on an integral projective complex scheme gives bijective actual middle cap. -/
theorem retained_projective_middle_cap_bijective
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k) (c : Homology ℚ (a3b4_an X.hom) (2 * (2 * k)))
    (ho : ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) (2 * (2 * k)) c x))
    (hv : ∀ j : ℕ, j ≠ 2 * (2 * k) → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x)) :
    Function.Bijective (retainedMiddleCapWithOrientation (a3b4_an X.hom) k c) := by
  letI : T2Space (a3b4_an X.hom) := HodgeLean.Foundations.Analytic.f4_t2Space X
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  letI : CompactSpace (a3b4_an X.hom) := inferInstanceAs (CompactSpace (ComplexPoint X))
  obtain ⟨U, hU, hgU, _, hsm⟩ := properCycle_smooth_affine_generic_neighborhood X
    (2*k) hdim ⊤ (by trivial)
  let Y := AlgebraicGeometry.ComplexPoint.openScheme X U
  letI : Nonempty U := ⟨⟨genericPoint X.left, hgU⟩⟩
  letI : Nonempty Y.left := inferInstanceAs (Nonempty U.toScheme)
  letI : IsAffine Y.left := hU
  letI : IsIntegral Y.left := isIntegral_of_isOpenImmersion U.ι
  letI : LocallyOfFiniteType Y.hom := by
    change LocallyOfFiniteType (U.ι ≫ X.hom)
    infer_instance
  letI : SmoothOfRelativeDimension (2*k) Y.hom := hsm
  letI : Smooth Y.hom := SmoothOfRelativeDimension.smooth (2*k) Y.hom
  letI : QuasiCompact Y.hom := inferInstance
  letI : IsSeparated Y.hom := by
    change IsSeparated (U.ι ≫ X.hom)
    infer_instance
  letI : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  letI : ConnectedSpace (ComplexPoint Y) := AlgebraicGeometry.ComplexPoint.connectedSpace Y
  have hdense : DenseRange (Point.map (AlgebraicGeometry.ComplexPoint.openInclusion X U)) := by
    apply (HodgeLean.Foundations.AnalyticDivisorAlgebraic24.gaga24_dense_overOpen X U).mono
    intro z hz
    refine ⟨(AlgebraicGeometry.ComplexPoint.openHomeomorph X U).symm ⟨z, hz⟩, ?_⟩
    exact congrArg Subtype.val
      ((AlgebraicGeometry.ComplexPoint.openHomeomorph X U).apply_symm_apply ⟨z, hz⟩)
  letI : PreconnectedSpace (a3b4_an X.hom) :=
    hdense.preconnectedSpace (Point.continuous_map _)
  letI : Nonempty (a3b4_an X.hom) := ⟨Point.map
    (AlgebraicGeometry.ComplexPoint.openInclusion X U) (Classical.choice inferInstance : ComplexPoint Y)⟩
  letI : ConnectedSpace (a3b4_an X.hom) := ⟨inferInstance⟩
  have h : 2 * k + 2 * k = 2 * (2 * k) := by omega
  have ht := retained_triangulated_cap_bijective (a3b4_an X.hom)
    (retainedProjectiveTriangulation X) (2*k) (2*k) (h.symm ▸ c)
  apply ht
  · have htransport : ∀ {n m : ℕ} (e : n = m)
        (a : Homology ℚ (a3b4_an X.hom) m),
        (∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) m a x)) →
        ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) n (e.symm ▸ a) x) := by
      intro n m e a ha
      subst m
      exact ha
    exact htransport h c ho
  · intro j hj x
    exact hv j (fun he => hj (he.trans h.symm)) x

end HodgeLean.Foundations.QuotientDuality
