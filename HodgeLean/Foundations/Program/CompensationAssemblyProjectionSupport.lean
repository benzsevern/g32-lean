import HodgeLean.Foundations.Program.CompensationAssemblyProjectionDimension
import HodgeLean.Foundations.Program.CompensationAssemblySingularSupport
import HodgeConjecture.Mathlib.Topology.Category.TopPair
import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.OpenRestrictedVanishing

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory Limits TopologicalSpace Opposite Abelian MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters
open AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

theorem cq_prime_smooth_support_relH_isZero
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) {p : ℕ} (hx : Order.coheight x = p)
    (n : ℕ) (hn : n < 2 * p) :
    IsZero (AddCommGrpCat.of (CategoryTheory.Sheaf.relH
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
      n (homOfLE (cycleComponentSupportComplement_le_smoothAmbientOpen X x)))) := by
  let T := TopCat.of (ComplexPoint X)
  let Z := cycleComponentAnalyticClosedSupport X x
  let U := cycleComponentSmoothSupportAmbientOpen X x
  let K := complexSupportInjectiveComplex X Z
  have hzero : IsZero ((((TopCat.Sheaf.supportEvaluation T U).mapHomologicalComplex
      ℤᵘᵖ).obj K).homology (n : ℤ)) := by
    apply TopCat.Sheaf.sectionCohomology_isZero_of_cofinal_lower_vanishing T K U 0 (n : ℤ)
    · intro j
      exact TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque T Z.compl
        ((ambientRationalInjectiveComplex X).X j)
    · intro j hj y hy V hyV
      exact cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing
        X x hx j (by omega) y hy V hyV
  let e := @TopCat.Sheaf.relHAddEquivSupportedSectionsHomology
    T Z.compl U Z.compl (inf_eq_right.mpr
      (cycleComponentSupportComplement_le_smoothAmbientOpen X x)) inferInstance
    ((TopCat.Sheaf.constantFunctor T).obj (AddCommGrpCat.of ℚ))
    (ambientRationalInjectiveComplex X)
    (ambientRationalInjectiveComplex_isKInjective X)
    (ambientRationalInjectiveSingleAugmentation X)
    (ambientRationalInjectiveSingleAugmentation_quasiIso X) n
  letI : Subsingleton ((((TopCat.Sheaf.supportEvaluation T U).mapHomologicalComplex
      ℤᵘᵖ).obj (((TopCat.Sheaf.sheafSectionsSupportedOutside T Z.compl).mapHomologicalComplex
        ℤᵘᵖ).obj (ambientRationalInjectiveComplex X))).homology (n : ℤ)) :=
    AddCommGrpCat.subsingleton_of_isZero hzero
  letI := e.injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

theorem cq_prime_support_isZero_of_lt
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) {p : ℕ} (hx : Order.coheight x = p)
    (n : ℕ) (hn : n < 2 * p) :
    IsZero (AddCommGrpCat.of (H_[cycleComponentAnalyticClosedSupport X x]^n(X; ℚ))) := by
  let T := TopCat.of (ComplexPoint X)
  let Z := cycleComponentAnalyticClosedSupport X x
  let U := cycleComponentSmoothSupportAmbientOpen X x
  let F := (TopCat.Sheaf.constantFunctor T).obj (AddCommGrpCat.of ℚ)
  let f : Z.compl ⟶ U := homOfLE (cycleComponentSupportComplement_le_smoothAmbientOpen X x)
  let g : U ⟶ ⊤ := homOfLE le_top
  let e := CategoryTheory.Sheaf.relH.restrictEquivOfIsZero F f g n
    (cycleComponentSingularBoundaryRelH_isZero_of_lt X x hx n (by omega))
    (cycleComponentSingularBoundaryRelH_isZero_of_lt X x hx (n + 1) (by omega))
  letI : Subsingleton (CategoryTheory.Sheaf.relH F n f) :=
    AddCommGrpCat.subsingleton_of_isZero (cq_prime_smooth_support_relH_isZero X x hx n hn)
  letI : Subsingleton (H_[Z]^n(X; ℚ)) := e.injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

theorem cq_prime_forgetSupport_eq_zero_of_lt
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) {p : ℕ} (hx : Order.coheight x = p)
    (n : ℕ) (hn : n < 2 * p)
    (c : H_[cycleComponentAnalyticClosedSupport X x]^n(X; ℚ)) :
    ComplexPoint.forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x) n c = 0 := by
  letI := AddCommGrpCat.subsingleton_of_isZero (cq_prime_support_isZero_of_lt X x hx n hn)
  have hc : c = 0 := Subsingleton.elim _ _
  rw [hc, map_zero]

theorem cq_support_restriction_injective_of_isZero
    (T : TopCat.{0})
    [HasExt.{0} (CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (Z : Closeds T) (n : ℕ)
    (hZ : IsZero (AddCommGrpCat.of (TopCat.Sheaf.supportH.{0, 0} T Z F n))) :
    Function.Injective ((Ext.mk₀
      ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology T)).map
        (homOfLE (le_top : Z.compl ≤ ⊤)))).precomp F (zero_add n)) := by
  let f : Z.compl ⟶ (⊤ : Opens T) := homOfLE le_top
  let S := Ext.contravariantSequence (CategoryTheory.Sheaf.pairShortComplex_shortExact f)
    F n (n + 1) (by omega)
  have hS := CategoryTheory.Sheaf.relH.sequence_exact F f n (n + 1) (by omega)
  have hmono : Mono (S.map' 1 2 (by omega) (by omega)) :=
    (hS.exact 0).mono_g (hZ.eq_zero_of_src _)
  exact (AddCommGrpCat.mono_iff_injective _).mp hmono

theorem cq_projection_image_support_isZero
    (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5)
    (himage : Order.coheight ((fst A Y).left x) ≠ 3) :
    IsZero (AddCommGrpCat.of
      (H_[cycleComponentAnalyticClosedSupport A
        ((fst A Y).left x)]^6(A; ℚ))) := by
  let y := (fst A Y).left x
  have hsum := cq_point_height_add_coheight A 6 hA y
  have hbound : Order.coheight y ≤ 6 := by
    calc
      Order.coheight y ≤ Order.height y + Order.coheight y := le_add_self
      _ = 6 := hsum
  have hfinite : Order.coheight y ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top 6) hbound
  obtain ⟨p, hp⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hge := cq_projection_image_coheight_ge_three A Y hA hY x hx
  have hgt : (3 : ℕ∞) < Order.coheight y := lt_of_le_of_ne hge himage.symm
  rw [← hp] at hgt
  have hpgt : 3 < p := by exact_mod_cast hgt
  exact cq_prime_support_isZero_of_lt A y hp.symm 6 (by omega)

theorem cq_support_sheaf_isZero_to_singular
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    (hS : IsZero (AddCommGrpCat.of (H_[S]^n(X; ℚ)))) :
    IsZero (CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X)) n) := by
  let P := neighborhoodSupportComplementPair Set.univ (S : Set (ComplexPoint X))
  let Q := TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) ((S : Set (ComplexPoint X))ᶜ)
  let i : P ≅ Q := TopPair.isoOfSubset (Homeomorph.Set.univ (ComplexPoint X)) (fun _ => Iff.rfl)
  letI := AddCommGrpCat.subsingleton_of_isZero hS
  letI : Subsingleton (RelativeCohomology ℚ P n) :=
    (supportedSingularClass X S n).symm.injective.subsingleton
  have hleft : Function.LeftInverse (relativeCohomologyMap ℚ n i.inv)
      (relativeCohomologyMap ℚ n i.hom) := by
    intro a
    change (relativeCohomologyMap ℚ n i.inv ∘ₗ relativeCohomologyMap ℚ n i.hom) a = a
    rw [← relativeCohomologyMap_comp, i.inv_hom_id, relativeCohomologyMap_id]
    rfl
  have hinj : Function.Injective (relativeCohomologyMap ℚ n i.hom) := hleft.injective
  letI : Subsingleton (RelativeCohomology ℚ Q n) := hinj.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

theorem cq_projection_image_singular_restriction_injective
    (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5)
    (himage : Order.coheight ((fst A Y).left x) ≠ 3) :
    Function.Injective (cohomologyMap ℚ 6
      (Opens.inclusion' (X := TopCat.of (ComplexPoint A))
        (cycleComponentAnalyticClosedSupport A ((fst A Y).left x)).compl)) := by
  let S := cycleComponentAnalyticClosedSupport A ((fst A Y).left x)
  exact cq_relative_restriction_injective_of_isZero
    (TopPair.ofSubset (X := TopCat.of (ComplexPoint A)) ((S : Set (ComplexPoint A))ᶜ)) 6
    (cq_support_sheaf_isZero_to_singular A S 6
      (cq_projection_image_support_isZero A Y hA hY x hx himage))

end HodgeLean.Foundations.Program
