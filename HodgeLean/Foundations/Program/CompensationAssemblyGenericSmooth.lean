import HodgeLean.Foundations.Program.CompensationAssemblyPrimeMap
import Mathlib.AlgebraicGeometry.FunctionField

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

theorem cq_genericPoint_mem_smoothLocus {X Y : Scheme}
    (sX : X ⟶ Spec ↧ℂ) (sY : Y ⟶ Spec ↧ℂ) (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [LocallyOfFinitePresentation f]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (hf : f ≫ sY = sX) [IsDominant f] :
    genericPoint X ∈ f.smoothLocus := by
  letI : LocallyOfFinitePresentation sX := inferInstance
  let U := sX.smoothLocus
  have hU : genericPoint X ∈ U := sX.genericPoint_mem_smoothLocus_of_perfectField
  letI : Nonempty U := ⟨⟨_, hU⟩⟩
  letI : IsIntegral U.toScheme := inferInstance
  letI : Smooth (U.ι ≫ sX) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq U.ι sX]
    ext u
    exact iff_true_intro u.2
  letI : IsDominant U.ι := by
    constructor
    rw [DenseRange, Scheme.Opens.range_ι]
    exact U.isOpen.dense ⟨_, hU⟩
  have hgp := gfs_genericPoint_mem_smoothLocus (U.ι ≫ sX) sY (U.ι ≫ f)
    (by rw [Category.assoc, hf])
  rw [← Scheme.Hom.preimage_smoothLocus_eq U.ι f, Scheme.Hom.mem_preimage,
    genericPoint_eq_of_isOpenImmersion U.ι] at hgp
  exact hgp

instance cq_primeProjection_locallyOfFinitePresentation (A Y : Over (Spec ↧ℂ))
    [LocallyOfFiniteType A.hom] [IsProjective Y.hom] (x : (A ⊗ Y).left) :
    LocallyOfFinitePresentation (cq_primeProjection A Y x).left := by
  letI : IsProper (cq_primeProjection A Y x).left := cq_primeProjection_proper A Y x
  letI : IsLocallyNoetherian (HodgeLean.Adapters.a2r_component A
      ((CategoryTheory.CartesianMonoidalCategory.fst A Y).left x)).left :=
    LocallyOfFiniteType.isLocallyNoetherian
      (HodgeLean.Adapters.a2r_component A ((CategoryTheory.CartesianMonoidalCategory.fst A Y).left x)).hom
  infer_instance

theorem cq_exists_smooth_restriction_of_fiber {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsProper f] [LocallyOfFinitePresentation f] (y : Y)
    (hy : ∀ x, f x = y → x ∈ f.smoothLocus) :
    ∃ U : Y.Opens, y ∈ U ∧ Smooth (f ∣_ U) := by
  let U : Y.Opens := ⟨(f '' (f.smoothLocus : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ f.smoothLocus.isOpen.isClosed_compl).isOpen_compl⟩
  have hyU : y ∈ U := by
    rintro ⟨x, hx, hxy⟩
    exact hx (hy x hxy)
  letI : Smooth ((f ⁻¹ᵁ U).ι ≫ f) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq (f ⁻¹ᵁ U).ι f]
    ext x
    refine iff_true_intro ?_
    by_contra hx
    exact x.2 ⟨x.1, hx, rfl⟩
  haveI : Smooth ((f ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι]
    infer_instance
  letI : MorphismProperty.RespectsIso (@Smooth.{0}) := by
    apply MorphismProperty.RespectsIso.mk
    · intro S T Z e g hg
      letI : Smooth g := hg
      infer_instance
    · intro S T Z e g hg
      letI : Smooth g := hg
      infer_instance
  letI : MorphismProperty.HasOfPostcompProperty (@Smooth.{0}) (@IsOpenImmersion.{0}) :=
    hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict (@Smooth.{0}) (by
      intro S T g V hg
      letI : Smooth g := hg
      infer_instance)
  exact ⟨U, hyU, MorphismProperty.of_postcomp (@Smooth.{0}) (W' := @IsOpenImmersion.{0})
    (f ∣_ U) U.ι inferInstance inferInstance⟩

theorem cq_primeProjection_generic_smooth (A Y : Over (Spec ↧ℂ))
    [LocallyOfFiniteType A.hom] [IsProjective Y.hom] (x : (A ⊗ Y).left) :
    genericPoint (a2r_component (A ⊗ Y) x).left ∈ (cq_primeProjection A Y x).left.smoothLocus := by
  letI : IsProper (cq_primeProjection A Y x).left := cq_primeProjection_proper A Y x
  letI : IsDominant (cq_primeProjection A Y x).left := cq_primeProjection_dominant A Y x
  letI : LocallyOfFiniteType (a2r_component (A ⊗ Y) x).hom := by
    have h : LocallyOfFiniteType ((cq_primeProjection A Y x).left ≫
        (a2r_component A ((fst A Y).left x)).hom) := inferInstance
    exact (Over.w (cq_primeProjection A Y x)) ▸ h
  exact cq_genericPoint_mem_smoothLocus (a2r_component (A ⊗ Y) x).hom
    (a2r_component A ((fst A Y).left x)).hom (cq_primeProjection A Y x).left
    (Over.w (cq_primeProjection A Y x))

theorem cq_primeProjection_generic_fiber_eq (A Y : Over (Spec ↧ℂ))
    [CategoryTheory.GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [CategoryTheory.GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5)
    (himage : Order.coheight ((fst A Y).left x) = 3) :
    (cq_primeProjection A Y x).left ⁻¹'
        {genericPoint (a2r_component A ((fst A Y).left x)).left} =
      {genericPoint (a2r_component (A ⊗ Y) x).left} := by
  ext q
  constructor
  · intro hq
    apply Set.mem_singleton_iff.mpr
    let inc := cycleComponentι (A ⊗ Y).left x
    apply inc.isClosedEmbedding.injective
    have hs : inc q ∈ closure {x} := by
      rw [← range_cycleComponentι (A ⊗ Y).left x]
      exact ⟨q, rfl⟩
    have hc := congrArg (fun g : (a2r_component (A ⊗ Y) x).left ⟶ A.left => g q)
      (cq_primeProjection_comp A Y x)
    have hq' : (cq_primeProjection A Y x).left q =
        genericPoint (a2r_component A ((fst A Y).left x)).left := hq
    change cycleComponentι A.left ((fst A Y).left x) ((cq_primeProjection A Y x).left q) =
      (fst A Y).left (inc q) at hc
    rw [hq'] at hc
    have ht : cycleComponentι A.left ((fst A Y).left x)
        (genericPoint (a2r_component A ((fst A Y).left x)).left) = (fst A Y).left x :=
      a2r_cycleComponentι_genericPoint _ _
    have hm : inc q ∈ ({x} : Set (A ⊗ Y).left) :=
      (Set.ext_iff.mp (cq_projection_prime_fiber_eq A Y hA hY x hx himage) (inc q)).mp
        ⟨hs, hc.symm.trans ht⟩
    exact (Set.mem_singleton_iff.mp hm).trans
      (a2r_cycleComponentι_genericPoint (A ⊗ Y).left x).symm
  · intro hq
    obtain rfl := Set.mem_singleton_iff.mp hq
    exact cq_primeProjection_genericPoint A Y x

theorem cq_primeProjection_smooth_neighborhood (A Y : Over (Spec ↧ℂ))
    [CategoryTheory.GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [CategoryTheory.GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5)
    (himage : Order.coheight ((fst A Y).left x) = 3) :
    ∃ U : (a2r_component A ((fst A Y).left x)).left.Opens,
      genericPoint (a2r_component A ((fst A Y).left x)).left ∈ U ∧
      Dense (U : Set (a2r_component A ((fst A Y).left x)).left) ∧
      Smooth ((cq_primeProjection A Y x).left ∣_ U) := by
  letI : IsProper (cq_primeProjection A Y x).left := cq_primeProjection_proper A Y x
  have hy : ∀ q, (cq_primeProjection A Y x).left q =
      genericPoint (a2r_component A ((fst A Y).left x)).left →
      q ∈ (cq_primeProjection A Y x).left.smoothLocus := by
    intro q hq
    have hm : q ∈ ({genericPoint (a2r_component (A ⊗ Y) x).left} :
        Set (a2r_component (A ⊗ Y) x).left) :=
      (Set.ext_iff.mp (cq_primeProjection_generic_fiber_eq A Y hA hY x hx himage) q).mp hq
    rw [Set.mem_singleton_iff.mp hm]
    exact cq_primeProjection_generic_smooth A Y x
  obtain ⟨U, hU, hs⟩ := cq_exists_smooth_restriction_of_fiber (cq_primeProjection A Y x).left
    (genericPoint (a2r_component A ((fst A Y).left x)).left) hy
  exact ⟨U, hU, U.isOpen.dense ⟨_, hU⟩, hs⟩

end HodgeLean.Foundations.Program
