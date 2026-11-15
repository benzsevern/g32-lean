import HodgeLean.Foundations.Program.CompensationAssemblyPrimeFinite

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

def cq_primeProjection (A Y : Over (Spec ↧ℂ)) (x : (A ⊗ Y).left) :
    a2r_component (A ⊗ Y) x ⟶ a2r_component A ((fst A Y).left x) :=
  (a2r_exists_restrict (fst A Y) x).choose

theorem cq_primeProjection_comp (A Y : Over (Spec ↧ℂ)) (x : (A ⊗ Y).left) :
    (cq_primeProjection A Y x).left ≫ cycleComponentι A.left ((fst A Y).left x) =
      cycleComponentι (A ⊗ Y).left x ≫ (fst A Y).left :=
  (a2r_exists_restrict (fst A Y) x).choose_spec

theorem cq_primeProjection_genericPoint (A Y : Over (Spec ↧ℂ)) (x : (A ⊗ Y).left) :
    (cq_primeProjection A Y x).left (genericPoint (a2r_component (A ⊗ Y) x).left) =
      genericPoint (a2r_component A ((fst A Y).left x)).left := by
  apply (cycleComponentι A.left ((fst A Y).left x)).isClosedEmbedding.injective
  change ((cq_primeProjection A Y x).left ≫ cycleComponentι A.left ((fst A Y).left x))
      (genericPoint (a2r_component (A ⊗ Y) x).left) = _
  rw [cq_primeProjection_comp, Scheme.Hom.comp_apply]
  change (fst A Y).left
      (cycleComponentι (A ⊗ Y).left x (genericPoint (cycleComponent (A ⊗ Y).left x))) =
    cycleComponentι A.left ((fst A Y).left x)
      (genericPoint (cycleComponent A.left ((fst A Y).left x)))
  rw [a2r_cycleComponentι_genericPoint, a2r_cycleComponentι_genericPoint]

theorem cq_primeProjection_proper (A Y : Over (Spec ↧ℂ)) [IsProjective Y.hom]
    (x : (A ⊗ Y).left) : IsProper (cq_primeProjection A Y x).left := by
  letI : IsProper (fst A Y).left :=
    inferInstanceAs (IsProper (Limits.pullback.fst A.hom Y.hom))
  have hp : IsProper (cycleComponentι (A ⊗ Y).left x ≫ (fst A Y).left) := inferInstance
  haveI : IsProper ((cq_primeProjection A Y x).left ≫ cycleComponentι A.left ((fst A Y).left x)) :=
    (cq_primeProjection_comp A Y x).symm ▸ hp
  exact IsProper.of_comp (cq_primeProjection A Y x).left
    (cycleComponentι A.left ((fst A Y).left x))

theorem cq_primeProjection_dominant (A Y : Over (Spec ↧ℂ)) (x : (A ⊗ Y).left) :
    IsDominant (cq_primeProjection A Y x).left := by
  constructor
  intro y
  have hy : y ∈ closure {genericPoint (a2r_component A ((fst A Y).left x)).left} :=
    specializes_iff_mem_closure.mp
      ((genericPoint_spec (a2r_component A ((fst A Y).left x)).left).specializes (Set.mem_univ y))
  have hg : genericPoint (a2r_component A ((fst A Y).left x)).left ∈
      Set.range (cq_primeProjection A Y x).left :=
    ⟨genericPoint (a2r_component (A ⊗ Y) x).left, cq_primeProjection_genericPoint A Y x⟩
  exact closure_mono (Set.singleton_subset_iff.mpr hg) hy

theorem cq_primeProjection_degree (A Y : Over (Spec ↧ℂ)) (x : (A ⊗ Y).left) :
    a1p_degree (cq_primeProjection A Y x).left
      (genericPoint (a2r_component (A ⊗ Y) x).left) = a1p_degree (fst A Y).left x := by
  have hd {X Z : Scheme} (g : X ⟶ Z) [IsClosedImmersion g] (z : X) :
      a1p_degree g z = 1 := by
    apply a1x_degree_eq_one_of_surjective
    intro a
    obtain ⟨b, rfl⟩ := X.residue_surjective z a
    obtain ⟨c, hc⟩ := g.stalkMap_surjective z b
    refine ⟨Z.residue (g z) c, ?_⟩
    rw [← hc, ← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]
  have h := a1p_degree_comp (cq_primeProjection A Y x).left
    (cycleComponentι A.left ((fst A Y).left x))
    (genericPoint (a2r_component (A ⊗ Y) x).left)
  rw [cq_primeProjection_comp, a1p_degree_comp] at h
  have hg : cycleComponentι (A ⊗ Y).left x
      (genericPoint (a2r_component (A ⊗ Y) x).left) = x :=
    a2r_cycleComponentι_genericPoint _ _
  have hs : a1p_degree (cycleComponentι (A ⊗ Y).left x)
      (genericPoint (a2r_component (A ⊗ Y) x).left) = 1 :=
    hd _ _
  have ht : a1p_degree (cycleComponentι A.left ((fst A Y).left x))
      ((cq_primeProjection A Y x).left (genericPoint (a2r_component (A ⊗ Y) x).left)) = 1 :=
    hd _ _
  rw [hg, hs, ht, mul_one, one_mul] at h
  exact h.symm

theorem cq_primeProjection_finite_neighborhood (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5)
    (himage : Order.coheight ((fst A Y).left x) = 3) :
    ∃ V : (a2r_component A ((fst A Y).left x)).left.Opens,
      genericPoint (a2r_component A ((fst A Y).left x)).left ∈ V ∧
      Dense (V : Set (a2r_component A ((fst A Y).left x)).left) ∧
      IsFinite ((cq_primeProjection A Y x).left ∣_ V) := by
  let f := (cq_primeProjection A Y x).left
  let inc := cycleComponentι (A ⊗ Y).left x
  letI : IsProper f := cq_primeProjection_proper A Y x
  have hfin : (f ⁻¹' {genericPoint (a2r_component A ((fst A Y).left x)).left}).Finite := by
    apply Set.Finite.of_finite_image (f := inc) _ inc.isClosedEmbedding.injective.injOn
    apply (Set.finite_singleton x).subset
    rintro _ ⟨q, hq, rfl⟩
    apply (Set.ext_iff.mp (cq_projection_prime_fiber_eq A Y hA hY x hx himage) (inc q)).mp
    refine ⟨?_, ?_⟩
    · rw [← range_cycleComponentι (A ⊗ Y).left x]
      exact ⟨q, rfl⟩
    · have hc := congrArg (fun g : (a2r_component (A ⊗ Y) x).left ⟶ A.left => g q)
        (cq_primeProjection_comp A Y x)
      have hq' : f q = genericPoint (a2r_component A ((fst A Y).left x)).left := hq
      change cycleComponentι A.left ((fst A Y).left x) (f q) = (fst A Y).left (inc q) at hc
      rw [hq'] at hc
      have hg : cycleComponentι A.left ((fst A Y).left x)
          (genericPoint (a2r_component A ((fst A Y).left x)).left) = (fst A Y).left x :=
        a2r_cycleComponentι_genericPoint _ _
      exact hc.symm.trans hg
  obtain ⟨V, hV, hf⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f _ hfin
  exact ⟨V, hV, V.isOpen.dense ⟨_, hV⟩, hf⟩

theorem cq_primeProjection_generic_flat (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5)
    (himage : Order.coheight ((fst A Y).left x) = 3) :
    ∃ V : (a2r_component A ((fst A Y).left x)).left.Opens,
      genericPoint (a2r_component A ((fst A Y).left x)).left ∈ V ∧
      Dense (V : Set (a2r_component A ((fst A Y).left x)).left) ∧
      IsFinite ((cq_primeProjection A Y x).left ∣_ V) ∧
      ∃ W : V.toScheme.Opens, Dense (W : Set V.toScheme) ∧
        Flat (((cq_primeProjection A Y x).left ∣_ V) ∣_ W) := by
  obtain ⟨V, hV, hVd, hf⟩ := cq_primeProjection_finite_neighborhood A Y hA hY x hx himage
  letI : Nonempty V := ⟨⟨_, hV⟩⟩
  letI : IsIntegral V.toScheme := inferInstance
  letI : IsLocallyNoetherian (a2r_component A ((fst A Y).left x)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (a2r_component A ((fst A Y).left x)).hom
  letI : IsFinite ((cq_primeProjection A Y x).left ∣_ V) := hf
  obtain ⟨W, hWd, hWflat⟩ :=
    gfs_exists_flat_over_dense_open ((cq_primeProjection A Y x).left ∣_ V)
  exact ⟨V, hV, hVd, hf, W, hWd, hWflat⟩

end HodgeLean.Foundations.Program
