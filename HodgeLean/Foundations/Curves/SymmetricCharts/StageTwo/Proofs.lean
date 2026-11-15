import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.Checks
import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.Defs
import HodgeLean.Foundations.Curves.SymmetricCharts.Basic
import HodgeLean.Foundations.Program.SchoenCycleRetainedQuotientSmoothNeighbourhood
import HodgeLean.Foundations.Program.SchoenCycleComplexNeighbourhoodDimension
import HodgeLean.Foundations.Program.SchoenTowerBranchProjective
import HodgeLean.Foundations.Program.SchoenTowerBranchKernel
import HodgeLean.Foundations.Program.SchoenTowerI2aInitialBranchChart
import HodgeLean.Foundations.Program.SchoenCycleBranchImagePoints
import HodgeLean.Foundations.Program.SchoenTowerComplexPointsExist
import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.CoordinateHelpers
import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.TransportPositive
import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.TransportZero
import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.CoordinateReducedHelpers
import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.LocalRadicalHelpers
import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.MultipleImageHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2SmoothConormalFramesHelpers

/-! # Symmetric curve stage two interfaces

Retained projections, branch ideals and relative dimensions keep their scheme types.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
variable (C : Over (Spec ↧ℂ)) [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
private theorem projection_universal (n : ℕ) :
    (∀ σ, s2_permute C n σ ≫ projection C n = projection C n) ∧
    (∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) →
      ∃! d : symmetricPower C n ⟶ T, projection C n ≫ d = f) := by
  obtain ⟨_, _, _, _, hi, hu⟩ := projective_quotient C n
  constructor
  · intro σ
    apply (cancel_epi (HodgeLean.Foundations.Curves.Picard.Families.orderedRecursiveIso C n).hom).mp
    have h := hi σ⁻¹
    dsimp only [orderedProjection] at h
    rw [← Category.assoc,
      HodgeLean.Foundations.Curves.Picard.Families.orderedRecursiveIso_permute,
      inv_inv, Category.assoc] at h
    exact h
  · intro T f hf
    let e := HodgeLean.Foundations.Curves.Picard.Families.orderedRecursiveIso C n
    obtain ⟨d, hd, huniq⟩ := hu T (e.hom ≫ f) (by
      intro σ
      dsimp only [e]
      rw [← Category.assoc,
        HodgeLean.Foundations.Curves.Picard.Families.orderedRecursiveIso_permute,
        Category.assoc, hf])
    refine ⟨d, ?_, ?_⟩
    · exact (cancel_epi e.hom).mp hd
    · intro d' hd'
      apply huniq
      change e.hom ≫ projection C n ≫ d' = e.hom ≫ f
      rw [hd']

/-- The specified categorical quotient has a unique projection-preserving comparison.
Source: SGA 1, Exposé V, §1.
HC no distance; AV milestone no distance.
-/
theorem retained_comparison_aux (n : ℕ) (Q : Over (Spec ↧ℂ)) (q : g3_power C n ⟶ Q)
    (hinv : ∀ σ, s2_permute C n σ ≫ q = q)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : Q ⟶ T, q ≫ d = f) :
    ∃! e : symmetricPower C n ≅ Q, projection C n ≫ e.hom = q := by
  obtain ⟨hp, hu⟩ := projection_universal C n
  obtain ⟨a, ha, hau⟩ := hu Q q hinv
  obtain ⟨b, hb, hbu⟩ := huniv _ (projection C n) hp
  have hab : a ≫ b = 𝟙 _ := by
    exact (hu _ (projection C n) hp).unique
      (by rw [← Category.assoc, ha, hb]) (by rw [Category.comp_id])
  have hba : b ≫ a = 𝟙 _ := by
    exact (huniv _ q hinv).unique
      (by rw [← Category.assoc, hb, ha]) (by rw [Category.comp_id])
  let e : symmetricPower C n ≅ Q := ⟨a, b, hab, hba⟩
  refine ⟨e, ha, ?_⟩
  intro e' he'
  apply Iso.ext
  exact hau e'.hom he'

/-- The curve quotient is smooth of relative dimension n, also in degree zero.
Source: Milne, Jacobian Varieties, §3.
HC no distance; AV milestone no distance.
-/
theorem smooth_dimension_aux [SmoothOfRelativeDimension 1 C.hom] (n : ℕ) :
    SmoothOfRelativeDimension n (symmetricPower C n).hom ∧
      topologicalKrullDim (symmetricPower C n).left = n := by
  obtain ⟨hi, _, hf, hs, _⟩ := projective_quotient C n
  letI := hi
  letI := hf
  letI : Surjective (projection C n).left := ⟨hs⟩
  obtain ⟨hinv, huniv⟩ := projection_universal C n
  refine ⟨?_, krull_dimension C n⟩
  exact s2e_relativeDimension_of_complex_lift_neighbourhoods
    (g3_power C n) (symmetricPower C n) (projection C n) n
    (s2e_retained_quotient_standardSmooth_neighbourhood C (symmetricPower C n) n
      (projection C n) hinv huniv)

/-- The empty symmetric power is the base with its actual projection.
Source: Milne, Jacobian Varieties, §3, empty effective divisor.
HC no distance; AV milestone no distance.
-/
theorem degree_zero_aux : ∃ e : symmetricPower C 0 ≅ Over.mk (𝟙 (Spec ↧ℂ)),
    projection C 0 ≫ e.hom = 𝟙 _ := by
  obtain ⟨e, he, _⟩ := retained_comparison_aux C 0 (Over.mk (𝟙 (Spec ↧ℂ)))
    (𝟙 (g3_power C 0)) (by
      intro σ
      apply s2_product_hom_ext 0
      intro i
      exact Fin.elim0 i) (by
      intro T f hf
      refine ⟨f, Category.id_comp f, ?_⟩
      intro d hd
      exact (Category.id_comp d).symm.trans hd)
  exact ⟨e, he⟩

/-- Distinct branch divisors have independent etale parameters at every divisor, including repeated support.
Source: Milne, Jacobian Varieties, §3; Hartshorne, Algebraic Geometry, II.8.
HC no distance; AV milestone no distance.
-/
theorem branch_coordinates_aux [SmoothOfRelativeDimension 1 C.hom] (h k : ℕ) (hk : k ≤ h+1)
    (b : Fin k → ComplexPoint C) (hb : Function.Injective b)
    (x : ComplexPoint (symmetricPower C (h+1)))
    (hx : ∀ i, x.left (default : Spec ↧ℂ) ∈ (branchIdeal C h (b i)).support) :
    ∃ (V : (symmetricPower C (h+1)).left.Opens)
      (t : V.toScheme ⟶ (affine (h+1)).left),
      x.left (default : Spec ↧ℂ) ∈ V ∧ Etale t ∧
      t ≫ (affine (h+1)).hom = V.ι ≫ (symmetricPower C (h+1)).hom ∧
      ∀ i : Fin k, (branchIdeal C h (b i)).comap V.ι =
        (coordinateIdeal (h+1) ⟨i.val, lt_of_lt_of_le i.isLt hk⟩).comap t := by
  classical
  obtain ⟨hi, hp, hf, hs, _⟩ := projective_quotient C (h+1)
  letI := hf
  obtain ⟨hinv, huniv⟩ := projection_universal C (h+1)
  obtain ⟨z, hz⟩ := s2e_complexPoint_lift_of_mem_range (projection C (h+1)) x
    (hs x.underlying)
  obtain ⟨U, hU, u, p, c, J, κ, v, hu, hp, hc, hJ, hv, hnot, hI⟩ :=
    s2v_i2a_simultaneous_initial_branch_chart C (symmetricPower C (h+1))
      (SmoothOfRelativeDimension.dim_eq C.hom 1) h (projection C (h+1))
      hinv huniv b hb z
  letI := hU
  letI := hu
  letI := overSpecAlgebra U ⊤
  have hmem (i : Fin k) : i ∈ J := (hJ i).mpr (by
    rw [hz]
    change x.left (IsLocalRing.closedPoint ℂ) ∈ (branchIdeal C h (b i)).support
    simpa only [show (default : Spec ↧ℂ) = IsLocalRing.closedPoint ℂ from
      Subsingleton.elim _ _] using hx i)
  let f : Fin k → Fin (h+1) := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  let g : Fin k → Fin (h+1) := fun i => κ ⟨i, hmem i⟩
  have hf : Function.Injective f := fun i j hij => Fin.ext (congrArg (fun a : Fin (h+1) => a.val) hij)
  have hg : Function.Injective g := fun i j hij =>
    congrArg Subtype.val (κ.injective hij)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  let G := c.comp (MvPolynomial.renameEquiv ℂ σ).toAlgHom
  have hG : G.toRingHom.Etale :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (MvPolynomial.renameEquiv ℂ σ).bijective) hc
  obtain ⟨t, ht, hti⟩ := affine_section_coordinates U (h+1) G hG
  have hbranch (i : Fin k) : (branchIdeal C h (b i)).comap u.left =
      (coordinateIdeal (h+1) (f i)).comap t.left := by
    rw [hti]
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [branchIdeal, hI]
    simp only [Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id]
    rw [U.left.presheaf.map_id]
    simp only [CommRingCat.hom_id, Ideal.map_id]
    rw [hv ⟨i, hmem i⟩]
    congr 2
    change c (MvPolynomial.X (g i)) = c (MvPolynomial.rename σ (MvPolynomial.X (f i)))
    rw [MvPolynomial.rename_X, hσ]
  let V := u.left.opensRange
  have heq : Set.range u.left = Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rfl
  let e := IsOpenImmersion.isoOfRangeEq u.left V.ι heq
  have he : e.inv ≫ u.left = V.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  refine ⟨V, e.inv ≫ t.left, ?_, ?_, ?_, ?_⟩
  · have H := congrArg (fun q : ComplexPoint (symmetricPower C (h+1)) => q.underlying)
      (hp.trans hz)
    rw [show (default : Spec ↧ℂ) = IsLocalRing.closedPoint ℂ from Subsingleton.elim _ _]
    change x.underlying ∈ V
    rw [← H]
    exact ⟨p.underlying, rfl⟩
  · letI := ht
    infer_instance
  · rw [Category.assoc, Over.w t, ← Over.w u, ← Category.assoc, he]
  · intro i
    rw [← he, Scheme.IdealSheafData.comap_comp, hbranch,
      ← Scheme.IdealSheafData.comap_comp]


/-- The finite intersection of distinct retained branches has its reduced scheme ideal.
Source: Schoen (1988), Lemma 2.2; etale coordinate intersections.
HC no distance; AV milestone no distance.
-/
theorem intersectionIdeal_radical [SmoothOfRelativeDimension 1 C.hom]
    (h k : ℕ) (hk : k ≤ h+1) (b : Fin k → ComplexPoint C) (hb : Function.Injective b) :
    (intersectionIdeal C h k b).radical = intersectionIdeal C h k b := by
  classical
  obtain ⟨_, hp, _, _, _⟩ := projective_quotient C (h+1)
  letI := hp
  apply radical_of_complex_neighborhoods (symmetricPower C (h+1)) (intersectionIdeal C h k b)
  intro x
  by_cases hx : x.underlying ∈ (intersectionIdeal C h k b).support
  · have hxb (i : Fin k) : x.left (default : Spec ↧ℂ) ∈ (branchIdeal C h (b i)).support := by
      rw [show (default : Spec ↧ℂ) = IsLocalRing.closedPoint ℂ from Subsingleton.elim _ _]
      exact Scheme.IdealSheafData.support_antitone
        (le_iSup (fun i => branchIdeal C h (b i)) i) hx
    obtain ⟨V, t, hxV, ht, hbase, hbranch⟩ := branch_coordinates_aux C h k hk b hb x hxb
    rw [show (default : Spec ↧ℂ) = IsLocalRing.closedPoint ℂ from Subsingleton.elim _ _] at hxV
    change x.underlying ∈ V at hxV
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
    let X := (symmetricPower C (h+1)).left
    let j : W.toScheme ⟶ V.toScheme := X.homOfLE hWV
    letI : IsOpenImmersion j := inferInstance
    letI : IsAffine W.toScheme := hW
    letI := ht
    let tW := j ≫ t
    have hj : j ≫ V.ι = W.ι := X.homOfLE_ι hWV
    have H : (intersectionIdeal C h k b).comap W.ι =
        ⨆ i : Fin k, (coordinateIdeal (h+1) ⟨i.val, lt_of_lt_of_le i.isLt hk⟩).comap tW := by
      rw [intersectionIdeal, (Scheme.IdealSheafData.map_gc W.ι).l_iSup]
      congr 1
      funext i
      rw [← hj, Scheme.IdealSheafData.comap_comp, hbranch i,
        ← Scheme.IdealSheafData.comap_comp]
    refine ⟨⟨W, hW⟩, hxW, radical_of_affine_open_comap X (intersectionIdeal C h k b) W hW ?_⟩
    rw [H]
    exact etale_coordinate_sum_radical W.toScheme (h+1) k
      (fun i => ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) tW
  · exact radical_neighborhood_off_support _ _ x.underlying hx

/-- Point insertion descends with the actual scheme kernel.
Source: Milne, Jacobian Varieties, §3; Schoen (1988), Lemma 2.2, p. 13.
HC no distance; AV milestone no distance.
-/
theorem point_addition_aux [SmoothOfRelativeDimension 1 C.hom] (h : ℕ) (b : ComplexPoint C) :
    ∃! a : symmetricPower C h ⟶ symmetricPower C (h+1),
      projection C h ≫ a = s2c_branchInsertion C h b ≫ projection C (h+1) ∧
      IsClosedImmersion a.left ∧ a.left.ker = branchIdeal C h b := by
  obtain ⟨hπinv, hπquot⟩ := projection_universal C h
  obtain ⟨hγinv, hγquot⟩ := projection_universal C (h+1)
  obtain ⟨a, ha, hk, hu⟩ := s2t_branch_descent_kernel C
    (symmetricPower C h) (symmetricPower C (h+1)) h b
    (projection C h) (projection C (h+1)) hπinv hπquot hγinv
  refine ⟨a, ⟨ha, ?_, hk⟩, ?_⟩
  · exact s2t_branch_projective_immersion C (symmetricPower C h)
      (symmetricPower C (h+1)) h b (projection C h) (projection C (h+1))
      hπinv hπquot hγinv hγquot a ha
  · intro a' ha'
    exact hu a' ha'.1

/-- Multiple insertion descends to an immersion with its literal ordered projection square.
Source: Milne, Jacobian Varieties, §3; Schoen (1988), Lemma 2.2.
HC no distance; AV milestone no distance.
-/
theorem multiple_addition (h k : ℕ) (hk : k ≤ h+1) (b : Fin k → ComplexPoint C) :
    ∃ a : symmetricPower C (h+1-k) ⟶ symmetricPower C (h+1),
      IsClosedImmersion a.left ∧ projection C (h+1-k) ≫ a =
        multipleInsertion C h k hk b ≫ projection C (h+1) := by
  obtain ⟨a, ha, hπa⟩ := recursive_addition C (symmetricPower C) (projection C)
    (fun n => (projection_universal C n).1) (fun n => (projection_universal C n).2)
    (h+1-k) k b
  let e : symmetricPower C ((h+1-k)+k) ≅ symmetricPower C (h+1) :=
    eqToIso (congrArg (symmetricPower C) (Nat.sub_add_cancel hk))
  letI := ha
  letI : IsIso e.hom.left := by
    change IsIso ((Over.forget (Spec ↧ℂ)).map e.hom)
    infer_instance
  refine ⟨a ≫ e.hom, inferInstanceAs (IsClosedImmersion (a.left ≫ e.hom.left)), ?_⟩
  rw [← Category.assoc, hπa, Category.assoc]
  change recursiveInsertion C (h+1-k) k b ≫
    (projection C ((h+1-k)+k) ≫ eqToHom (congrArg (symmetricPower C) (Nat.sub_add_cancel hk))) = _
  rw [symmetric_projection_cast, ← Category.assoc, recursiveInsertion_eq_multipleInsertion]
  all_goals omega

/-- Distinct point branches intersect scheme-theoretically with the specified conormal rank.
Source: Schoen (1988), Lemma 2.2, pp. 13–14; Hartshorne, Algebraic Geometry, II.8.
HC no distance; AV milestone no distance.
-/
theorem branch_intersections_aux [SmoothOfRelativeDimension 1 C.hom] (h k : ℕ) (hk : k ≤ h+1)
    (b : Fin k → ComplexPoint C) (hb : Function.Injective b) :
    (∃ e : symmetricPower C (h+1-k) ≅ branchIntersection C h k b,
      projection C (h+1-k) ≫ e.hom ≫
        s2c_subschemeι (symmetricPower C (h+1)) (intersectionIdeal C h k b) =
        multipleInsertion C h k hk b ≫ projection C (h+1)) ∧
      SmoothOfRelativeDimension (h+1-k) (branchIntersection C h k b).hom ∧
      (∀ x : (branchIntersection C h k b).left,
        ∃ U : (branchIntersection C h k b).left.Opens, x ∈ U ∧
          Nonempty ((Scheme.Modules.pullback U.ι).obj
            (s2c_conormal (intersectionIdeal C h k b).subschemeι) ≅
            SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k))) := by
  obtain ⟨a, ha, hπa⟩ := multiple_addition C h k hk b
  obtain ⟨hPint, hPproj, hπfin, hπsurj, _⟩ := projective_quotient C (h+1-k)
  obtain ⟨hBint, hBproj, hγfin, hγsurj, _⟩ := projective_quotient C (h+1)
  letI := ha
  letI := hPint
  letI := hPproj
  letI := hBint
  letI := hBproj
  letI := hγfin
  letI : Surjective (projection C (h+1-k)).left := ⟨hπsurj⟩
  letI : Surjective (projection C (h+1)).left := ⟨hγsurj⟩
  letI := (smooth_dimension_aux C (h+1)).1
  letI : Smooth (symmetricPower C (h+1)).hom :=
    SmoothOfRelativeDimension.smooth (h+1) (symmetricPower C (h+1)).hom
  obtain ⟨hinv, huniv⟩ := projection_universal C (h+1)
  have hrange := multiple_addition_range C (symmetricPower C (h+1-k))
    (symmetricPower C (h+1)) (SmoothOfRelativeDimension.dim_eq C.hom 1)
    h k hk b hb (projection C (h+1-k)) (projection C (h+1)) hinv huniv a hπa
  let I := intersectionIdeal C h k b
  change Set.range a.left = (I.support : Set _) at hrange
  letI : IsReduced I.subscheme := subscheme_reduced_of_radical _ I
    (intersectionIdeal_radical C h k hk b hb)
  obtain ⟨e, he⟩ := s2_reducedClosedImmersion_iso_of_range_eq a.left I.subschemeι
    (hrange.trans (Scheme.IdealSheafData.range_subschemeι I).symm)
  let eO : symmetricPower C (h+1-k) ≅ branchIntersection C h k b := Over.isoMk e (by
    change e.hom ≫ (I.subschemeι ≫ (symmetricPower C (h+1)).hom) = _
    rw [← Category.assoc, he, Over.w a])
  have heO : eO.hom ≫ s2c_subschemeι (symmetricPower C (h+1)) I = a := by
    apply Over.OverMorphism.ext
    exact he
  letI := (smooth_dimension_aux C (h+1-k)).1
  letI : IsIso eO.inv.left := by
    change IsIso ((Over.forget (Spec ↧ℂ)).map eO.inv)
    infer_instance
  have hdim : SmoothOfRelativeDimension (h+1-k) (branchIntersection C h k b).hom := by
    rw [← Over.w eO.inv]
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0+(h+1-k))
        (eO.inv.left ≫ (symmetricPower C (h+1-k)).hom))
  letI := hdim
  refine ⟨⟨eO, ?_⟩, hdim, ?_⟩
  · change projection C (h+1-k) ≫
      (eO.hom ≫ s2c_subschemeι (symmetricPower C (h+1)) I) = _
    rw [heO]
    exact hπa
  · intro x
    letI : SmoothOfRelativeDimension ((h+1-k)+k) (symmetricPower C (h+1)).hom := by
      simpa only [Nat.sub_add_cancel hk] using (smooth_dimension_aux C (h+1)).1
    letI : IsClosedImmersion (s2c_subschemeι (symmetricPower C (h+1)) I).left := by
      change IsClosedImmersion I.subschemeι
      infer_instance
    obtain ⟨U, hxU, ⟨E⟩⟩ := s2e_smooth_closedImmersion_conormal_frames
      (branchIntersection C h k b) (symmetricPower C (h+1)) (h+1-k) k
      (s2c_subschemeι (symmetricPower C (h+1)) I) x
    exact ⟨U, hxU, ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app
      (s2c_conormal I.subschemeι) ≪≫ E⟩⟩

/-- More distinct point branches than the degree have empty scheme intersection.
Source: Milne, Jacobian Varieties, §3, effective divisors.
HC no distance; AV milestone no distance.
-/
theorem excess_branches_aux [SmoothOfRelativeDimension 1 C.hom] (h k : ℕ) (hk : h+1 < k)
    (b : Fin k → ComplexPoint C) (hb : Function.Injective b) :
    IsEmpty (branchIntersection C h k b).left := by
  classical
  obtain ⟨hi, hp, hf, hs, _⟩ := projective_quotient C (h+1)
  letI := hi
  letI := hp
  letI := hf
  obtain ⟨hinv, huniv⟩ := projection_universal C (h+1)
  refine ⟨fun y => ?_⟩
  letI : Nonempty (branchIntersection C h k b).left := ⟨y⟩
  letI : LocallyOfFiniteType (branchIntersection C h k b).hom := by
    change LocallyOfFiniteType ((intersectionIdeal C h k b).subschemeι ≫ _)
    infer_instance
  obtain ⟨p⟩ := s2t_nonempty_complexPoints (branchIntersection C h k b)
  let j := s2c_subschemeι (symmetricPower C (h+1)) (intersectionIdeal C h k b)
  let x := Point.map j p
  obtain ⟨z, hz⟩ := s2e_complexPoint_lift_of_mem_range (projection C (h+1)) x
    (hs x.underlying)
  obtain ⟨U, hU, u, q, c, J, κ, v, hu, hq, hc, hJ, hv, hnot, hI⟩ :=
    s2v_i2a_simultaneous_initial_branch_chart C (symmetricPower C (h+1))
      (SmoothOfRelativeDimension.dim_eq C.hom 1) h (projection C (h+1))
      hinv huniv b hb z
  have hmem (i : Fin k) : i ∈ J := by
    apply (hJ i).mpr
    rw [hz]
    apply Scheme.IdealSheafData.support_antitone
      (show branchIdeal C h (b i) ≤ intersectionIdeal C h k b from
        le_iSup (fun i => branchIdeal C h (b i)) i)
    exact (Scheme.IdealSheafData.range_subschemeι (intersectionIdeal C h k b)).le
      ⟨p.underlying, rfl⟩
  have hfull : J = Finset.univ := Finset.eq_univ_iff_forall.mpr hmem
  have hcard := Fintype.card_le_of_injective κ κ.injective
  rw [Fintype.card_coe, hfull, Finset.card_univ, Fintype.card_fin,
    Fintype.card_fin] at hcard
  omega

/-- Curve parameters descend to elementary symmetric coordinates with the actual projection and reflected stabilizers.
Source: Milne, Jacobian Varieties, §3; SGA 1, Exposé V, §1.
HC no distance; AV milestone no distance.
-/
theorem curve_coordinate_transport_aux [SmoothOfRelativeDimension 1 C.hom] (n : ℕ) (z : Fin n → ComplexPoint C) :
    ∃ (U : C.left.Opens) (t : U.toScheme ⟶ (affine 1).left)
      (u : Fin n → (Spec ↧ℂ ⟶ U.toScheme))
      (V : (symmetricPower C n).left.Opens)
      (v : Spec ↧ℂ ⟶ V.toScheme) (c : V.toScheme ⟶ (affine n).left),
      IsAffineOpen U ∧ Etale t ∧ Etale c ∧
      t ≫ (affine 1).hom = U.ι ≫ C.hom ∧
      c ≫ (affine n).hom = V.ι ≫ (symmetricPower C n).hom ∧
      (∀ i, u i ≫ U.ι = (z i).left) ∧
      v ≫ V.ι = (s2_lift n z ≫ projection C n).left ∧
      (∀ i j, u i ≫ t = u j ≫ t ↔ z i = z j) ∧
      ∀ (y : Fin n → ComplexPoint C) (uy : Fin n → (Spec ↧ℂ ⟶ U.toScheme))
        (w : Spec ↧ℂ ⟶ V.toScheme),
        (∀ i, uy i ≫ U.ι = (y i).left) →
        w ≫ V.ι = (s2_lift n y ≫ projection C n).left →
        ∀ j : Fin n,
          (Scheme.ΓSpecIso ↧ℂ).hom
            ((w ≫ c).appTop ((Scheme.ΓSpecIso ↧(MvPolynomial (Fin n) ℂ)).inv
              (MvPolynomial.X j))) =
          MvPolynomial.eval (fun i => (Scheme.ΓSpecIso ↧ℂ).hom
            ((uy i ≫ t).appTop ((Scheme.ΓSpecIso ↧(MvPolynomial (Fin 1) ℂ)).inv
              (MvPolynomial.X (0 : Fin 1)))))
            (MvPolynomial.esymm (Fin n) ℂ (j.val+1)) := by
  by_cases hn : n = 0
  · subst n
    letI := (smooth_dimension_aux C 0).1
    exact curve_transport_zero C (symmetricPower C 0) (projection C 0) z
  · obtain ⟨_, _, hf, _, _⟩ := projective_quotient C n
    letI := hf
    obtain ⟨hinv, huniv⟩ := projection_universal C n
    exact curve_transport_positive C (symmetricPower C n) n (Nat.pos_of_ne_zero hn)
      (projection C n) hinv huniv z

-- Concrete independent example for `retained_comparison`.
example : Nonempty (g3_power E 1 ≅ symmetricPower E 1) := retained_comparison_example

-- Concrete independent example for `smooth_dimension`.
example : topologicalKrullDim (symmetricPower E 1).left = 1 := smooth_dimension_example

-- Concrete independent example for `degree_zero`.
example : Nonempty (g3_power E 0 ≅ symmetricPower E 0) := degree_zero_example

-- Concrete independent example for `branch_coordinates`.
example : coordinateIdeal 2 (0 : Fin 2) ≠ coordinateIdeal 2 (1 : Fin 2) := branch_coordinates_example

-- Concrete independent example for `point_addition`.
example : ∀ b : ComplexPoint (affine 1), s2c_branchInsertion (affine 1) 1 b ≫ g3_proj (affine 1) 2 (1 : Fin 2) = g3_proj (affine 1) 1 (0 : Fin 1) := point_addition_example

-- Concrete independent example for `branch_intersections`.
example : coordinateIdeal 2 (0 : Fin 2) ⊔ coordinateIdeal 2 (0 : Fin 2) ≠ coordinateIdeal 2 (0 : Fin 2) ⊔ coordinateIdeal 2 (1 : Fin 2) := branch_intersections_example

-- Concrete independent example for `excess_branches`.
example : Nonempty (branchIntersection E 0 2 (fun _ => Over.homMk finitePoint finitePoint_over)).left := excess_branches_example

-- Concrete independent example for `curve_coordinate_transport`.
example : ∃ z : Fin 2 → ComplexPoint (affine 1), z ∘ Equiv.swap (0 : Fin 2) 1 = z ∧ Equiv.swap (0 : Fin 2) 1 ≠ Equiv.refl _ := curve_coordinate_transport_example

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
