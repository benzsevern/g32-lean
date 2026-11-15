import HodgeLean.Foundations.Curves.SymmetricCharts.StageThree.IdealTransport
import HodgeLean.Foundations.Curves.SymmetricCharts.StageThree.Checks
import HodgeLean.Foundations.Curves.SymmetricCharts.StageThree.Defs
import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.Basic

/-! # Retained symmetric-power assembly

The five interfaces retain the quotient projection and the stage-zero branch
indices. Later blowup stages are separate from these initial branch charts.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageThree
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
variable (C : Over (Spec ↧ℂ)) [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
/-- Affine quotient charts transport with the specified projection.
Source: SGA 1, Exposé V, §1; Milne, Jacobian Varieties, §3.
HC no distance; AV milestone no distance.
-/
theorem retained_charts_aux (n : ℕ) (Q : Over (Spec ↧ℂ)) (q : g3_power C n ⟶ Q)
    (hinv : ∀ σ, s2_permute C n σ ≫ q = q)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : Q ⟶ T, q ≫ d = f) :
    ∃ e : symmetricPower C n ≅ Q, projection C n ≫ e.hom = q ∧
      ∀ W : Index C n, ∃ (V : Q.left.Opens) (a : affineChart C n W ≅ V.toScheme),
        a.hom ≫ V.ι = retainedChart C n e W ∧
        affineProjection C n W ≫ a.hom ≫ V.ι = W.val.ι ≫ q.left ∧
        q.left ⁻¹ᵁ V = W.val := by
  obtain ⟨e, he, _⟩ := StageTwo.retained_comparison C n Q q hinv huniv
  refine ⟨e, he, ?_⟩
  intro W
  obtain ⟨V, a, ha, hs, hv⟩ := chart_comparison C n W
  refine ⟨e.hom.left ''ᵁ V, a ≪≫ e.hom.left.isoImage V, ?_, ?_, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc, Scheme.Hom.isoImage_hom_ι]
    rw [← Category.assoc, ha]
    rfl
  · simp only [Iso.trans_hom, Category.assoc, Scheme.Hom.isoImage_hom_ι]
    rw [← Category.assoc a.hom, ← Category.assoc, hs, Category.assoc]
    exact congrArg (fun f => W.val.ι ≫ f.left) he
  · rw [← he]
    change ((projection C n).left ≫ e.hom.left) ⁻¹ᵁ (e.hom.left ''ᵁ V) = _
    rw [Scheme.Hom.comp_preimage, e.hom.left.preimage_image_eq, hv]


/-- The retained quotient has smooth relative dimension and independent Krull dimension, including the empty power.
Source: Milne, Jacobian Varieties, §3, Proposition 3.2.
HC no distance; AV milestone no distance.
-/
theorem retained_geometry_aux (hdim : TopologicalSpace.dim C.left = 1) (n : ℕ) (Q : Over (Spec ↧ℂ)) (q : g3_power C n ⟶ Q)
    (hinv : ∀ σ, s2_permute C n σ ≫ q = q)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : Q ⟶ T, q ≫ d = f) :
    IsIntegral Q.left ∧ IsProjective Q.hom ∧
      SmoothOfRelativeDimension n Q.hom ∧ topologicalKrullDim Q.left = n ∧
      (n = 0 → Nonempty (Q ≅ Over.mk (𝟙 (Spec ↧ℂ)))) := by
  letI : SmoothOfRelativeDimension 1 C.hom := by
    simpa only [hdim] using
      (inferInstance : SmoothOfRelativeDimension (TopologicalSpace.dim C.left) C.hom)
  obtain ⟨e, he, _⟩ := StageTwo.retained_comparison C n Q q hinv huniv
  haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  haveI : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  obtain ⟨hi, hp, _⟩ := projective_quotient C n
  letI := hi
  letI := hp
  have hQ : IsIntegral Q.left := IsIntegral.of_isIso e.hom.left
  letI := hQ
  have hP : IsProjective Q.hom := by
    obtain ⟨P⟩ := IsProjective.nonempty_presentation (f := (symmetricPower C n).hom)
    letI := P.isClosedImmersion
    refine ⟨⟨{ ambientDimension := P.ambientDimension
               immersion := e.inv.left ≫ P.immersion
               immersion_toBase := ?_ }⟩⟩
    rw [Category.assoc, P.immersion_toBase, Over.w]
  letI := (StageTwo.smooth_dimension C n).1
  have hS : SmoothOfRelativeDimension n Q.hom := by
    rw [← Over.w e.inv]
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0+n)
        (e.inv.left ≫ (symmetricPower C n).hom))
  letI := hS
  refine ⟨hQ, hP, hS, ?_, ?_⟩
  · rw [Scheme.topologicalKrullDim_eq_orderKrullDim]
    exact SmoothOfRelativeDimension.orderKrullDim_eq_complex (f := Q.hom) (d := n)
  · intro hn
    subst n
    exact ⟨e.symm ≪≫ (StageTwo.degree_zero C).choose⟩


/-- The exact retained symmetric-power existential, with complex orbit fibres and arbitrary-target descent.
Source: Schoen (1988), Remark 1.4; Milne, Jacobian Varieties, §3; SGA 1, Exposé V, §1.
HC no distance; AV milestone no distance.
-/
theorem symmetric_power_assembly_aux (hdim : TopologicalSpace.dim C.left = 1) (h : ℕ) :
    ∃ (B : Over (Spec ↧ℂ)) (γ : g3_power C h ⟶ B),
      ∃ (_ : IsIntegral B.left), Smooth B.hom ∧ IsProjective B.hom ∧
      TopologicalSpace.dim B.left = h ∧ IsFinite γ.left ∧
      Function.Surjective (Point.map γ) ∧
      (∀ σ, s2_permute C h σ ≫ γ = γ) ∧
      (∀ x y : ComplexPoint (g3_power C h), Point.map γ x = Point.map γ y ↔
        ∃ σ, Point.map (s2_permute C h σ) x = y) ∧
      (∀ (T : Over (Spec ↧ℂ)) (f : g3_power C h ⟶ T),
        (∀ σ, s2_permute C h σ ≫ f = f) →
        ∃! d : B ⟶ T, γ ≫ d = f) := by
  obtain ⟨B, γ, hi, hp, hf, hs, hinv, ho, hu, _⟩ :=
    s2_symmetricPower_projectiveQuotient C h
  obtain ⟨_, _, hS, _, _⟩ := retained_geometry_aux C hdim h B γ hinv hu
  letI := hi
  letI := hS
  haveI : Smooth B.hom := SmoothOfRelativeDimension.smooth h B.hom
  exact ⟨B, γ, hi, inferInstance, hp, SmoothOfRelativeDimension.dim_eq B.hom h,
    hf, hs, hinv, ho, hu⟩


/-- Retained finite subsets enumerate distinct points and preserve the actual sum ideal and pair order.
Source: Schoen (1988), §2, pp. 12–14, Lemma 2.2.
HC no distance; AV milestone no distance.
-/
theorem paired_subset_indexing_aux (h r : ℕ) (B : Over (Spec ↧ℂ)) (γ : g3_power C (h+1) ⟶ B)
    (hinv : ∀ σ, s2_permute C (h+1) σ ≫ γ = γ)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C (h+1) ⟶ T),
      (∀ σ, s2_permute C (h+1) σ ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f)
    (z : Fin (2*r) → ComplexPoint C) (hz : Function.Injective z) :
    (∀ J : Finset (Fin (2*r)), Function.Injective (subsetPoints z J) ∧
      J.sup (stageZeroBranches C B h r γ z) =
        ⨆ i : Fin J.card, s2c_branchIdeal C B h γ (subsetPoints z J i)) ∧
      ∀ i : Fin r, stageZeroBranches C B h r γ z (pairLabel r i 0) ⊔
        stageZeroBranches C B h r γ z (pairLabel r i 1) =
          s2c_branchIdeal C B h γ (z ⟨2*i.val, by omega⟩) ⊔
          s2c_branchIdeal C B h γ (z ⟨2*i.val+1, by omega⟩) := by
  constructor
  · intro J
    constructor
    · exact hz.comp (Subtype.val_injective.comp (J.orderIsoOfFin rfl).injective)
    · apply le_antisymm
      · apply Finset.sup_le
        intro j hj
        obtain ⟨i, hi⟩ := (J.orderIsoOfFin rfl).surjective ⟨j, hj⟩
        exact le_iSup_of_le i (by
          change s2c_branchIdeal C B h γ (z j) ≤
            s2c_branchIdeal C B h γ (z ((J.orderIsoOfFin rfl i).val))
          rw [hi])
      · apply iSup_le
        intro i
        exact Finset.le_sup (f := stageZeroBranches C B h r γ z)
          (J.orderIsoOfFin rfl i).property
  · intro i
    rfl

/-- Every retained stage-zero finite intersection has its smooth structure and local conormal frame, with excess intersections empty.
Source: Schoen (1988), Lemma 2.2, pp. 13–14; Hartshorne, Algebraic Geometry, II.8.
HC no distance; AV milestone no distance.
-/
theorem stage_zero_assembly_aux (hdim : TopologicalSpace.dim C.left = 1) (h r : ℕ) (B : Over (Spec ↧ℂ)) (γ : g3_power C (h+1) ⟶ B)
    (hinv : ∀ σ, s2_permute C (h+1) σ ≫ γ = γ)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C (h+1) ⟶ T),
      (∀ σ, s2_permute C (h+1) σ ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f)
    (z : Fin (2*r) → ComplexPoint C) (hz : Function.Injective z) :
    Smooth B.hom ∧ IsProjective B.hom ∧ IsIntegral B.left ∧
      ∀ J : Finset (Fin (2*r)),
        Smooth (s2c_subscheme B (J.sup (stageZeroBranches C B h r γ z))).hom ∧
        (∀ x : (s2c_subscheme B (J.sup (stageZeroBranches C B h r γ z))).left,
          ∃ U : (s2c_subscheme B (J.sup (stageZeroBranches C B h r γ z))).left.Opens,
            x ∈ U ∧ Nonempty (Scheme.Modules.restrict
              (s2c_conormal (s2c_subschemeι B (J.sup (stageZeroBranches C B h r γ z))).left) U.ι ≅
                (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) :
                  U.toScheme.Modules))) ∧
        (h+1 < J.card → IsEmpty (s2c_subscheme B
          (J.sup (stageZeroBranches C B h r γ z))).left) := by
  classical
  letI : SmoothOfRelativeDimension 1 C.hom := by
    simpa only [hdim] using
      (inferInstance : SmoothOfRelativeDimension (TopologicalSpace.dim C.left) C.hom)
  obtain ⟨hB, hp, hS, _, _⟩ := retained_geometry_aux C hdim (h+1) B γ hinv huniv
  letI := hB
  letI := hS
  haveI : Smooth B.hom := SmoothOfRelativeDimension.smooth (h+1) B.hom
  refine ⟨inferInstance, hp, hB, ?_⟩
  intro J
  obtain ⟨hb, hsum⟩ := (paired_subset_indexing_aux C h r B γ hinv huniv z hz).1 J
  obtain ⟨e, he, _⟩ := StageTwo.retained_comparison C (h+1) B γ hinv huniv
  let eL := (Over.forget (Spec ↧ℂ)).mapIso e
  let I := StageTwo.intersectionIdeal C h J.card (subsetPoints z J)
  have hmap : I.map eL.hom = J.sup (stageZeroBranches C B h r γ z) := by
    rw [hsum]
    change idealTransport eL (⨆ i, StageTwo.branchIdeal C h (subsetPoints z J i)) = _
    rw [(idealTransport eL).map_iSup]
    congr 1
    funext i
    change ((s2c_branchInsertion C h (subsetPoints z J i) ≫
      projection C (h+1)).left.ker).map e.hom.left = _
    rw [Scheme.IdealSheafData.map_ker]
    change ((s2c_branchInsertion C h (subsetPoints z J i) ≫
      projection C (h+1)) ≫ e.hom).left.ker = _
    rw [Category.assoc, he]
    rfl
  let eS : I.subscheme ≅ (J.sup (stageZeroBranches C B h r γ z)).subscheme :=
    subschemeTransport eL I ≪≫ eqToIso (congrArg (fun K => K.subscheme) hmap)
  have heS : eS.hom ≫ (J.sup (stageZeroBranches C B h r γ z)).subschemeι =
      I.subschemeι ≫ e.hom.left := by
    dsimp only [eS, Iso.trans_hom]
    have hcast (K L : B.left.IdealSheafData) (hKL : K = L) :
        (eqToIso (congrArg (fun A => A.subscheme) hKL)).hom ≫ L.subschemeι =
          K.subschemeι := by
      cases hKL
      exact Category.id_comp _
    rw [Category.assoc, hcast _ _ hmap, subschemeTransport_hom_ι]
    rfl
  let eO : StageTwo.branchIntersection C h J.card (subsetPoints z J) ≅
      s2c_subscheme B (J.sup (stageZeroBranches C B h r γ z)) :=
    Over.isoMk eS (by
      change eS.hom ≫ ((J.sup (stageZeroBranches C B h r γ z)).subschemeι ≫ B.hom) = _
      rw [← Category.assoc, heS, Category.assoc, Over.w e.hom]
      rfl)
  by_cases hk : J.card ≤ h+1
  · have hD := (StageTwo.branch_intersections C h J.card hk (subsetPoints z J) hb).2.1
    letI := hD
    haveI : IsIso eO.inv.left := (Over.forget _).map_isIso eO.inv
    have hT : SmoothOfRelativeDimension (h+1-J.card)
        (s2c_subscheme B (J.sup (stageZeroBranches C B h r γ z))).hom := by
      rw [← Over.w eO.inv]
      simpa only [Nat.zero_add] using
        (inferInstance : SmoothOfRelativeDimension (0+(h+1-J.card))
          (eO.inv.left ≫ (StageTwo.branchIntersection C h J.card (subsetPoints z J)).hom))
    letI := hT
    refine ⟨SmoothOfRelativeDimension.smooth (h+1-J.card) _, ?_, ?_⟩
    · intro x
      letI : SmoothOfRelativeDimension ((h+1-J.card)+J.card) B.hom := by
        simpa only [Nat.sub_add_cancel hk] using hS
      letI : IsClosedImmersion (s2c_subschemeι B
          (J.sup (stageZeroBranches C B h r γ z))).left := by
        change IsClosedImmersion (J.sup (stageZeroBranches C B h r γ z)).subschemeι
        infer_instance
      exact s2e_smooth_closedImmersion_conormal_frames _ B (h+1-J.card) J.card
        (s2c_subschemeι B (J.sup (stageZeroBranches C B h r γ z))) x
    · intro hlt
      omega
  · have hlt : h+1 < J.card := by omega
    letI := StageTwo.excess_branches C h J.card hlt (subsetPoints z J) hb
    haveI : IsEmpty (s2c_subscheme B
        (J.sup (stageZeroBranches C B h r γ z))).left :=
      Function.isEmpty eO.inv.left
    exact ⟨inferInstance, fun x => isEmptyElim x, fun _ => inferInstance⟩


example := @retained_charts_example
example := @retained_geometry_example
example := @symmetric_power_assembly_example
example := @paired_subset_indexing_example
example := @stage_zero_assembly_example

end HodgeLean.Foundations.Curves.SymmetricCharts.StageThree
