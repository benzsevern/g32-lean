import HodgeLean.Foundations.Curves.SymmetricCharts.StageThree.Proofs

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
theorem retained_charts (n : ℕ) (Q : Over (Spec ↧ℂ)) (q : g3_power C n ⟶ Q)
    (hinv : ∀ σ, s2_permute C n σ ≫ q = q)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : Q ⟶ T, q ≫ d = f) :
    ∃ e : symmetricPower C n ≅ Q, projection C n ≫ e.hom = q ∧
      ∀ W : Index C n, ∃ (V : Q.left.Opens) (a : affineChart C n W ≅ V.toScheme),
        a.hom ≫ V.ι = retainedChart C n e W ∧
        affineProjection C n W ≫ a.hom ≫ V.ι = W.val.ι ≫ q.left ∧
        q.left ⁻¹ᵁ V = W.val :=
  retained_charts_aux C n Q q hinv huniv

/-- The retained quotient has smooth relative dimension and independent Krull dimension, including the empty power.
Source: Milne, Jacobian Varieties, §3, Proposition 3.2.
HC no distance; AV milestone no distance.
-/
theorem retained_geometry (hdim : TopologicalSpace.dim C.left = 1) (n : ℕ) (Q : Over (Spec ↧ℂ)) (q : g3_power C n ⟶ Q)
    (hinv : ∀ σ, s2_permute C n σ ≫ q = q)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : Q ⟶ T, q ≫ d = f) :
    IsIntegral Q.left ∧ IsProjective Q.hom ∧
      SmoothOfRelativeDimension n Q.hom ∧ topologicalKrullDim Q.left = n ∧
      (n = 0 → Nonempty (Q ≅ Over.mk (𝟙 (Spec ↧ℂ)))) :=
  retained_geometry_aux C hdim n Q q hinv huniv

/-- The exact retained symmetric-power existential, with complex orbit fibres and arbitrary-target descent.
Source: Schoen (1988), Remark 1.4; Milne, Jacobian Varieties, §3; SGA 1, Exposé V, §1.
HC no distance; AV milestone no distance.
-/
theorem symmetric_power_assembly (hdim : TopologicalSpace.dim C.left = 1) (h : ℕ) :
    ∃ (B : Over (Spec ↧ℂ)) (γ : g3_power C h ⟶ B),
      ∃ (_ : IsIntegral B.left), Smooth B.hom ∧ IsProjective B.hom ∧
      TopologicalSpace.dim B.left = h ∧ IsFinite γ.left ∧
      Function.Surjective (Point.map γ) ∧
      (∀ σ, s2_permute C h σ ≫ γ = γ) ∧
      (∀ x y : ComplexPoint (g3_power C h), Point.map γ x = Point.map γ y ↔
        ∃ σ, Point.map (s2_permute C h σ) x = y) ∧
      (∀ (T : Over (Spec ↧ℂ)) (f : g3_power C h ⟶ T),
        (∀ σ, s2_permute C h σ ≫ f = f) →
        ∃! d : B ⟶ T, γ ≫ d = f) :=
  symmetric_power_assembly_aux C hdim h

/-- Retained finite subsets enumerate distinct points and preserve the actual sum ideal and pair order.
Source: Schoen (1988), §2, pp. 12–14, Lemma 2.2.
HC no distance; AV milestone no distance.
-/
theorem paired_subset_indexing (h r : ℕ) (B : Over (Spec ↧ℂ)) (γ : g3_power C (h+1) ⟶ B)
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
          s2c_branchIdeal C B h γ (z ⟨2*i.val+1, by omega⟩) :=
  paired_subset_indexing_aux C h r B γ hinv huniv z hz

/-- Every retained stage-zero finite intersection has its smooth structure and local conormal frame, with excess intersections empty.
Source: Schoen (1988), Lemma 2.2, pp. 13–14; Hartshorne, Algebraic Geometry, II.8.
HC no distance; AV milestone no distance.
-/
theorem stage_zero_assembly (hdim : TopologicalSpace.dim C.left = 1) (h r : ℕ) (B : Over (Spec ↧ℂ)) (γ : g3_power C (h+1) ⟶ B)
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
          (J.sup (stageZeroBranches C B h r γ z))).left) :=
  stage_zero_assembly_aux C hdim h r B γ hinv huniv z hz

example := @retained_charts_example
example := @retained_geometry_example
example := @symmetric_power_assembly_example
example := @paired_subset_indexing_example
example := @stage_zero_assembly_example

end HodgeLean.Foundations.Curves.SymmetricCharts.StageThree
