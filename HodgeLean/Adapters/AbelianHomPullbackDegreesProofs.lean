import HodgeLean.Adapters.AbelianHomPullback
import HodgeLean.Adapters.CupLeftFiltrationAbelian
import HodgeLean.Adapters.TorusCohomology
import HodgeLean.Foundations.ComplexSheafSingular
import HodgeLean.RealDefs.WeilClasses

/-! # Proof obligations for pullback along morphisms of abelian varieties in all degrees

One obligation per statement of `HodgeLean.Adapters.AbelianHomPullbackDegrees`. All are open. -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

section Cup

variable {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

theorem spec_homPullback_cup_aux (f : Y ⟶ X) {i j k : ℕ} (h : i + j = k) (a : HQ X i)
    (b : HQ X j) :
    homPullback f k ((cupProductOf X).cup h a b) =
      (cupProductOf Y).cup h (homPullback f i a) (homPullback f j b) := by
  apply (cupComparison Y k).injective
  simp only [homPullback, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, cupComparison_cup]
  exact Foundations.Singular.cohomologyMap_cup _ _ h _ _

theorem spec_homPullback_cupWedgeMap_aux (f : Y ⟶ X) (m : ℕ) :
    homPullback f m ∘ₗ (cupProductOf X).cupWedgeMap m =
      (cupProductOf Y).cupWedgeMap m ∘ₗ exteriorPower.map m (homPullback f 1) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
    exteriorPower.map_apply_ιMulti, CupProduct.cupWedgeMap_ιMulti]
  apply (cupComparison Y m).injective
  simp only [homPullback, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, cupComparison_cupMulti]
  exact Foundations.Singular.cohomologyMap_cupMulti _ m _

end Cup

section Abelian

variable {X Y : Over (Spec ↧ℂ)} [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom] [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

theorem spec_homPullback_eq_cupWedgeEquiv_aux (f : Y ⟶ X) (m : ℕ) :
    homPullback f m =
      ((torusCohomology_cupProductOf Y).cupWedgeEquiv m).toLinearMap ∘ₗ
        exteriorPower.map m (homPullback f 1) ∘ₗ
          ((torusCohomology_cupProductOf X).cupWedgeEquiv m).symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨w, rfl⟩ := ((torusCohomology_cupProductOf X).cupWedgeEquiv m).surjective x
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply]
  simp only [TorusCohomology.cupWedgeEquiv_apply]
  exact LinearMap.congr_fun (spec_homPullback_cupWedgeMap_aux f m) w

/-- The `m`-th exterior power of a scalar multiple: `⋀^m (c • φ) = c ^ m • ⋀^m φ`.
Source: multilinearity of `exteriorPower.ιMulti`. -/
theorem exteriorPower_map_smul {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] (c : ℚ) (φ : V →ₗ[ℚ] W) (m : ℕ) :
    exteriorPower.map m (c • φ) = c ^ m • exteriorPower.map m φ := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply,
    exteriorPower.map_apply_ιMulti]
  have := (exteriorPower.ιMulti ℚ m (M := W)).toMultilinearMap.map_smul_univ
    (fun _ => c) (fun i => φ (v i))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  simp only [Function.comp_def, LinearMap.smul_apply]
  exact this

example (φ : ℚ →ₗ[ℚ] ℚ) : exteriorPower.map 2 ((3 : ℚ) • φ) = (9 : ℚ) • exteriorPower.map 2 φ := by
  rw [exteriorPower_map_smul]; norm_num

theorem spec_homPullback_zpow_degree_aux (f : Y ⟶ X) (n : ℤ) (m : ℕ) :
    homPullback (f ^ n) m = ((n : ℚ) ^ m) • homPullback f m := by
  rw [spec_homPullback_eq_cupWedgeEquiv_aux (f ^ n) m, spec_homPullback_eq_cupWedgeEquiv_aux f m,
    spec_homPullback_zpow, exteriorPower_map_smul, LinearMap.smul_comp, LinearMap.comp_smul]

omit [GrpObj X] [GrpObj Y] in
/-- The complexified pullback commutes with rational conjugation. -/
private theorem homPullback_baseChange_sigmaQ (f : Y ⟶ X) (n : ℕ) (x : ℂ ⊗[ℚ] HQ X n) :
    (homPullback f n).baseChange ℂ (HodgeBlocks.sigmaQ (HQ X n) x) =
      HodgeBlocks.sigmaQ (HQ Y n) ((homPullback f n).baseChange ℂ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z v =>
    change (homPullback f n).baseChange ℂ (HodgeBlocks.sigmaQR (HQ X n) (z ⊗ₜ v)) =
      HodgeBlocks.sigmaQR (HQ Y n) ((homPullback f n).baseChange ℂ (z ⊗ₜ v))
    rw [HodgeBlocks.sigmaQ_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      HodgeBlocks.sigmaQ_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [GrpObj X] [IsProjective X.hom] in
/-- The `(1, 0)` piece in degree one is the pullback of `F^1`, since `conj F^0 = ⊤`. -/
private theorem cohomologyHodgePiece_one_one_zero :
    cohomologyHodgePiece X 1 (1, 0) =
      (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) := by
  have h : ((1 : ℤ), (0 : ℤ)).1 + ((1 : ℤ), (0 : ℤ)).2 = ((1 : ℕ) : ℤ) := by norm_num
  rw [cohomologyHodgePiece, ite_eq_left_of_eq_true _ _ (eq_true h)]
  congr 1
  change F^1 H_dR^((1 : ℕ) : ℤ)(X) ⊓ conjHodgeFiltrationComplexSubmodule X 0 ((1 : ℕ) : ℤ) = _
  refine inf_eq_left.mpr fun α _ => (mem_conjHodgeFiltrationComplexSubmodule X α).mpr ?_
  rw [hodgeFiltration_eq_top_of_nonpos X le_rfl]
  exact Submodule.mem_top

theorem spec_homPullback_hodgePiece_one_aux (f : Y ⟶ X) [IsMonHom f] (pq : ℤ × ℤ) :
    (cohomologyHodgePiece X 1 pq).map ((homPullback f 1).baseChange ℂ) ≤
      cohomologyHodgePiece Y 1 pq := by
  have h10 : (cohomologyHodgePiece X 1 (1, 0)).map ((homPullback f 1).baseChange ℂ) ≤
      cohomologyHodgePiece Y 1 (1, 0) := by
    rw [cohomologyHodgePiece_one_one_zero, cohomologyHodgePiece_one_one_zero]
    exact spec_homPullback_hodgeFiltration f
  obtain ⟨p, q⟩ := pq
  by_cases hpq : (p, q) = (1, 0)
  · rw [hpq]; exact h10
  by_cases hqp : (p, q) = (0, 1)
  · rw [hqp, ← cohomologyHodgePiece_map_sigmaQ X 1 1 0, ← cohomologyHodgePiece_map_sigmaQ Y 1 1 0]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [homPullback_baseChange_sigmaQ]
    exact Submodule.mem_map_of_mem (h10 (Submodule.mem_map_of_mem hx))
  · rw [cohomologyHodgePiece_one_eq_bot X (p, q) hpq hqp,
      Submodule.map_bot]
    exact bot_le

omit [GrpObj X] [GrpObj Y] in
/-- The complexified pullback of a complexified cup of degree-one classes is the complexified cup
of their pullbacks: both sides are `ℂ`-multilinear, and on rational vectors this is the `cupMulti`
form of `spec_homPullback_cupWedgeMap_aux`. -/
private theorem homPullback_baseChange_cupMultiC (f : Y ⟶ X) (m : ℕ)
    (v : Fin m → ℂ ⊗[ℚ] HQ X 1) :
    (homPullback f m).baseChange ℂ ((cupProductOf X).cupMultiC m v) =
      (cupProductOf Y).cupMultiC m (fun i => (homPullback f 1).baseChange ℂ (v i)) := by
  let e := Module.Free.chooseBasis ℚ (HQ X 1)
  have key : ((homPullback f m).baseChange ℂ).compMultilinearMap
      ((cupProductOf X).cupMultiC m) =
      ((cupProductOf Y).cupMultiC m).compLinearMap
        (fun _ => (homPullback f 1).baseChange ℂ) := by
    refine Module.Basis.ext_multilinear (fun _ => e.baseChange ℂ) fun σ => ?_
    simp only [Module.Basis.baseChange_apply, LinearMap.compMultilinearMap_apply,
      MultilinearMap.compLinearMap_apply, LinearMap.baseChange_tmul]
    rw [CupProduct.cupMultiC_tmul (cupProductOf X) m (fun i => e (σ i)),
      CupProduct.cupMultiC_tmul (cupProductOf Y) m (fun i => homPullback f 1 (e (σ i))),
      LinearMap.baseChange_tmul]
    congr 1
    have h := LinearMap.congr_fun (spec_homPullback_cupWedgeMap_aux f m)
      (exteriorPower.ιMulti ℚ m (fun i => e (σ i)))
    simpa only [LinearMap.comp_apply, CupProduct.cupWedgeMap_ιMulti,
      exteriorPower.map_apply_ιMulti, Function.comp_def] using h
  exact DFunLike.congr_fun key v

theorem spec_homPullback_hodgePiece_aux (f : Y ⟶ X) [IsMonHom f] (m : ℕ) (pq : ℤ × ℤ) :
    (cohomologyHodgePiece X m pq).map ((homPullback f m).baseChange ℂ) ≤
      cohomologyHodgePiece Y m pq := by
  have hDX := spec_hodgeDecomposition_of_cupLeft_alone X (torusCohomology_cupProductOf X)
    (spec_cupLeft_cupProductOf X)
  have hCX := spec_cupFiltered_of_cupLeft_alone X (torusCohomology_cupProductOf X)
    (spec_cupLeft_cupProductOf X)
  have hDY := spec_hodgeDecomposition_of_cupLeft_alone Y (torusCohomology_cupProductOf Y)
    (spec_cupLeft_cupProductOf Y)
  have hCY := spec_cupFiltered_of_cupLeft_alone Y (torusCohomology_cupProductOf Y)
    (spec_cupLeft_cupProductOf Y)
  let := (torusCohomology_cupProductOf X).finite
  let := (finiteBetti_of_torusCohomology (torusCohomology_cupProductOf X)).finite m
  let := (torusCohomology_cupProductOf Y).finite
  let := (finiteBetti_of_torusCohomology (torusCohomology_cupProductOf Y)).finite m
  have hP := comap_cohomologyHodgePiece_eq_exteriorPowerH (finiteBetti_abelian X)
    (spec_bettiDeRhamIso_abelian X) hDX (torusCohomology_cupProductOf X) hCX m pq
  rw [exteriorPowerH_eq_wedgePiece] at hP
  rw [← Submodule.map_comap_eq_of_surjective
    (HodgeBlocks.QHodgeStructure.complexificationCongr (V := _) (W := HQ X m)
      ((torusCohomology_cupProductOf X).cupWedgeEquiv m)).surjective
    (cohomologyHodgePiece X m pq), hP, Submodule.map_le_iff_le_comap,
    Submodule.map_le_iff_le_comap, wedgePiece, Submodule.span_le]
  rintro _ ⟨d, v, hd, hv, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_comap, LinearEquiv.coe_coe,
    (torusCohomology_cupProductOf X).complexificationCongr_symm_ιMulti,
    homPullback_baseChange_cupMultiC,
    ← (torusCohomology_cupProductOf Y).complexificationCongr_symm_ιMulti]
  refine map_wedgePiece_le_cohomologyHodgePiece (finiteBetti_abelian Y)
    (spec_bettiDeRhamIso_abelian Y) hDY (torusCohomology_cupProductOf Y) hCY m pq
    (Submodule.mem_map_of_mem (Submodule.subset_span ⟨d, _, hd, fun i => ?_, rfl⟩))
  have hvi : v i ∈ cohomologyHodgePiece X 1 (d i) := hv i
  exact spec_homPullback_hodgePiece_one_aux f (d i) (Submodule.mem_map_of_mem hvi)

theorem spec_homPullback_hodgeClasses_aux (f : Y ⟶ X) [IsMonHom f] (p : ℕ) (x : HQ X (2 * p))
    (hx : (x : H^(2 * p)(X; ℚ)) ∈ Hdg^p(X; ℚ)) :
    (homPullback f (2 * p) x : H^(2 * p)(Y; ℚ)) ∈ Hdg^p(Y; ℚ) := by
  rw [mem_hodgeClasses_iff_tmul_mem] at hx ⊢
  have h := spec_homPullback_hodgePiece_aux f (2 * p) ((p : ℤ), (p : ℤ))
    (Submodule.mem_map_of_mem hx)
  rwa [LinearMap.baseChange_tmul] at h

theorem spec_homPullback_weilClassOf_aux (f : Y ⟶ X) [IsMonHom f] (hF : FiniteBetti X)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) {d : ℚ}
    (A : letI := (torusCohomology_cupProductOf X).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf hF hB hD (torusCohomology_cupProductOf X)).weight1 d)
    (hW : letI := (torusCohomology_cupProductOf X).finite; A.IsWeilType) :
    letI := (torusCohomology_cupProductOf X).finite
    (weilClassOf hF hB hD (torusCohomology_cupProductOf X) A hW).map (homPullback f _) ≤
      Hdg^(Module.finrank ℂ ↥(A.Vs ⊓
        (abelianVarietyCohomologyOf hF hB hD (torusCohomology_cupProductOf X)).weight1.H
          (1, 0)))(Y; ℚ) := by
  let := (torusCohomology_cupProductOf X).finite
  have hX := weilClassOf_le_hdg hF hB hD (torusCohomology_cupProductOf X)
    (spec_cupFiltered_of_cupLeft_alone X (torusCohomology_cupProductOf X)
      (spec_cupLeft_cupProductOf X)) A hW
  rintro _ ⟨x, hx, rfl⟩
  exact spec_homPullback_hodgeClasses_aux f _ x (hX hx)

end Abelian

end HodgeLean.Adapters
