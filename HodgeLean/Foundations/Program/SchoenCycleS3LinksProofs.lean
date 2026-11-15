import HodgeLean.Foundations.Program.SchoenCycleS3LinearPoints
import HodgeLean.Foundations.Program.SchoenCycleS3ConormalOnCharts
import HodgeLean.Foundations.Program.SchoenCycleS3ResidueTransport
import HodgeLean.Foundations.Program.SchoenCycleS3Cartier
import HodgeLean.Foundations.Program.SchoenCycleS3IntersectionBase
import HodgeLean.Foundations.Program.SchoenCycleProjectivePoints
import HodgeLean.Foundations.Program.SchoenCycleCartierAvoidance
import HodgeLean.Foundations.Program.SchoenCycleS2b
import HodgeLean.Foundations.Program.SchoenCycleStageDefs

/-! # S3 geometric links
Implication from coordinate ideals and coherent prefixes to residual restrictions
and intersection geometry over the complex base. HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Manifold AlgebraicGeometry.ComplexProjectiveSpace
open scoped BigOperators ContDiff
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

theorem s2e_chain_pair_cartier_on_slice_aux
    (k : ℕ) (j : Fin (k + 1)) :
    ∀ x : ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ),
      ∃ U : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).affineOpens,
        x ∈ U.1 ∧ Nonempty (((s2e_s2b_residueIdeal k j).ideal U)
          ≃ₗ[Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ), U)] Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ), U)) := by
  intro x
  have hc : x ∈ ⨆ i : Fin (k + 1), projectiveSpaceBasicOpen k (MvPolynomial.X i) := by
    rw [show (⨆ i : Fin (k + 1), projectiveSpaceBasicOpen k (MvPolynomial.X i)) = ⊤ from
      (Limits.pullback.snd (Limits.terminal.from (Spec ↧ℂ))
        (Limits.terminal.from (Proj (UniversalGrading k)))).iSup_preimage_eq_top
          (iSup_coordinateBasicOpen_eq_top k)]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
  refine ⟨⟨s2e_s2b_chart i ''ᵁ ⊤,
    (isAffineOpen_top _).image_of_isOpenImmersion _⟩, ?_, s2e_residue_chart_free i j⟩
  change x ∈ s2e_s2b_chart i ''ᵁ ⊤
  change x ∈ (s2e_s2b_chart i) '' (⊤ : (Spec ↧(MvPolynomial {q : Fin (k + 1) // q ≠ i} ℂ)).Opens)
  change x ∈ (s2e_s2b_chart i) '' Set.univ
  rw [Set.image_univ, s2e_chart_range]
  exact hi

theorem s2e_chain_unprocessed_pair_transverse_aux
    (k r n : ℕ) (hn : n ≤ r) (ι : Fin r ↪ Fin (k + 1))
    (B : Fin (n + 1) → Over (Spec ↧ℂ))
    (b : ∀ i : Fin n, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (htransform : ∀ (i : Fin n) t,
      D i.succ t = s2c_strictTransform (b i).left (D i.castSucc t)
        (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
          D i.castSucc ⟨2 * i.val + 1, by omega⟩))
    (hcartier : ∀ (i : Fin n) (x : (B i.succ).left),
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
          D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap (b i).left).ideal U)
            ≃ₗ[Γ((B i.succ).left, U)] Γ((B i.succ).left, U)))
    (ℓ : ∀ i, Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B i)
    (hfac : ∀ i : Fin n, ℓ i.succ ≫ b i = ℓ i.castSucc)
    (hresidue : ∀ j : Fin r,
      (D 0 ⟨2 * j.val, by omega⟩).comap (ℓ 0).left = s2e_s2b_residueIdeal k (ι j) ∧
      (D 0 ⟨2 * j.val + 1, by omega⟩).comap (ℓ 0).left = s2e_s2b_residueIdeal k (ι j)) :
    ∀ j : Fin r, n ≤ j.val →
      (D (Fin.last n) ⟨2 * j.val, by omega⟩).comap (ℓ (Fin.last n)).left =
        s2e_s2b_residueIdeal k (ι j) ∧
      (D (Fin.last n) ⟨2 * j.val + 1, by omega⟩).comap (ℓ (Fin.last n)).left =
        s2e_s2b_residueIdeal k (ι j) := by
  have hall : ∀ i : Fin (n + 1), ∀ j : Fin r, i.val ≤ j.val →
      (D i ⟨2 * j.val, by omega⟩).comap (ℓ i).left = s2e_s2b_residueIdeal k (ι j) ∧
      (D i ⟨2 * j.val + 1, by omega⟩).comap (ℓ i).left = s2e_s2b_residueIdeal k (ι j) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      intro j hj
      exact hresidue j
    | succ i ih =>
      intro j hj
      change i.val + 1 ≤ j.val at hj
      let p : Fin r := ⟨i.val, by omega⟩
      have hp := ih p (by rfl)
      have hjprev := ih j (by change i.val ≤ j.val; omega)
      have hf : (ℓ i.succ).left ≫ (b i).left = (ℓ i.castSucc).left :=
        congrArg (fun f => f.left) (hfac i)
      have hk : (((D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
          D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap (b i).left).comap
            (ℓ i.succ).left) = s2e_s2b_residueIdeal k (ι p) := by
        rw [← Scheme.IdealSheafData.comap_comp, hf,
          Scheme.IdealSheafData.comap_sup]
        change (D i.castSucc ⟨2 * p.val, by omega⟩).comap (ℓ i.castSucc).left ⊔
          (D i.castSucc ⟨2 * p.val + 1, by omega⟩).comap (ℓ i.castSucc).left = _
        rw [hp.1, hp.2, sup_idem]
      have hne : ι p ≠ ι j := by
        intro he
        have hv := congrArg Fin.val (ι.injective he)
        change i.val = j.val at hv
        omega
      constructor
      · rw [htransform i]
        apply s2e_residue_strict_restriction k (ι j) (ι p) hne (b i).left (ℓ i.succ).left _ _ _ hk
        rw [← Scheme.IdealSheafData.comap_comp, hf]
        exact hjprev.1
      · rw [htransform i]
        apply s2e_residue_strict_restriction k (ι j) (ι p) hne (b i).left (ℓ i.succ).left _ _ _ hk
        rw [← Scheme.IdealSheafData.comap_comp, hf]
        exact hjprev.2
  exact hall (Fin.last n)

theorem s2e_chain_residue_conormal_aux
    (k : ℕ) (T : Finset (Fin (k + 1))) :
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    let I := s2e_s2b_intersectionIdeal k T
    ∀ x : (s2c_subscheme PP I).left,
      ∃ U : (s2c_subscheme PP I).left.Opens, x ∈ U ∧
        Nonempty (Scheme.Modules.restrict
          (s2c_conormal (s2c_subschemeι PP I).left) U.ι ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin T.card) :
            U.toScheme.Modules)) := by
  dsimp only
  let I := s2e_s2b_intersectionIdeal k T
  let c := I.subschemeι
  change ∀ x : I.subscheme, ∃ U : I.subscheme.Opens, x ∈ U ∧
    Nonempty (Scheme.Modules.restrict (s2c_conormal c) U.ι ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin T.card) : U.toScheme.Modules))
  intro x
  have hx : c x ∈ I.support := by
    change c x ∈ (I.support : Set _)
    rw [← I.range_subschemeι]
    exact ⟨x, rfl⟩
  have hc : c x ∈ ⨆ i : Fin (k + 1), projectiveSpaceBasicOpen k (MvPolynomial.X i) := by
    rw [show (⨆ i : Fin (k + 1), projectiveSpaceBasicOpen k (MvPolynomial.X i)) = ⊤ from
      (Limits.pullback.snd (Limits.terminal.from (Spec ↧ℂ))
        (Limits.terminal.from (Proj (UniversalGrading k)))).iSup_preimage_eq_top
          (iSup_coordinateBasicOpen_eq_top k)]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
  have hnot : i ∉ T := by
    intro hit
    have hle : s2e_s2b_residueIdeal k i ≤ I :=
      le_iSup_of_le i (le_iSup_of_le hit le_rfl)
    have hs := Scheme.IdealSheafData.support_antitone hle hx
    change c x ∈ ((s2e_s2b_residueIdeal k i).support : Set _) at hs
    rw [s2e_s2b_residueIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hs
    exact hs hi
  let U := c ⁻¹ᵁ (s2e_s2b_chart i).opensRange
  refine ⟨U, ?_, ?_⟩
  · change c x ∈ (s2e_s2b_chart i).opensRange
    change c x ∈ Set.range (s2e_s2b_chart i)
    rw [s2e_chart_range]
    exact hi
  · exact s2e_subschemeConormal_free_on_chart I (s2e_s2b_chart i) (Fin T.card)
      (s2e_residueChartActualConormal_free T i hnot)

theorem s2e_chain_residue_intersection_over_base_aux
    (k : ℕ) (T : Finset (Fin (k + 1))) (hT : T.card ≤ k) :
    Nonempty (s2c_subscheme
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
      (s2e_s2b_intersectionIdeal k T) ≅
      Over.mk (ProjectiveSpace.toBase (Fin (k - T.card + 1)) (Spec ↧ℂ))) := by
  exact s2e_coordinate_intersection_over k T hT

theorem s2e_chain_adapted_residue_ideals_aux
    (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (k r : ℕ)
    [FiniteDimensional ℂ (b3_HolForm E C)]
    (hd : Module.finrank ℂ (b3_HolForm E C × (Fin r → ℂ)) = k + 1)
    (b : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] (b3_HolForm E C × (Fin r → ℂ)))
    (ι : Fin r ↪ Fin (k + 1)) (hb : ∀ v j, (b v).2 j = v (ι j)) :
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm E C × (Fin r → ℂ)) k hd
    let H : Fin r → PP.left.IdealSheafData := fun j =>
      Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure
        (AlgebraicGeometry.Point.underlying ''
          {R : AlgebraicGeometry.ComplexPoint PP |
            ∃ (v : b3_HolForm E C × (Fin r → ℂ)) (hv : v ≠ 0),
              ep.symm R = Projectivization.mk ℂ v hv ∧ v.2 j = 0}))
    ∃ e : PP ≅ PP, ∀ j, (H j).comap e.hom.left = s2e_s2b_residueIdeal k (ι j) := by
  let a := b.trans (Module.finBasisOfFinrankEq ℂ
    (b3_HolForm E C × (Fin r → ℂ)) hd).equivFun
  refine ⟨s2e_linearProjectiveOverIso a, ?_⟩
  intro j
  let L : (b3_HolForm E C × (Fin r → ℂ)) →ₗ[ℂ] ℂ :=
    { toFun := fun v => v.2 j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact s2e_coefficient_ideal_transport k hd b L (ι j) (fun v => hb v j)
    (s2e_linearProjectiveOverIso a) (fun v hv => s2e_linearProjectiveOverIso_point a v hv)

end HodgeLean.Foundations.Program
