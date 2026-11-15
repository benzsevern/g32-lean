import HodgeLean.Foundations.Program.G32Native.PairedC3FullPoleDimension
import HodgeLean.Foundations.Program.G32Native.PairedC3FullFibreConormal
import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveFactorCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedResidualPoleEnvelope
import HodgeLean.Foundations.Program.G32Native.PairedResidualSymmetricAbel
import HodgeLean.Foundations.Program.G32Native.InitialResidueData

/-! # The full Abel fibre containing the supplied initial slice -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter
open scoped BigOperators Manifold ContDiff Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- The retained initial residue data factors through a full projective
Abel fibre with its genus-rank conormal frame.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(ii);
ACGH, Geometry of Algebraic Curves I, IV.1. -/
theorem paired_c3_initial_full_fibre_coordinates
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r : ℕ) (hr : 0 < r)
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    [IsClosedImmersion ℓ.left]
    (D : G32InitialResidueData Z B k r y hy γ ℓ) :
    ∃ f : Over.mk (ProjectiveSpace.toBase (Fin ((k + r - 1) + 1)) (Spec ↧ℂ)) ⟶ B,
      IsClosedImmersion f.left ∧
      Nonempty (s2c_conormal f.left ≅
        (SheafOfModules.free (R :=
          (ProjectiveSpace (Fin ((k + r - 1) + 1)) (Spec ↧ℂ)).ringCatSheaf) (Fin (k + 1 - r)))) ∧
      ∃ i : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶
          Over.mk (ProjectiveSpace.toBase (Fin ((k + r - 1) + 1)) (Spec ↧ℂ)),
        IsClosedImmersion i.left ∧ i ≫ f = ℓ ∧
          Nonempty (PairedC3ProjectiveFactorCoordinates k (k + r - 1) _ i.left) := by
  classical
  letI := D.curve
  letI := D.finite
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  let h := Module.finrank_fin_fun (n := 1) ℂ
  let S := Finset.univ.image y
  have hS (p : ComplexPoint Z) : p ∈ S ↔ p ∈ Set.range y := by simp [S]
  obtain ⟨W, hfin, hW, F, hF, hFg⟩ := paired_residual_pole_envelope h D.w
    (fun j => y ⟨2 * j.val + 1, by omega⟩) D.hres S D.horder
    (fun j p hp => D.hout j p (fun hy => hp ((hS p).mpr hy)))
  letI : Module.Finite ℂ W := hfin
  have hWS : ∀ q, q ∈ W ↔ b4c_IsMeroForm h q ∧
      (∀ p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h q p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc h q p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q ⟨p, u⟩ = 0 := by
    intro q
    simpa only [hS, WithTop.coe_one] using hW q
  have hdim := paired_c3_full_pole_space_finrank h (2 * r) (by omega) y hy W hWS
  have hg := D.hg
  have hlen : k + r - 1 + 1 = k + r := by omega
  have hdim' : Module.finrank ℂ W = (k + r - 1) + 1 := by omega
  have hgenus : Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) =
      k + 1 - r := by omega
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (by rw [hdim']; omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  let p := y ⟨0, by omega⟩
  obtain ⟨a, ha, _⟩ := residual_symmetric_abel_algebraic Z B (2 * k) γ hquot p
  have ha' : Point.map (γ ≫ a) = fun u => theta h
      (∑ j, analyticAbel h p (Point.map (g3_proj Z (2 * k) j) u)) := by
    funext u
    exact (Point.map_comp_apply γ a u).trans (ha u)
  obtain ⟨f, hf, hpoint, ⟨e⟩⟩ := paired_c3_full_abel_fibre_conormal Z B k r
    (k + r - 1) y hy W hWS D.hg hdim' γ hγ hsurj hquot hr p a ha' v hv
  refine ⟨f, hf, ⟨?_⟩, ?_⟩
  · simpa only [hgenus] using e
  let PP := Over.mk (ProjectiveSpace.toBase (Fin ((k + r - 1) + 1)) (Spec ↧ℂ))
  let PX := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  letI : IsIntegral PP.left := IntersectionProductScaf_projective_integral (k + r - 1)
  letI : IsIntegral PX.left := IntersectionProductScaf_projective_integral k
  letI : IsProjective PX.hom := ⟨⟨⟨k, 𝟙 _, Category.id_comp _⟩⟩⟩
  letI : IsClosedImmersion f.left := hf
  let ep := s2e_finiteDimensionalProjectivePointEquiv
    (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k D.hd
  let efull := s2e_finiteDimensionalProjectivePointEquiv (V := W) (k + r - 1) hdim'
  let q : ComplexPoint PX → ComplexPoint PP := fun z =>
    efull (Projectivization.map F hF (ep.symm (Point.map D.e.hom z)))
  obtain ⟨i, hi, hqi⟩ := paired_c3_factor_closed_immersion_with_point_map PX PP B ℓ f q (by
    intro z
    let t := ep.symm (Point.map D.e.hom z)
    change Point.map f (efull (Projectivization.map F hF t)) = Point.map ℓ z
    rw [hpoint]
    change residualProjectiveSystemPoint h y hy W (fun q => (hWS q.val).mp q.property)
      D.hg γ id (efull.symm (efull (Projectivization.map F hF t))) = _
    rw [efull.symm_apply_apply]
    rw [residualProjectiveSystemPoint_map_paired h D.w _ D.hres y hy D.horder D.hout
      D.hg W (fun q => (hWS q.val).mp q.property) F hF hFg γ id t]
    exact (congrFun D.point_formula (Point.map D.e.hom z)).symm.trans
      ((Point.map_comp_apply D.e.hom D.raw z).symm.trans
        (congrArg (fun l => Point.map l z) D.adapted).symm))
  haveI : IsClosedImmersion (i.left ≫ f.left) := by
    change IsClosedImmersion (i ≫ f).left
    rw [hi]
    infer_instance
  refine ⟨i, IsClosedImmersion.of_comp i.left f.left, hi, ⟨?_⟩⟩
  refine {
    targetSpace := W
    targetDimension := hdim'
    ambient := Iso.refl _
    embedding := F.comp D.coefficients.toLinearMap
    embedding_injective := hF.comp D.coefficients.injective
    point_formula := ?_ }
  intro u hu
  have he : Point.map D.e.hom (AlgebraicGeometry.ComplexProjectiveSpace.vectorToComplexPoint u hu) =
      AlgebraicGeometry.ComplexProjectiveSpace.vectorToComplexPoint
        ((D.coefficients.trans (Module.finBasisOfFinrankEq ℂ _ D.hd).equivFun) u)
        ((D.coefficients.trans (Module.finBasisOfFinrankEq ℂ _ D.hd).equivFun).map_ne_zero_iff.mpr hu) := by
    apply ComplexPoint.underlying_injective_of_locallyOfFiniteType
    rw [Point.underlying_map, D.coordinate_change]
    exact s2e_linearProjectiveOverIso_point _ u hu
  have hp := congrFun hqi (AlgebraicGeometry.ComplexProjectiveSpace.vectorToComplexPoint u hu)
  dsimp only [q] at hp
  rw [he, s2e_adapted_projective_parameter_mk k D.hd D.coefficients u hu] at hp
  change (AlgebraicGeometry.ComplexProjectiveSpace.vectorToComplexPoint u hu).left ≫ i.left =
    (efull (Projectivization.mk ℂ (F (D.coefficients u)) (by
      intro hz
      apply hu
      apply D.coefficients.injective
      apply hF
      simpa only [map_zero] using hz))).left ≫ 𝟙 _
  rw [Category.comp_id]
  exact congrArg Over.Hom.left hp



/-- Retain the source-fixed section coordinates in the full-fibre construction.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(ii). -/
theorem paired_c3_initial_full_fibre_marked
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r : ℕ) (hr : 0 < r)
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    [IsClosedImmersion ℓ.left]
    (D : G32InitialResidueData Z B k r y hy γ ℓ) :
    ∃ f : Over.mk (ProjectiveSpace.toBase (Fin (k + r)) (Spec ↧ℂ)) ⟶ B,
      IsClosedImmersion f.left ∧
      Nonempty (s2c_conormal f.left ≅
        (SheafOfModules.free (R :=
          (ProjectiveSpace (Fin (k + r)) (Spec ↧ℂ)).ringCatSheaf) (Fin (k + 1 - r)))) ∧
      ∃ i : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶
          Over.mk (ProjectiveSpace.toBase (Fin (k + r)) (Spec ↧ℂ)),
        IsClosedImmersion i.left ∧ i ≫ f = ℓ ∧
          Nonempty (PairedC3ProjectiveFactorCoordinates k (k + r - 1) _ i.left) := by
  have h := paired_c3_initial_full_fibre_coordinates Z B k r hr y hy γ hγ hsurj hquot ℓ D
  generalize hn : k + r - 1 = n at h ⊢
  have hc : n + 1 = k + r := by omega
  rw [← hc]
  exact h

/-- Forget the additional coordinate data while retaining the original full-fibre interface.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(ii);
ACGH, Geometry of Algebraic Curves I, IV.1. -/
theorem paired_c3_initial_full_fibre_aux
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r : ℕ) (hr : 0 < r)
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    [IsClosedImmersion ℓ.left]
    (D : G32InitialResidueData Z B k r y hy γ ℓ) :
    ∃ f : Over.mk (ProjectiveSpace.toBase (Fin (k + r)) (Spec ↧ℂ)) ⟶ B,
      IsClosedImmersion f.left ∧
      Nonempty (s2c_conormal f.left ≅
        (SheafOfModules.free (R :=
          (ProjectiveSpace (Fin (k + r)) (Spec ↧ℂ)).ringCatSheaf) (Fin (k + 1 - r)))) ∧
      ∃ i : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶
          Over.mk (ProjectiveSpace.toBase (Fin (k + r)) (Spec ↧ℂ)),
        IsClosedImmersion i.left ∧ i ≫ f = ℓ := by
  obtain ⟨f, hf, ef, i, hi, hcomp, _⟩ :=
    paired_c3_initial_full_fibre_marked Z B k r hr y hy γ hγ hsurj hquot ℓ D
  exact ⟨f, hf, ef, i, hi, hcomp⟩

#print axioms paired_c3_initial_full_fibre_coordinates
#print axioms paired_c3_initial_full_fibre_marked
#print axioms paired_c3_initial_full_fibre_aux
end HodgeLean.Foundations.Program.G32Native
