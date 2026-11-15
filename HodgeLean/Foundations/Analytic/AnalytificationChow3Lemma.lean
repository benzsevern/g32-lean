import HodgeLean.Foundations.Analytic.AnalytificationChow3Charts
import HodgeLean.Foundations.Analytic.AnalytificationChow3Product
import HodgeLean.Foundations.Analytic.AnalytificationChow3Cover
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Chow's lemma (F4g-C1 to C4 assembled)

For a proper `f : X ⟶ Y` over an affine Noetherian base `S`, with `X` of finite type over `S`,
there is a surjective `π : X' ⟶ X` with `π ≫ f` projective (`AnalytificationChow3_chow`):
- cover `X` by finitely many dense affine opens `Uᵢ` (`AnalytificationChow3_exists_dense_affine_cover`),
  so that `U = ⋂ Uᵢ` is dense;
- immerse each `Uᵢ` in `ℙ^{nᵢ}_Y` over `Y` (`AnalytificationChow3_exists_immersion`);
- let `P = ∏_Y ℙ^{nᵢ}_Y`, projective over `Y` (`AnalytificationChow3_exists_product`), and `X'`
  the scheme-theoretic closure of the graph of `U ⟶ P` in `X ×_Y P`;
- `X' ⟶ P` is a closed immersion (`AnalytificationChow3_isClosedImmersion_h`, using that `f` is
  proper), so `X' ⟶ Y` is projective; `π` is proper with range containing the dense `U`, so it is
  surjective.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace

namespace HodgeLean.Foundations.Analytic

/-- A scheme locally of finite type over an affine Noetherian scheme is locally Noetherian
(Hilbert's basis theorem on each affine open).
Source: Hartshorne, *Algebraic Geometry*, Ex. II.3.13(g) and §II.3; Mathlib
`Algebra.FiniteType.isNoetherianRing`. -/
theorem AnalytificationChow3_isLocallyNoetherian {X S : Scheme.{0}} [IsAffine S]
    [IsLocallyNoetherian S] (σ : X ⟶ S) [LocallyOfFiniteType σ] : IsLocallyNoetherian X where
  component_noetherian U := by
    have hft := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) σ inferInstance
      ⟨⊤, isAffineOpen_top S⟩ U le_top
    let := (σ.appLE ⊤ U.1 le_top).hom.toAlgebra
    have : Algebra.FiniteType Γ(S, ⊤) Γ(X, U.1) := hft
    have : IsNoetherianRing Γ(S, ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
    exact Algebra.FiniteType.isNoetherianRing Γ(S, ⊤) Γ(X, U.1)

example : IsLocallyNoetherian (Spec (CommRingCat.of ℤ)) :=
  AnalytificationChow3_isLocallyNoetherian (𝟙 _)

lemma AnalytificationChow3_dense_finset_inf {X : Scheme.{0}} {k : ℕ} (U : Fin k → X.Opens)
    (hU : ∀ i, Dense (U i : Set X)) (s : Finset (Fin k)) : Dense ((s.inf U : X.Opens) : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
    rw [Finset.inf_insert, TopologicalSpace.Opens.coe_inf]
    exact (hU a).inter_of_isOpen_left ih (U a).isOpen

/-- **Chow's lemma** over an affine Noetherian base `S`. For `f : X ⟶ Y` proper, with `X` locally
of finite type over `S` and quasi-compact, there is `π : X' ⟶ X` surjective with `π ≫ f`
projective and `X'` locally of finite type over `S`.
Source: EGA II, Théorème 5.6.1; Hartshorne, *Algebraic Geometry*, Ex. II.4.10. -/
theorem AnalytificationChow3_chow {X Y S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    (σX : X ⟶ S) (σY : Y ⟶ S) (f : X ⟶ Y) (hf : f ≫ σY = σX) [LocallyOfFiniteType σX]
    [CompactSpace X] [IsProper f] :
    ∃ (X' : Scheme.{0}) (π : X' ⟶ X), LocallyOfFiniteType (π ≫ σX) ∧ IsProjective (π ≫ f) ∧
      Surjective π := by
  have : IsLocallyNoetherian X := AnalytificationChow3_isLocallyNoetherian σX
  have : IsNoetherian X := {}
  obtain ⟨k, Ui, haff, hdense, hcov⟩ := AnalytificationChow3_exists_dense_affine_cover X
  have hφ : ∀ i, ∃ (n : ℕ) (φ : (Ui i).toScheme ⟶ ℙ(Fin (n + 1); Y)),
      IsImmersion φ ∧ φ ≫ toBase (Fin (n + 1)) Y = (Ui i).ι ≫ f := fun i ↦
    AnalytificationChow3_exists_immersion σX σY f hf (Ui i) (haff i)
  choose n φ hφimm hφt using hφ
  obtain ⟨P, s, p, hs, hp, hP⟩ := AnalytificationChow3_exists_product Y k n
  let U : X.Opens := Finset.univ.inf Ui
  have hUi : ∀ i, U ≤ Ui i := fun i ↦ Finset.inf_le (Finset.mem_univ i)
  have hUd : Dense (U : Set X) := AnalytificationChow3_dense_finset_inf Ui hdense _
  obtain ⟨ψ, hψs, hψp⟩ := hP U.toScheme (U.ι ≫ f) (fun i ↦ X.homOfLE (hUi i) ≫ φ i)
    (fun i ↦ by rw [Category.assoc, hφt i, Scheme.homOfLE_ι_assoc])
  have : TopologicalSpace.NoetherianSpace U.toScheme := inferInstanceAs (TopologicalSpace.NoetherianSpace (U : Set X))
  let D : AnalytificationChow3_GraphData f :=
    { P := P, s := s, ι := Fin k, Ui := Ui, Pi := fun i ↦ ℙ(Fin (n i + 1); Y)
      t := fun i ↦ toBase (Fin (n i + 1)) Y, p := p, φ := φ, U := U, le_Ui := hUi, φU := ψ
      isSeparated_t := fun i ↦ inferInstance
      isImmersion_φ := hφimm
      p_t := hp
      φ_t := hφt
      φU_p := hψp
      φU_s := hψs.symm
      mem_Ui := hcov
      quasiCompact_graph := inferInstance }
  have := D.AnalytificationChow3_isClosedImmersion_h
  have hsP : IsProjective D.s := hs
  refine ⟨D.X', D.π, ?_, ?_, ?_⟩
  · dsimp only [AnalytificationChow3_GraphData.π]
    infer_instance
  · rw [D.π_f]
    exact AnalytificationChow_isProjective_comp_of_isClosedImmersion D.h D.s
  · have : UniversallyClosed D.π := by
      dsimp only [AnalytificationChow3_GraphData.π]
      infer_instance
    refine ⟨fun x ↦ ?_⟩
    have hcl : IsClosed (Set.range D.π) := D.π.isClosedMap.isClosed_range
    have : (U : Set X) ⊆ Set.range D.π := fun y hy ↦ D.le_range_π y hy
    have := hcl.closure_subset_iff.mpr this
    rw [hUd.closure_eq] at this
    exact this (Set.mem_univ x)

end HodgeLean.Foundations.Analytic
