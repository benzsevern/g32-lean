import HodgeLean.Foundations.Program.SchoenCycleStep1Quotient

/-! # Fixed rational functions and field-valued generic maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

lemma s2e_step1_fieldPullback_base (X Y : Scheme) [IsIntegral X]
    (u : X ⟶ X) [IsIso u] (q : X ⟶ Y) (hu : u ≫ q = q)
    (U : Y.Opens) [Nonempty (q ⁻¹ᵁ U)] (r : Γ(Y, U)) :
    s2e_step1_fieldPullback X u
      (X.germToFunctionField (q ⁻¹ᵁ U) ((q.app U).hom r)) =
      X.germToFunctionField (q ⁻¹ᵁ U) ((q.app U).hom r) := by
  have hUV : q ⁻¹ᵁ U ≤ u ⁻¹ᵁ (q ⁻¹ᵁ U) := by
    change q ⁻¹ᵁ U ≤ (u ≫ q) ⁻¹ᵁ U
    rw [hu]
  have hl : q.app U ≫ u.appLE (q ⁻¹ᵁ U) (q ⁻¹ᵁ U) hUV = q.app U := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    have hc : (u ≫ q).appLE U (q ⁻¹ᵁ U) (by exact hUV) =
        q.appLE U (q ⁻¹ᵁ U) le_rfl := by congr 1
    rw [hc, ← Scheme.Hom.app_eq_appLE]
  have he : q.app U ≫ X.germToFunctionField (q ⁻¹ᵁ U) ≫
      CommRingCat.ofHom (s2e_step1_fieldPullback X u) =
      q.app U ≫ X.germToFunctionField (q ⁻¹ᵁ U) := by
    rw [s2e_step1_fieldPullback_germ X u _ _ hUV, ← Category.assoc, hl]
  exact congrArg (fun k : Γ(Y, U) ⟶ X.functionField => k.hom r) he

/-- The subfield fixed by the specified scheme isomorphisms.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, Chapter 1, section 1. -/
def s2e_step1_fixedField (X : Scheme) [IsIntegral X] (I : Type)
    (a : I → (X ⟶ X)) [∀ i, IsIso (a i)] : Subfield X.functionField :=
  ⨅ i, (s2e_step1_fieldPullback X (a i)).eqLocusField (RingHom.id X.functionField)

@[simp] lemma s2e_step1_mem_fixedField (X : Scheme) [IsIntegral X] (I : Type)
    (a : I → (X ⟶ X)) [∀ i, IsIso (a i)] (x : X.functionField) :
    x ∈ s2e_step1_fixedField X I a ↔ ∀ i, s2e_step1_fieldPullback X (a i) x = x := by
  simp [s2e_step1_fixedField]

/-- Any morphism whose source is the spectrum of a field is affine. -/
lemma s2e_step1_fieldSpec_affine (K : Type*) [Field K] (Y : Scheme)
    (η : Spec (CommRingCat.of K) ⟶ Y) : IsAffineHom η := by
  haveI : Subsingleton (Spec (CommRingCat.of K)) := by
    change Subsingleton (PrimeSpectrum K)
    infer_instance
  constructor
  intro U _
  cases isEmpty_or_nonempty (η ⁻¹ᵁ U) with
  | inl he =>
    have h : η ⁻¹ᵁ U = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      exact (he.false ⟨x, hx⟩).elim
    rw [h]
    exact isAffineOpen_bot _
  | inr hn =>
    have h : η ⁻¹ᵁ U = ⊤ := by
      apply top_unique
      intro x _
      have hx : x = hn.some.1 := Subsingleton.elim _ _
      exact hx ▸ hn.some.2
    rw [h]
    exact isAffineOpen_top _

/-- Base functions define a generic map from the fixed subfield. -/
theorem s2e_step1_fixedField_genericMap
    (X Y : Scheme) [IsIntegral X] (I : Type)
    (a : I → (X ⟶ X)) [∀ i, IsIso (a i)]
    (q : X ⟶ Y) [IsAffineHom q] (hinv : ∀ i, a i ≫ q = q)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty (q ⁻¹ᵁ U)] :
    let K := s2e_step1_fixedField X I a
    ∃ η : Spec (CommRingCat.of K) ⟶ Y,
      IsAffineHom η ∧
      Spec.map (CommRingCat.ofHom K.subtype) ≫ η =
        X.fromSpecStalk (genericPoint X) ≫ q := by
  let K := s2e_step1_fixedField X I a
  let φ : Γ(Y, U) →+* K :=
    ((X.germToFunctionField (q ⁻¹ᵁ U)).hom.comp (q.app U).hom).codRestrict K (by
      intro r
      rw [s2e_step1_mem_fixedField]
      intro i
      exact s2e_step1_fieldPullback_base X Y (a i) q (hinv i) U r)
  let η := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  refine ⟨η, s2e_step1_fieldSpec_affine K Y η, ?_⟩
  dsimp only [η]
  rw [← Spec.map_comp_assoc]
  change Spec.map (q.app U ≫ X.germToFunctionField (q ⁻¹ᵁ U)) ≫ hU.fromSpec = _
  rw [Spec.map_comp, Category.assoc, Scheme.Hom.app_eq_appLE,
    hU.SpecMap_appLE_fromSpec q (hU.preimage q) le_rfl, ← Category.assoc]
  have he : Spec.map (X.germToFunctionField (q ⁻¹ᵁ U)) ≫ (hU.preimage q).fromSpec =
      X.fromSpecStalk (genericPoint X) := by
    rw [← (hU.preimage q).isoSpec_inv_ι, ← Category.assoc]
    exact s2e_step1_generic_chart_comp X _ _
  rw [he]

end HodgeLean.Foundations.Program
