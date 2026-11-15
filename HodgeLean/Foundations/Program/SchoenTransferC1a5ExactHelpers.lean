import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! Exact sequence transport for integral relative chain comparison.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open ComposableArrows HomologicalComplex HomologicalComplex.HomologySequence
namespace HodgeLean.Foundations.Program

/-- In a map of short exact sequences of chain complexes, outer comparisons give the middle one.
Source: Hatcher, Algebraic Topology, §2.1, exact sequence of a pair and five lemma. -/
lemma c1a5_quasiIso_middle {C : Type*} [Category* C] [Abelian C]
    {S T : ShortComplex (ChainComplex C ℕ)} (φ : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact)
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  have := hS.epi_g
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hm : Mono (homologyMap φ.τ₂ i) := by
    have hrel : (ComplexShape.down ℕ).Rel (i + 1) i := by simp
    exact mono_of_epi_of_mono_of_mono'' (k := 2) (by omega)
      (composableArrows₅_exact hS (i + 1) i hrel)
      (composableArrows₅_exact hT (i + 1) i hrel)
      (mapComposableArrows₅ φ hS hT (i + 1) i hrel)
      2 3 4 5 rfl rfl rfl rfl
      (by change Epi (homologyMap φ.τ₃ (i + 1)); infer_instance)
      (by change Mono (homologyMap φ.τ₁ i); infer_instance)
      (by change Mono (homologyMap φ.τ₃ i); infer_instance)
  have he : Epi (homologyMap φ.τ₂ i) := by
    cases i with
    | zero =>
      have : Epi (homologyMap S.g 0) :=
        epi_homologyMap_of_epi_of_not_rel _ _ (by simp)
      exact epi_of_epi_of_epi_of_epi (mapComposableArrows₂ φ 0)
        (composableArrows₂_exact hT 0)
        (by change Epi (homologyMap S.g 0); infer_instance)
        (by change Epi (homologyMap φ.τ₁ 0); infer_instance)
        (by change Epi (homologyMap φ.τ₃ 0); infer_instance)
    | succ i =>
      have hrel : (ComplexShape.down ℕ).Rel (i + 1) i := by simp
      exact epi_of_epi_of_epi_of_mono'' (k := 0) (by omega)
        (composableArrows₅_exact hS (i + 1) i hrel)
        (composableArrows₅_exact hT (i + 1) i hrel)
        (mapComposableArrows₅ φ hS hT (i + 1) i hrel)
        0 1 2 3 rfl rfl rfl rfl
        (by change Epi (homologyMap φ.τ₁ (i + 1)); infer_instance)
        (by change Epi (homologyMap φ.τ₃ (i + 1)); infer_instance)
        (by change Mono (homologyMap φ.τ₁ i); infer_instance)
  exact isIso_of_mono_of_epi _

/-- The cokernel sequence of a monomorphic chain map is short exact.
Source: Hatcher, Algebraic Topology, §2.1, exact sequence of a pair. -/
lemma c1a5_cokernel_shortExact {C : Type*} [Category* C] [Abelian C]
    {A B : ChainComplex C ℕ} (f : A ⟶ B) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)

/-- A map of monomorphic inclusions with absolute comparisons gives a relative comparison.
Source: Hatcher, Algebraic Topology, §2.1, exact sequence of a pair and five lemma. -/
lemma c1a5_cokernel_comparison {C : Type*} [Category* C] [Abelian C]
    {A B D E : ChainComplex C ℕ} (f : A ⟶ B) (g : D ⟶ E) [Mono f] [Mono g]
    (a : A ⟶ D) (b : B ⟶ E) (w : f ≫ b = a ≫ g)
    (ha : QuasiIso a) (hb : QuasiIso b) : QuasiIso (cokernel.map f g a b w) := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let T := ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
  let φ : S ⟶ T := ShortComplex.homMk a b (cokernel.map f g a b w) w.symm
    (by simp only [S, T, cokernel.map, cokernel.π_desc])
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (c1a5_cokernel_shortExact f) (c1a5_cokernel_shortExact g) ha hb

/-- Subobject and relative comparisons give the ambient comparison for monomorphic chain maps.
Source: Hatcher, Algebraic Topology, §2.1, exact sequence of a pair and five lemma. -/
lemma c1a5_cokernel_middle_comparison {C : Type*} [Category* C] [Abelian C]
    {A B D E : ChainComplex C ℕ} (f : A ⟶ B) (g : D ⟶ E) [Mono f] [Mono g]
    (a : A ⟶ D) (b : B ⟶ E) (w : f ≫ b = a ≫ g)
    (ha : QuasiIso a) (hr : QuasiIso (cokernel.map f g a b w)) : QuasiIso b := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let T := ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
  let φ : S ⟶ T := ShortComplex.homMk a b (cokernel.map f g a b w) w.symm
    (by simp only [S, T, cokernel.map, cokernel.π_desc])
  exact c1a5_quasiIso_middle φ
    (c1a5_cokernel_shortExact f) (c1a5_cokernel_shortExact g) ha hr

end HodgeLean.Foundations.Program
