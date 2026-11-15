import HodgeConjecture.Mathlib.Topology.Category.TopPair
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSupportChains
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cMayerVietoris
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false in
theorem b6m_cokernelMap_quasiIso
    (R : Type) [CommRing R] {A B C D : ChainCategory R}
    (f : A ⟶ B) (g : C ⟶ D) [Mono f] [Mono g]
    (u : A ⟶ C) (v : B ⟶ D) (w : f ≫ v = u ≫ g)
    [QuasiIso u] [QuasiIso v] : QuasiIso (cokernel.map f g u v w) := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let T := ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_cokernel f }
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_cokernel g }
  let φ : S ⟶ T :=
    { τ₁ := u
      τ₂ := v
      τ₃ := cokernel.map f g u v w
      comm₁₂ := w.symm
      comm₂₃ := by simp [S, T] }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hS hT inferInstance inferInstance

def b6m_subspacePairMap (X : TopCat) (U V : Set X) :
    TopPair.ofSubset (X := TopCat.of U) (Subtype.val ⁻¹' V) ⟶
      TopPair.ofSubset (X := X) V :=
  TopPair.ofSubsetHom (topologicalSubsetInclusion X U) (fun _ h => h)

def b6m_nestedIntersectionHomeomorph (X : TopCat) (U V : Set X) :
    ↥(Subtype.val ⁻¹' V : Set U) ≃ₜ ↥(U ∩ V) where
  toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
  invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

set_option backward.isDefEq.respectTransparency false in
theorem b6m_subspaceSmallChainSquare_isPushout
    (R : Type) [CommRing R] (X : TopCat) (U V : Set X) :
    IsPushout
      (((chainPairFunctor R).obj
        (TopPair.ofSubset (X := TopCat.of U) (Subtype.val ⁻¹' V))).hom)
      (((chainPairFunctor R).map (b6m_subspacePairMap X U V)).left)
      (SSet.chainComplexMap (subsetLeftToSmallSingularSet X U V) (ModuleCat.of R R))
      (SSet.chainComplexMap (subsetRightToSmallSingularSet X U V) (ModuleCat.of R R)) := by
  let G := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)
  let e := G.mapIso (TopCat.isoOfHomeo (X := TopCat.of ↥(Subtype.val ⁻¹' V : Set U))
    (Y := TopCat.of ↥(U ∩ V)) (b6m_nestedIntersectionHomeomorph X U V))
  refine (b6m_subsetSmallChainSquare_isPushout R X U V).of_iso' e
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · change G.map _ ≫ G.map _ = G.map _ ≫ 𝟙 _
    rw [Category.comp_id, ← G.map_comp]
    rfl
  · change G.map _ ≫ G.map _ = G.map _ ≫ 𝟙 _
    rw [Category.comp_id, ← G.map_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem b6m_openCover_relativeChainMap_quasiIso
    (R : Type) [CommRing R] (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    QuasiIso ((relativeChainFunctor R).map (b6m_subspacePairMap X U V)) := by
  let P := TopPair.ofSubset (X := TopCat.of U) (Subtype.val ⁻¹' V)
  let Q := TopPair.ofSubset (X := X) V
  let f := ((chainPairFunctor R).obj P).hom
  let g := ((chainPairFunctor R).obj Q).hom
  let u := ((chainPairFunctor R).map (b6m_subspacePairMap X U V)).left
  let v := ((chainPairFunctor R).map (b6m_subspacePairMap X U V)).right
  let r := SSet.chainComplexMap (subsetLeftToSmallSingularSet X U V) (ModuleCat.of R R)
  let b := SSet.chainComplexMap (subsetRightToSmallSingularSet X U V) (ModuleCat.of R R)
  let h := b6m_twoSubsetSmallChainInclusion R X U V
  have sq : IsPushout f u r b := b6m_subspaceSmallChainSquare_isPushout R X U V
  have wr : r ≫ h = v := by
    let F := (SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)
    change F.map _ ≫ F.map _ = F.map _
    rw [← F.map_comp]
    rfl
  have wb : b ≫ h = g := by
    let F := (SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)
    change F.map _ ≫ F.map _ = F.map _
    rw [← F.map_comp]
    rfl
  have : Mono (subsetRightToSmallSingularSet X U V) := by
    dsimp [subsetRightToSmallSingularSet]
    infer_instance
  have : Mono b := by
    dsimp [b, SSet.chainComplexMap, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  have : Mono g := (relativeChainShortComplex_shortExact R Q).mono_f
  have : QuasiIso h := b6m_twoSubsetSmallChainInclusion_quasiIso R X U V hU hV hUV
  let φ := cokernel.map f b u r sq.w
  let ψ := cokernel.map b g (𝟙 _) h (by simpa using wb)
  have : IsIso φ := isIso_cokernel_map_of_isPushout sq
  have : QuasiIso φ := quasiIso_of_isIso _
  have : QuasiIso ψ := b6m_cokernelMap_quasiIso R b g (𝟙 _) h _
  have hfac : φ ≫ ψ = (relativeChainFunctor R).map (b6m_subspacePairMap X U V) := by
    change φ ≫ ψ = cokernel.map f g u v
      (((chainPairFunctor R).map (b6m_subspacePairMap X U V)).w.symm)
    apply (cancel_epi (cokernel.π f)).1
    simp only [φ, ψ, cokernel.map, Category.assoc, cokernel.π_desc_assoc, cokernel.π_desc]
    rw [← Category.assoc, wr]
  rw [← hfac]
  infer_instance

theorem b6m_closed_support_excision
    (R : Type) [CommRing R] {M : Type} [TopologicalSpace M] {U A : Set M}
    (hU : IsOpen U) (hA : IsClosed A) (hAU : A ⊆ U) :
    QuasiIso ((relativeChainFunctor R).map (b6m_subspacePairMap (TopCat.of M) U Aᶜ)) := by
  apply b6m_openCover_relativeChainMap_quasiIso R _ _ _ hU hA.isOpen_compl
  exact Set.eq_univ_of_forall fun x => by
    by_cases hx : x ∈ A
    · exact Or.inl (hAU hx)
    · exact Or.inr hx

theorem b6m_closed_support_excision_bijective
    (R : Type) [CommRing R] {M : Type} [TopologicalSpace M] {U A : Set M}
    (hU : IsOpen U) (hA : IsClosed A) (hAU : A ⊆ U) (i : ℕ) :
    Function.Bijective (relativeHomologyMap R i (b6m_subspacePairMap (TopCat.of M) U Aᶜ)) := by
  have := b6m_closed_support_excision R hU hA hAU
  have hiso : IsIso (HomologicalComplex.homologyMap
      ((relativeChainFunctor R).map (b6m_subspacePairMap (TopCat.of M) U Aᶜ)) i) := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hiso

end HodgeLean.Foundations.Program
