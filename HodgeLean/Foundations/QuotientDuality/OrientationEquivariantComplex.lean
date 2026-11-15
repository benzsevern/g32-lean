import HodgeLean.Foundations.QuotientDuality.OrientationInvariantExactness
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Endomorphism

/-! Chain complexes with a group action, regarded as complexes of representations. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

variable (G : Type) [Group G]

def complexDegreeRepresentation (K : ChainComplex (ModuleCat ℚ) ℕ)
    (ρ : G →* End K) (i : ℕ) : Representation ℚ G (K.X i) :=
  (ModuleCat.endRingEquiv (K.X i)).toMonoidHom.comp
    (((HomologicalComplex.eval (ModuleCat ℚ) (.down ℕ) i).mapEnd K).comp ρ)

def equivariantChainComplex (K : ChainComplex (ModuleCat ℚ) ℕ) (ρ : G →* End K) :
    ChainComplex (Rep ℚ G) ℕ where
  X i := Rep.of (complexDegreeRepresentation G K ρ i)
  d i j := Rep.ofHom
    { toLinearMap := (K.d i j).hom
      isIntertwining' g := by
        exact congrArg ModuleCat.Hom.hom ((ρ g).asHom.comm i j) }
  shape i j h := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact congrArg ModuleCat.Hom.hom (K.shape i j h)
  d_comp_d' i j k _ _ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact congrArg ModuleCat.Hom.hom (K.d_comp_d i j k)

def equivariantChainMap {K L : ChainComplex (ModuleCat ℚ) ℕ}
    (ρ : G →* End K) (σ : G →* End L) (f : K ⟶ L)
    (hf : ∀ g, (ρ g).asHom ≫ f = f ≫ (σ g).asHom) :
    equivariantChainComplex G K ρ ⟶ equivariantChainComplex G L σ where
  f i := Rep.ofHom
    { toLinearMap := (f.f i).hom
      isIntertwining' g := congrArg (fun t => (t.f i).hom) (hf g) }
  comm' i j _ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact congrArg ModuleCat.Hom.hom (f.comm i j)

lemma equivariantChainComplex_forget (K : ChainComplex (ModuleCat ℚ) ℕ)
    (ρ : G →* End K) :
    ((forget₂ (Rep ℚ G) (ModuleCat ℚ)).mapHomologicalComplex (.down ℕ)).obj
      (equivariantChainComplex G K ρ) = K := rfl

def equivariantShortComplex (S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ))
    (ρ₁ : G →* End S.X₁) (ρ₂ : G →* End S.X₂) (ρ₃ : G →* End S.X₃)
    (hf : ∀ g, (ρ₁ g).asHom ≫ S.f = S.f ≫ (ρ₂ g).asHom)
    (hg : ∀ g, (ρ₂ g).asHom ≫ S.g = S.g ≫ (ρ₃ g).asHom) :
    ShortComplex (ChainComplex (Rep ℚ G) ℕ) :=
  ShortComplex.mk (equivariantChainMap G ρ₁ ρ₂ S.f hf)
    (equivariantChainMap G ρ₂ ρ₃ S.g hg) (by
      apply HomologicalComplex.hom_ext
      intro i
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      exact congrArg (fun t => (t.f i).hom) S.zero)

lemma equivariantShortComplex_shortExact
    (S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ))
    (ρ₁ : G →* End S.X₁) (ρ₂ : G →* End S.X₂) (ρ₃ : G →* End S.X₃)
    (hf : ∀ g, (ρ₁ g).asHom ≫ S.f = S.f ≫ (ρ₂ g).asHom)
    (hg : ∀ g, (ρ₂ g).asHom ≫ S.g = S.g ≫ (ρ₃ g).asHom)
    (hS : S.ShortExact) : (equivariantShortComplex G S ρ₁ ρ₂ ρ₃ hf hg).ShortExact := by
  let F := (forget₂ (Rep ℚ G) (ModuleCat ℚ)).mapHomologicalComplex (.down ℕ)
  let T := equivariantShortComplex G S ρ₁ ρ₂ ρ₃ hf hg
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact (T.exact_map_iff_of_faithful F).mp hS.exact
  · haveI : Mono (F.map T.f) := hS.mono_f
    exact Functor.mono_of_mono_map F inferInstance
  · haveI : Epi (F.map T.g) := hS.epi_g
    exact Functor.epi_of_epi_map F inferInstance

def representationActionNat (g : G) :
    forget₂ (Rep ℚ G) (ModuleCat ℚ) ⟶ forget₂ (Rep ℚ G) (ModuleCat ℚ) where
  app A := ModuleCat.ofHom (A.ρ g)
  naturality X Y f := by
    ext x
    exact (Rep.hom_comm_apply f g x).symm

lemma invariantChainShortComplex_shortExact [Fintype G]
    (S : ShortComplex (ChainComplex (Rep ℚ G) ℕ)) (hS : S.ShortExact) :
    (S.map ((Rep.invariantsFunctor ℚ G).mapHomologicalComplex (.down ℕ))).ShortExact := by
  letI := rational_invariants_preserves_homology G
  letI := Functor.preservesFiniteColimits_of_preservesHomology (Rep.invariantsFunctor ℚ G)
  exact hS.map_of_exact _

lemma equivariant_homology_action (K : ChainComplex (ModuleCat ℚ) ℕ)
    (ρ : G →* End K) (i : ℕ) (g : G) :
    HomologicalComplex.homologyMap (ρ g).asHom i ≫
        (((equivariantChainComplex G K ρ).sc i).mapHomologyIso
          (forget₂ (Rep ℚ G) (ModuleCat ℚ))).hom =
      (((equivariantChainComplex G K ρ).sc i).mapHomologyIso
          (forget₂ (Rep ℚ G) (ModuleCat ℚ))).hom ≫
        ModuleCat.ofHom (((equivariantChainComplex G K ρ).homology i).ρ g) := by
  let E := equivariantChainComplex G K ρ
  let e := (E.sc i).mapHomologyIso (forget₂ (Rep ℚ G) (ModuleCat ℚ))
  have h := ShortComplex.homologyMap_mapNatTrans (S := E.sc i) (representationActionNat G g)
  change HomologicalComplex.homologyMap (ρ g).asHom i =
    e.hom ≫ ModuleCat.ofHom ((E.homology i).ρ g) ≫ e.inv at h
  change HomologicalComplex.homologyMap (ρ g).asHom i ≫ e.hom = _
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

def complexHomologyRepresentation (K : ChainComplex (ModuleCat ℚ) ℕ)
    (ρ : G →* End K) (i : ℕ) : Representation ℚ G (K.homology i) :=
  (ModuleCat.endRingEquiv (K.homology i)).toMonoidHom.comp
    (((HomologicalComplex.homologyFunctor (ModuleCat ℚ) (.down ℕ) i).mapEnd K).comp ρ)

def equivariantHomologyIso (K : ChainComplex (ModuleCat ℚ) ℕ)
    (ρ : G →* End K) (i : ℕ) :
    Rep.of (complexHomologyRepresentation G K ρ i) ≅
      (equivariantChainComplex G K ρ).homology i :=
  Rep.mkIso <| Representation.Equiv.mk
    (((equivariantChainComplex G K ρ).sc i).mapHomologyIso
      (forget₂ (Rep ℚ G) (ModuleCat ℚ))).toLinearEquiv
    (fun g => congrArg ModuleCat.Hom.hom (equivariant_homology_action G K ρ i g))

end HodgeLean.Foundations.QuotientDuality
