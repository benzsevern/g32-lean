import HodgeLean.Foundations.Program.CompensationAssemblyPrismHomology

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology.Singular MonoidalCategory
namespace HodgeLean.Foundations.Program

def cq_pairCircleHomologyPrism (P : TopPair.{0}) (n : ℕ) :
    RelativeHomology ℚ P n ⟶ RelativeHomology ℚ (cq_pairCircle P) (n + 1) :=
  cq_selfHomotopy_homologyMap (cq_pairCircleChainHomotopy P) n

def cq_pairCircleCohomologyPrism (P : TopPair.{0}) (n : ℕ) :
    RelativeCohomology ℚ (cq_pairCircle P) (n + 1) →ₗ[ℚ] RelativeCohomology ℚ P n :=
  (relativeCohomologyEquivDualHomology ℚ P n).symm.toLinearMap ∘ₗ
    LinearMap.dualMap (cq_pairCircleHomologyPrism P n).hom ∘ₗ
      (relativeCohomologyEquivDualHomology ℚ (cq_pairCircle P) (n + 1)).toLinearMap

theorem cq_pairCircleCohomologyPrism_pairing (P : TopPair.{0}) (n : ℕ)
    (a : RelativeCohomology ℚ (cq_pairCircle P) (n + 1)) (z : RelativeHomology ℚ P n) :
    relativeCohomologyEquivDualHomology ℚ P n (cq_pairCircleCohomologyPrism P n a) z =
      relativeCohomologyEquivDualHomology ℚ (cq_pairCircle P) (n + 1) a
        (cq_pairCircleHomologyPrism P n z) := by
  simp only [cq_pairCircleCohomologyPrism, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.dualMap_apply]

def cq_pairCircleMap {P Q : TopPair.{0}} (a : P ⟶ Q) :
    cq_pairCircle P ⟶ cq_pairCircle Q :=
  TopPair.ofHom (cq_circleProductMap (TopPair.Hom.fst a))
    (cq_circleProductMap (TopPair.Hom.snd a)) (by
      apply ConcreteCategory.hom_ext
      intro p
      change ((TopPair.Hom.snd a ≫ Q.map) p.1, p.2) =
        ((P.map ≫ TopPair.Hom.fst a) p.1, p.2)
      rw [TopPair.Hom.w])

theorem cq_relativeChainHomotopy_naturality
    {P Q P' Q' : TopPair.{0}} {f g : P ⟶ Q} {f' g' : P' ⟶ Q'}
    (H : TopPair.Homotopy f g) (H' : TopPair.Homotopy f' g')
    (a : P' ⟶ P) (b : Q' ⟶ Q)
    (hw : TopPair.Hom.fst a ▷ TopCat.I ≫ H.fst.h = H'.fst.h ≫ TopPair.Hom.fst b)
    (i j : ℕ) :
    ((relativeChainFunctor ℚ).map a).f i ≫
        TopPair.Homotopy.relativeChainHomotopyComponent (R := ℚ) H i j =
      TopPair.Homotopy.relativeChainHomotopyComponent (R := ℚ) H' i j ≫
        ((relativeChainFunctor ℚ).map b).f j := by
  apply CategoryTheory.Limits.Cofork.IsColimit.hom_ext
    (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel (R := ℚ) P' i)
  have ha := congrArg (fun k => k.f i)
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) a)
  have hb := congrArg (fun k => k.f j)
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) b)
  dsimp only [HomologicalComplex.comp_f] at ha hb
  change (relativeChainProjection ℚ P').f i ≫ _ =
    (relativeChainProjection ℚ P').f i ≫ _
  rw [← Category.assoc, ha, Category.assoc,
    TopPair.Homotopy.relativeChainHomotopyComponent_fac,
    ← Category.assoc, TopCat.Homotopy.singularChainHomotopy_hom_naturality
      H.fst H'.fst (TopPair.Hom.fst a) (TopPair.Hom.fst b) hw (ModuleCat.of ℚ ℚ) i j,
    Category.assoc, ← hb]
  rw [TopPair.Homotopy.relativeChainHomotopyComponent_fac_assoc]

theorem cq_pairCircleChainHomotopy_naturality {P Q : TopPair.{0}} (a : P ⟶ Q)
    (i j : ℕ) :
    ((relativeChainFunctor ℚ).map a).f i ≫ (cq_pairCircleChainHomotopy Q).hom i j =
      (cq_pairCircleChainHomotopy P).hom i j ≫
        ((relativeChainFunctor ℚ).map (cq_pairCircleMap a)).f j := by
  apply cq_relativeChainHomotopy_naturality
  apply ConcreteCategory.hom_ext
  intro p
  rfl

theorem cq_pairCircleHomologyPrism_naturality {P Q : TopPair.{0}} (a : P ⟶ Q)
    (n : ℕ) :
    HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map a) n ≫
        cq_pairCircleHomologyPrism Q n =
      cq_pairCircleHomologyPrism P n ≫
        HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map (cq_pairCircleMap a)) (n + 1) := by
  exact cq_selfHomotopy_homologyMap_naturality _ _ _ _
    (fun k => cq_pairCircleChainHomotopy_naturality a k (k + 1)) n

theorem cq_pairCircleCohomologyPrism_naturality {P Q : TopPair.{0}} (a : P ⟶ Q)
    (n : ℕ) (c : RelativeCohomology ℚ (cq_pairCircle Q) (n + 1)) :
    cq_pairCircleCohomologyPrism P n
        (relativeCohomologyMap ℚ (n + 1) (cq_pairCircleMap a) c) =
      relativeCohomologyMap ℚ n a (cq_pairCircleCohomologyPrism Q n c) := by
  apply (relativeCohomologyEquivDualHomology ℚ P n).injective
  ext z
  rw [cq_pairCircleCohomologyPrism_pairing,
    relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    cq_pairCircleCohomologyPrism_pairing]
  have h := ConcreteCategory.congr_hom (cq_pairCircleHomologyPrism_naturality a n) z
  exact congrArg (relativeCohomologyEquivDualHomology ℚ (cq_pairCircle Q) (n + 1) c) h.symm

end HodgeLean.Foundations.Program
