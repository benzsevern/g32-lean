import HodgeLean.Foundations.Program.CompensationAssemblyRelativeTorus

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

def cq_pairProduct (P : TopPair.{0}) (Y : TopCat.{0}) : TopPair.{0} :=
  TopPair.of (TopCat.ofHom ⟨fun p : P.snd × Y => (P.map p.1, p.2),
    P.map.hom.continuous.prodMap continuous_id⟩ :
      TopCat.of (P.snd × Y) ⟶ TopCat.of (P.fst × Y))
    (P.isEmbedding_map.prodMap Topology.IsEmbedding.id)

def cq_pairTorusTowerHomeomorph (P : TopPair.{0}) (k : ℕ) :
    cq_pairCircleTower P k ⟶ cq_pairProduct P (TopCat.of (UnitAddTorus (Fin k))) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨cq_circleTowerHomeomorph P.fst k,
      (cq_circleTowerHomeomorph P.fst k).continuous⟩)
    (TopCat.ofHom ⟨cq_circleTowerHomeomorph P.snd k,
      (cq_circleTowerHomeomorph P.snd k).continuous⟩) (by
        apply ConcreteCategory.hom_ext
        intro p
        exact (cq_circleTowerHomeomorph_naturality P.map k p).symm)

theorem cq_relativeToAbsolute_naturality {P Q : TopPair.{0}} (a : P ⟶ Q) (n : ℕ)
    (c : RelativeCohomology ℚ Q n) :
    relativeCohomologyToAbsolute ℚ P n (relativeCohomologyMap ℚ n a c) =
      cohomologyMap ℚ n (TopPair.Hom.fst a) (relativeCohomologyToAbsolute ℚ Q n c) := by
  apply (cohomologyEquivDualHomology ℚ P.fst n).injective
  ext z
  rw [cohomologyEquivDualHomology_relativeCohomologyToAbsolute,
    relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    cohomologyEquivDualHomology_cohomologyMap,
    cohomologyEquivDualHomology_relativeCohomologyToAbsolute]
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) a)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  exact congrArg (relativeCohomologyEquivDualHomology ℚ Q n c)
    (ConcreteCategory.congr_hom h z)

def cq_relativeProductTorusTrace (P : TopPair.{0}) (k n : ℕ) :
    RelativeCohomology ℚ (cq_pairProduct P (TopCat.of (UnitAddTorus (Fin k)))) (n + k) →ₗ[ℚ]
      RelativeCohomology ℚ P n :=
  cq_relativeTorusTrace P k n ∘ₗ
    relativeCohomologyMap ℚ (n + k) (cq_pairTorusTowerHomeomorph P k)

set_option backward.isDefEq.respectTransparency false in
theorem cq_relativeProductTorusTrace_absolute (P : TopPair.{0}) (k n : ℕ)
    (a : RelativeCohomology ℚ (cq_pairProduct P (TopCat.of (UnitAddTorus (Fin k)))) (n + k)) :
    relativeCohomologyToAbsolute ℚ P n (cq_relativeProductTorusTrace P k n a) =
      cq_productTorusTrace P.fst k n
        (relativeCohomologyToAbsolute ℚ
          (cq_pairProduct P (TopCat.of (UnitAddTorus (Fin k)))) (n + k) a) := by
  change relativeCohomologyToAbsolute ℚ P n
    (cq_relativeTorusTrace P k n
      (relativeCohomologyMap ℚ (n + k) (cq_pairTorusTowerHomeomorph P k) a)) = _
  rw [cq_relativeTorusTrace_absolute, cq_relativeToAbsolute_naturality]
  rfl

end HodgeLean.Foundations.Program
