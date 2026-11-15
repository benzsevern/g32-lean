import HodgeLean.Foundations.Program.CompensationAssemblyRelativeSurface

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

theorem cq_pairCircleTowerMap_fst {P Q : TopPair.{0}} (a : P ⟶ Q) (k : ℕ) :
    TopPair.Hom.fst (cq_pairCircleTowerMap a k) =
      cq_circleTowerMap (TopPair.Hom.fst a) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change cq_circleProductMap (TopPair.Hom.fst (cq_pairCircleTowerMap a k)) =
        cq_circleProductMap (cq_circleTowerMap (TopPair.Hom.fst a) k)
      rw [ih]
      rfl

theorem cq_pairCircleTowerMap_snd {P Q : TopPair.{0}} (a : P ⟶ Q) (k : ℕ) :
    TopPair.Hom.snd (cq_pairCircleTowerMap a k) =
      cq_circleTowerMap (TopPair.Hom.snd a) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change cq_circleProductMap (TopPair.Hom.snd (cq_pairCircleTowerMap a k)) =
        cq_circleProductMap (cq_circleTowerMap (TopPair.Hom.snd a) k)
      rw [ih]
      rfl

def cq_pairProductMap {P Q : TopPair.{0}} (a : P ⟶ Q) (Y : TopCat.{0}) :
    cq_pairProduct P Y ⟶ cq_pairProduct Q Y :=
  TopPair.ofHom (cq_fibreProductMap (TopPair.Hom.fst a) Y)
    (cq_fibreProductMap (TopPair.Hom.snd a) Y) (by
      apply ConcreteCategory.hom_ext
      intro p
      change ((TopPair.Hom.snd a ≫ Q.map) p.1, p.2) =
        ((P.map ≫ TopPair.Hom.fst a) p.1, p.2)
      rw [TopPair.Hom.w])

set_option backward.isDefEq.respectTransparency false in
theorem cq_pairTorusTowerHomeomorph_naturality {P Q : TopPair.{0}} (a : P ⟶ Q) (k : ℕ) :
    cq_pairCircleTowerMap a k ≫ cq_pairTorusTowerHomeomorph Q k =
      cq_pairTorusTowerHomeomorph P k ≫ cq_pairProductMap a (TopCat.of (UnitAddTorus (Fin k))) := by
  apply MorphismProperty.Arrow.Hom.ext
  · change TopPair.Hom.snd (cq_pairCircleTowerMap a k) ≫ _ = _
    rw [cq_pairCircleTowerMap_snd]
    apply ConcreteCategory.hom_ext
    intro p
    exact cq_circleTowerHomeomorph_naturality (TopPair.Hom.snd a) k p
  · change TopPair.Hom.fst (cq_pairCircleTowerMap a k) ≫ _ = _
    rw [cq_pairCircleTowerMap_fst]
    apply ConcreteCategory.hom_ext
    intro p
    exact cq_circleTowerHomeomorph_naturality (TopPair.Hom.fst a) k p

set_option backward.isDefEq.respectTransparency false in
theorem cq_relativeProductTorusTrace_naturality {P Q : TopPair.{0}} (a : P ⟶ Q) (k n : ℕ)
    (c : RelativeCohomology ℚ (cq_pairProduct Q (TopCat.of (UnitAddTorus (Fin k)))) (n + k)) :
    cq_relativeProductTorusTrace P k n
        (relativeCohomologyMap ℚ (n + k) (cq_pairProductMap a (TopCat.of (UnitAddTorus (Fin k)))) c) =
      relativeCohomologyMap ℚ n a (cq_relativeProductTorusTrace Q k n c) := by
  change cq_relativeTorusTrace P k n
    (relativeCohomologyMap ℚ (n + k) (cq_pairTorusTowerHomeomorph P k)
      (relativeCohomologyMap ℚ (n + k)
        (cq_pairProductMap a (TopCat.of (UnitAddTorus (Fin k)))) c)) = _
  have h : relativeCohomologyMap ℚ (n + k) (cq_pairTorusTowerHomeomorph P k)
      (relativeCohomologyMap ℚ (n + k)
        (cq_pairProductMap a (TopCat.of (UnitAddTorus (Fin k)))) c) =
      relativeCohomologyMap ℚ (n + k) (cq_pairCircleTowerMap a k)
        (relativeCohomologyMap ℚ (n + k) (cq_pairTorusTowerHomeomorph Q k) c) := by
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
      ← cq_pairTorusTowerHomeomorph_naturality,
      relativeCohomologyMap_comp, LinearMap.comp_apply]
  exact (congrArg (cq_relativeTorusTrace P k n) h).trans
    (cq_relativeTorusTrace_naturality a k n _)

theorem cq_pairFibreTorusMap_naturality {P Q : TopPair.{0}} (a : P ⟶ Q)
    (Y : TopCat.{0}) (k : ℕ) (e : Y ≃ₜ UnitAddTorus (Fin k)) :
    cq_pairProductMap a (TopCat.of (UnitAddTorus (Fin k))) ≫ cq_pairFibreTorusMap Q Y k e =
      cq_pairFibreTorusMap P Y k e ≫ cq_pairProductMap a Y := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem cq_relativeFibreTrace_naturality {P Q : TopPair.{0}} (a : P ⟶ Q)
    (Y : TopCat.{0}) (k n : ℕ) (e : Y ≃ₜ UnitAddTorus (Fin k))
    (c : RelativeCohomology ℚ (cq_pairProduct Q Y) (n + k)) :
    cq_relativeFibreTrace P Y k n e
        (relativeCohomologyMap ℚ (n + k) (cq_pairProductMap a Y) c) =
      relativeCohomologyMap ℚ n a (cq_relativeFibreTrace Q Y k n e c) := by
  change cq_relativeProductTorusTrace P k n
    (relativeCohomologyMap ℚ (n + k) (cq_pairFibreTorusMap P Y k e)
      (relativeCohomologyMap ℚ (n + k) (cq_pairProductMap a Y) c)) = _
  have h : relativeCohomologyMap ℚ (n + k) (cq_pairFibreTorusMap P Y k e)
      (relativeCohomologyMap ℚ (n + k) (cq_pairProductMap a Y) c) =
      relativeCohomologyMap ℚ (n + k) (cq_pairProductMap a (TopCat.of (UnitAddTorus (Fin k))))
        (relativeCohomologyMap ℚ (n + k) (cq_pairFibreTorusMap Q Y k e) c) := by
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
      ← cq_pairFibreTorusMap_naturality,
      relativeCohomologyMap_comp, LinearMap.comp_apply]
  exact (congrArg (cq_relativeProductTorusTrace P k n) h).trans
    (cq_relativeProductTorusTrace_naturality a k n _)

theorem cq_relativeNormalizedFibreTrace_naturality {P Q : TopPair.{0}} (a : P ⟶ Q)
    (Y : TopCat.{0}) (k n : ℕ) (e : Y ≃ₜ UnitAddTorus (Fin k))
    (I : Cohomology ℚ Y (0 + k) ≃ₗ[ℚ] ℚ)
    (c : RelativeCohomology ℚ (cq_pairProduct Q Y) (n + k)) :
    cq_relativeNormalizedFibreTrace P Y k n e I
        (relativeCohomologyMap ℚ (n + k) (cq_pairProductMap a Y) c) =
      relativeCohomologyMap ℚ n a (cq_relativeNormalizedFibreTrace Q Y k n e I c) := by
  change (cq_fibreIntegral Y k e (I.symm 1))⁻¹ • cq_relativeFibreTrace P Y k n e
    (relativeCohomologyMap ℚ (n + k) (cq_pairProductMap a Y) c) =
      relativeCohomologyMap ℚ n a
        ((cq_fibreIntegral Y k e (I.symm 1))⁻¹ • cq_relativeFibreTrace Q Y k n e c)
  rw [cq_relativeFibreTrace_naturality, map_smul]

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters

theorem cq_relativeSurfaceTrace_naturality {P Q : TopPair.{0}} (a : P ⟶ Q)
    (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ) (n : ℕ)
    (c : RelativeCohomology ℚ (cq_pairProduct Q (TopCat.of (ComplexPoint Y))) (n + 4)) :
    cq_relativeSurfaceTrace P Y hY I n
        (relativeCohomologyMap ℚ (n + 4) (cq_pairProductMap a (TopCat.of (ComplexPoint Y))) c) =
      relativeCohomologyMap ℚ n a (cq_relativeSurfaceTrace Q Y hY I n c) := by
  letI : SmoothOfRelativeDimension 2 Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  exact cq_relativeNormalizedFibreTrace_naturality a (TopCat.of (ComplexPoint Y)) 4 n
    (HodgeLean.Foundations.complexPointTorusHomeomorph Y 2)
    ((cupComparison Y 4).symm.trans I) c

end HodgeLean.Foundations.Program
