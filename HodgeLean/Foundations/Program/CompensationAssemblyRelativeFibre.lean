import HodgeLean.Foundations.Program.CompensationAssemblyRelativeProduct
import HodgeLean.Foundations.Program.CompensationAssemblyNormalizedTrace

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

def cq_pairFibreTorusMap (P : TopPair.{0}) (Y : TopCat.{0}) (k : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k)) :
    cq_pairProduct P (TopCat.of (UnitAddTorus (Fin k))) ⟶ cq_pairProduct P Y :=
  TopPair.ofHom
    (TopCat.ofHom ⟨((Homeomorph.refl P.fst).prodCongr e).symm,
      ((Homeomorph.refl P.fst).prodCongr e).symm.continuous⟩)
    (TopCat.ofHom ⟨((Homeomorph.refl P.snd).prodCongr e).symm,
      ((Homeomorph.refl P.snd).prodCongr e).symm.continuous⟩) (by
        apply ConcreteCategory.hom_ext
        intro p
        rfl)

def cq_relativeFibreTrace (P : TopPair.{0}) (Y : TopCat.{0}) (k n : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k)) :
    RelativeCohomology ℚ (cq_pairProduct P Y) (n + k) →ₗ[ℚ] RelativeCohomology ℚ P n :=
  cq_relativeProductTorusTrace P k n ∘ₗ
    relativeCohomologyMap ℚ (n + k) (cq_pairFibreTorusMap P Y k e)

set_option backward.isDefEq.respectTransparency false in
theorem cq_relativeFibreTrace_absolute (P : TopPair.{0}) (Y : TopCat.{0}) (k n : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k))
    (a : RelativeCohomology ℚ (cq_pairProduct P Y) (n + k)) :
    relativeCohomologyToAbsolute ℚ P n (cq_relativeFibreTrace P Y k n e a) =
      cq_fibreTrace P.fst Y k n e
        (relativeCohomologyToAbsolute ℚ (cq_pairProduct P Y) (n + k) a) := by
  change relativeCohomologyToAbsolute ℚ P n
    (cq_relativeProductTorusTrace P k n
      (relativeCohomologyMap ℚ (n + k) (cq_pairFibreTorusMap P Y k e) a)) = _
  rw [cq_relativeProductTorusTrace_absolute, cq_relativeToAbsolute_naturality]
  rfl

def cq_relativeNormalizedFibreTrace (P : TopPair.{0}) (Y : TopCat.{0}) (k n : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k)) (I : Cohomology ℚ Y (0 + k) ≃ₗ[ℚ] ℚ) :
    RelativeCohomology ℚ (cq_pairProduct P Y) (n + k) →ₗ[ℚ] RelativeCohomology ℚ P n :=
  (cq_fibreIntegral Y k e (I.symm 1))⁻¹ • cq_relativeFibreTrace P Y k n e

set_option backward.isDefEq.respectTransparency false in
theorem cq_relativeNormalizedFibreTrace_absolute (P : TopPair.{0}) (Y : TopCat.{0}) (k n : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k)) (I : Cohomology ℚ Y (0 + k) ≃ₗ[ℚ] ℚ)
    (a : RelativeCohomology ℚ (cq_pairProduct P Y) (n + k)) :
    relativeCohomologyToAbsolute ℚ P n (cq_relativeNormalizedFibreTrace P Y k n e I a) =
      cq_normalizedFibreTrace P.fst Y k n e I
        (relativeCohomologyToAbsolute ℚ (cq_pairProduct P Y) (n + k) a) := by
  change relativeCohomologyToAbsolute ℚ P n
    ((cq_fibreIntegral Y k e (I.symm 1))⁻¹ • cq_relativeFibreTrace P Y k n e a) = _
  rw [map_smul, cq_relativeFibreTrace_absolute]
  rfl

end HodgeLean.Foundations.Program
