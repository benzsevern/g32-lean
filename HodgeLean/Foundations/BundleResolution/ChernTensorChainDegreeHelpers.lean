import HodgeLean.Foundations.BundleResolution.ChernTensorDegreeFamilyHelpers

/-! # Components of actual tensor chain maps

The actual chain tensor map agrees with its underlying degreewise linear
family construction on each total group.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory MonoidalCategory
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_tensorRight_degree {K K' : ChainComplex (ModuleCat ℚ) ℕ}
    (f : K ⟶ K') (L : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (f ▷ L).f n = i1_tensorDegreeMapLeft K K' L (fun p => (f.f p).hom) n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [i1_tensorDegreeMapLeft_inclusion]
  change HomologicalComplex.ιTensorObj K L p q n hpq ≫
    (HomologicalComplex.tensorHom f (𝟙 L)).f n = _
  rw [tensorDegreeInclusion_naturality]
  simp only [HomologicalComplex.id_f, tensorHom_def, whiskerLeft_id, Category.comp_id]
  rfl

end HodgeLean.Foundations.BundleResolution
