import HodgeLean.Foundations.Program.G32Native.UnionConormalNoetherianExact
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Right exactness in associated-module coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Associated-module coordinates and an epic last arrow determine exactness
when the algebraic quotient is noetherian. -/
lemma unionConormal_tilde_exact_of_noetherian
    (R : CommRingCat.{0}) (M N P : ModuleCat R) [IsNoetherian R P]
    (f : M ⟶ N) (g₀ : N ⟶ P)
    (he : Function.Exact f g₀) (hg₀ : Function.Surjective g₀)
    (S : ShortComplex (Spec R).Modules) [Epi S.g]
    (e₁ : S.X₁ ≅ (tilde.functor R).obj M)
    (e₂ : S.X₂ ≅ (tilde.functor R).obj N)
    (e₃ : S.X₃ ≅ (tilde.functor R).obj P)
    (hf : S.f ≫ e₂.hom = e₁.hom ≫ (tilde.functor R).map f) : S.Exact := by
  let F := tilde.functor R
  let g : N ⟶ P := F.preimage (e₂.inv ≫ S.g ≫ e₃.hom)
  have hg : F.map g = e₂.inv ≫ S.g ≫ e₃.hom := F.map_preimage _
  haveI : Epi (F.map g) := by rw [hg]; infer_instance
  haveI : Epi g := F.epi_of_epi_map inferInstance
  have hz : f ≫ g = 0 := by
    apply F.map_injective
    rw [Functor.map_comp, hg, Functor.map_zero]
    apply (cancel_epi e₁.hom).mp
    rw [← Category.assoc e₁.hom (F.map f), ← hf]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, S.zero, zero_comp, comp_zero]
  have hx : Function.Exact f g :=
    unionConormal_exact_of_noetherian_quotient f.hom g₀.hom g.hom he hg₀
      (by exact congrArg ModuleCat.Hom.hom hz)
      ((ModuleCat.epi_iff_surjective g).mp inferInstance)
  let T := ShortComplex.mk f g hz
  have ht : T.Exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mpr hx
  letI := (tilde.adjunction (R := R)).leftAdjoint_preservesColimits
  have hm := ht.map_of_epi_of_preservesCokernel F inferInstance inferInstance
  let e : S ≅ T.map F := ShortComplex.isoMk e₁ e₂ e₃ hf.symm (by
    change e₂.hom ≫ F.map g = S.g ≫ e₃.hom
    rw [hg, Iso.hom_inv_id_assoc])
  exact ShortComplex.exact_of_iso e.symm hm

end HodgeLean.Foundations.Program.G32Native
