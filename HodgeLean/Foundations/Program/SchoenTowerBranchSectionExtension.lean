import HodgeLean.Foundations.Program.SchoenTowerPointRetractions
import HodgeLean.Foundations.Program.SchoenTowerRetractionExtension
import HodgeLean.Foundations.Program.SchoenTowerOverSections

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- Section pullbacks compose in the contravariant order. -/
theorem s2t_overSectionsAlgHom_comp_apply {X Y Z : Over (Spec ↧ℂ)}
    (f : X ⟶ Y) (g : Y ⟶ Z) (p : Γ(Z.left, ⊤)) :
    s2t_overSectionsAlgHom f (s2t_overSectionsAlgHom g p) =
      s2t_overSectionsAlgHom (f ≫ g) p := by
  change f.left.appTop (g.left.appTop p) = (f ≫ g).left.appTop p
  rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- Every invariant section on a retained power extends invariantly through point insertion.
Source: SGA 1, Exposé V, §1, affine invariant quotients; commuting coordinate retractions and averaging. -/
theorem s2t_branch_invariant_section_extension (C : Over (Spec ↧ℂ)) (n : ℕ)
    (b : ComplexPoint C) (p : Γ((g3_power C n).left, ⊤))
    (hp : ∀ σ, (s2_permute C n σ).left.appTop p = p) :
    ∃ q : Γ((g3_power C (n + 1)).left, ⊤),
      (∀ σ, (s2_permute C (n + 1) σ).left.appTop q = q) ∧
      (s2c_branchInsertion C n b).left.appTop q = p := by
  let X := g3_power C (n + 1)
  let G := Equiv.Perm (Fin (n + 1))
  let ρ := ((Over.forget (Spec ↧ℂ)).mapAut X).comp (s2_symmetricPowerAction C (n + 1))
  letI := s2_schemeSectionAction X.left G ρ
  letI := s2t_overSectionAction_smulCommClass X G (s2_symmetricPowerAction C (n + 1))
  let r := fun i : Fin (n + 1) => s2t_overSectionsAlgHom (s2t_pointReset C (n + 1) b i)
  let h := fun i : Fin (n + 1) => s2t_overSectionsAlgHom (s2t_dropCoordinate C n i) p
  have hid (i) (a : Γ(X.left, ⊤)) : r i (r i a) = r i a := by
    dsimp only [r]
    rw [s2t_overSectionsAlgHom_comp_apply, s2t_pointReset_idem]
  have hcomm (i j) (a : Γ(X.left, ⊤)) : r i (r j a) = r j (r i a) := by
    dsimp only [r]
    rw [s2t_overSectionsAlgHom_comp_apply, s2t_overSectionsAlgHom_comp_apply,
      s2t_pointReset_comm]
  have hfix (i) : r i (h i) = h i := by
    dsimp only [r, h]
    rw [s2t_overSectionsAlgHom_comp_apply, s2t_pointReset_drop]
  have hcompat (i j) : r i (h j) = r j (h i) := by
    obtain ⟨σ, hσ⟩ := s2t_pointReset_drop_permute C n b i j
    dsimp only [r, h]
    rw [s2t_overSectionsAlgHom_comp_apply, s2t_overSectionsAlgHom_comp_apply, hσ,
      ← Category.assoc, ← s2t_overSectionsAlgHom_comp_apply]
    change s2t_overSectionsAlgHom
      (s2t_pointReset C (n + 1) b j ≫ s2t_dropCoordinate C n i)
      ((s2_permute C n σ).left.appTop p) = _
    rw [hp]
  have hr (g : G) (i : Fin (n + 1)) (a : Γ(X.left, ⊤)) :
      r (g • i) (g • a) = g • r i a := by
    change s2t_overSectionsAlgHom (s2t_pointReset C (n + 1) b (g i))
      (s2t_overSectionsAlgHom (s2_permute C (n + 1) g⁻¹) a) =
      s2t_overSectionsAlgHom (s2_permute C (n + 1) g⁻¹)
        (s2t_overSectionsAlgHom (s2t_pointReset C (n + 1) b i) a)
    rw [s2t_overSectionsAlgHom_comp_apply, s2t_overSectionsAlgHom_comp_apply]
    have he := s2t_permute_pointReset C (n + 1) b i g⁻¹
    simpa only [Equiv.Perm.inv_def, Equiv.symm_symm] using
      congrArg (fun f => s2t_overSectionsAlgHom f a) he.symm
  have hh (g : G) (i : Fin (n + 1)) : g • h i = h (g • i) := by
    obtain ⟨τ, hτ⟩ := s2t_permute_dropCoordinate C n i g⁻¹
    have he : s2_permute C (n + 1) g⁻¹ ≫ s2t_dropCoordinate C n i =
        s2t_dropCoordinate C n (g i) ≫ s2_permute C n τ := by
      simpa only [Equiv.Perm.inv_def, Equiv.symm_symm] using hτ
    change s2t_overSectionsAlgHom (s2_permute C (n + 1) g⁻¹)
      (s2t_overSectionsAlgHom (s2t_dropCoordinate C n i) p) = _
    rw [s2t_overSectionsAlgHom_comp_apply, he, ← s2t_overSectionsAlgHom_comp_apply]
    change s2t_overSectionsAlgHom (s2t_dropCoordinate C n (g i))
      ((s2_permute C n τ).left.appTop p) = _
    rw [hp]
    rfl
  obtain ⟨q, hq⟩ := s2t_extend_invariant_retractions r h hid hcomm hfix hcompat hr hh
  refine ⟨q, ?_, ?_⟩
  · intro σ
    have he := q.property σ⁻¹
    change (s2_permute C (n + 1) (σ⁻¹)⁻¹).left.appTop (q : Γ(X.left, ⊤)) = _ at he
    simpa only [inv_inv] using he
  · have he := congrArg (s2t_overSectionsAlgHom (s2c_branchInsertion C n b)) (hq 0)
    change s2t_overSectionsAlgHom (s2c_branchInsertion C n b)
      (s2t_overSectionsAlgHom (s2t_pointReset C (n + 1) b 0) (q : Γ(X.left, ⊤))) =
        s2t_overSectionsAlgHom (s2c_branchInsertion C n b)
          (s2t_overSectionsAlgHom (s2t_dropCoordinate C n 0) p) at he
    rw [s2t_overSectionsAlgHom_comp_apply, s2t_overSectionsAlgHom_comp_apply,
      ← s2t_drop_branchInsertion, ← Category.assoc, s2t_branchInsertion_drop,
      Category.id_comp] at he
    change (s2c_branchInsertion C n b).left.appTop (q : Γ(X.left, ⊤)) = p at he
    exact he

end HodgeLean.Foundations.Program
