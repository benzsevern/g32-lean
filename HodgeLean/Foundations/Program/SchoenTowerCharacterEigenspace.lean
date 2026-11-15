import HodgeLean.Foundations.Program.SchoenTowerCharacterCohomology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program

theorem s2v_character_H_eigenspace_of_comparison {X E : TopCat}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (m : ℕ) (hm : 0 < m)
    (horder : ∀ x : X, d^[m] x = x) (ζ : ℂ) (hζ : ζ ^ m = 1) (hζ0 : ζ ≠ 0)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (n : ℕ)
    (c : V ≃+ Sheaf.H (s2c_coverSheaf f) n)
    (hcD : ∀ v, c (T v) = Sheaf.H.map (s2c_coverSheafDeck f d hd) n (c v))
    (hcS : ∀ (z : ℂ) v, c (z • v) = Sheaf.H.map (s2c_coverSheafScalar f z) n (c v)) :
    ∃ e : Sheaf.H (s2c_characterSheaf f d hd m ζ) n ≃+
        ↥(Module.End.eigenspace T ζ),
      ∀ v, c (e v).val = Sheaf.H.map (image.ι (s2c_characterProjector f d hd m ζ)) n v := by
  let P := s2c_characterProjector f d hd m ζ
  let i := image.ι P
  let r := factorThruImage P
  let g : Sheaf.H (s2c_characterSheaf f d hd m ζ) n →+ ↥(Module.End.eigenspace T ζ) := {
    toFun := fun v => ⟨c.symm (Sheaf.H.map i n v),
      Module.End.mem_eigenspace_iff.mpr
        (s2v_character_H_image_eigen f d hd m horder ζ hζ hζ0 T n c hcD (hcS ζ) v)⟩
    map_zero' := by
      apply Subtype.ext
      change c.symm (Sheaf.H.map i n 0) = 0
      rw [map_zero, map_zero]
    map_add' := by
      intro v w
      apply Subtype.ext
      change c.symm (Sheaf.H.map i n (v + w)) =
        c.symm (Sheaf.H.map i n v) + c.symm (Sheaf.H.map i n w)
      rw [map_add, map_add] }
  have hgI : Function.Injective g := by
    intro v w hvw
    apply s2v_character_H_inclusion_injective f d hd m hm horder ζ hζ hζ0 n
    have h := congrArg (fun z : ↥(Module.End.eigenspace T ζ) => c z.val) hvw
    change c (c.symm (Sheaf.H.map i n v)) = c (c.symm (Sheaf.H.map i n w)) at h
    simpa only [c.apply_symm_apply] using h
  have hgS : Function.Surjective g := by
    intro w
    refine ⟨Sheaf.H.map r n (c w.val), ?_⟩
    apply Subtype.ext
    apply c.injective
    change c (c.symm (Sheaf.H.map i n (Sheaf.H.map r n (c w.val)))) = c w.val
    rw [c.apply_symm_apply, ← Sheaf.H.map_comp_apply]
    change Sheaf.H.map (factorThruImage P ≫ image.ι P) n (c w.val) = c w.val
    rw [image.fac]
    rw [s2v_character_H_projector_formula f d hd T n c hcD hcS m ζ w.val]
    rw [s2v_character_average_fixes_eigenvector T m hm ζ hζ0 w.val
      (Module.End.mem_eigenspace_iff.mp w.property)]
  refine ⟨AddEquiv.ofBijective g ⟨hgI, hgS⟩, ?_⟩
  intro v
  change c (c.symm (Sheaf.H.map i n v)) = Sheaf.H.map i n v
  exact c.apply_symm_apply _

end HodgeLean.Foundations.Program
