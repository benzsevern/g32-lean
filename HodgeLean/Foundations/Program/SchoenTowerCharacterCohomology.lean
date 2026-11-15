import HodgeLean.Foundations.Program.SchoenTowerProjectorIdempotent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s2v_character_H_inclusion_injective {X E : TopCat}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (m : ℕ) (hm : 0 < m)
    (horder : ∀ x : X, d^[m] x = x) (ζ : ℂ) (hζ : ζ ^ m = 1) (hζ0 : ζ ≠ 0) (n : ℕ) :
    Function.Injective (Sheaf.H.map (image.ι (s2c_characterProjector f d hd m ζ)) n) := by
  let P := s2c_characterProjector f d hd m ζ
  have hr := s2v_characterImage_retraction f d hd m hm horder ζ hζ hζ0
  have he (v : Sheaf.H (image P) n) :
      Sheaf.H.map (factorThruImage P) n (Sheaf.H.map (image.ι P) n v) = v := by
    rw [← Sheaf.H.map_comp_apply, hr, Sheaf.H.map_id_apply]
  intro v w hvw
  rw [← he v, ← he w, hvw]

theorem s2v_character_H_projector_formula {X E : TopCat}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (n : ℕ)
    (c : V ≃+ Sheaf.H (s2c_coverSheaf f) n)
    (hcD : ∀ v, c (T v) = Sheaf.H.map (s2c_coverSheafDeck f d hd) n (c v))
    (hcS : ∀ (z : ℂ) v, c (z • v) = Sheaf.H.map (s2c_coverSheafScalar f z) n (c v))
    (m : ℕ) (ζ : ℂ) (v : V) :
    Sheaf.H.map (s2c_characterProjector f d hd m ζ) n (c v) =
      c ((∑ t ∈ Finset.range m, ((m : ℂ)⁻¹ * ζ ^ (-(t : ℤ))) • T ^ t) v) := by
  classical
  have hp (t : ℕ) (v : V) :
      Sheaf.H.map ((End.of (s2c_coverSheafDeck f d hd)) ^ t).asHom n (c v) = c ((T ^ t) v) := by
    induction t generalizing v with
    | zero =>
      simp only [pow_zero, End.one_asHom, Module.End.one_apply]
      rw [Sheaf.H.map_id_apply]
    | succ t ih =>
      simp only [pow_succ, End.mul_asHom, Module.End.mul_apply]
      rw [Sheaf.H.map_comp_apply, ← hcD, ih]
  have hsum (r : Finset ℕ) (q : ℕ → (s2c_coverSheaf f ⟶ s2c_coverSheaf f))
      (x : Sheaf.H (s2c_coverSheaf f) n) :
      Sheaf.H.map (∑ t ∈ r, q t) n x = ∑ t ∈ r, Sheaf.H.map (q t) n x := by
    induction r using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      change ((Sheaf.functorH (Opens.grothendieckTopology E) n).map 0) x = 0
      rw [Functor.map_zero]
      rfl
    | @insert i r hi ih =>
      rw [Finset.sum_insert hi, Sheaf.H.map_add_apply, ih, Finset.sum_insert hi]
  unfold s2c_characterProjector
  rw [hsum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Sheaf.H.map_comp_apply, ← hcS, hp, map_smul]

theorem s2v_character_H_image_eigen {X E : TopCat}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (m : ℕ)
    (horder : ∀ x : X, d^[m] x = x) (ζ : ℂ) (hζ : ζ ^ m = 1) (hζ0 : ζ ≠ 0)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (n : ℕ)
    (c : V ≃+ Sheaf.H (s2c_coverSheaf f) n)
    (hcD : ∀ v, c (T v) = Sheaf.H.map (s2c_coverSheafDeck f d hd) n (c v))
    (hcS : ∀ v, c (ζ • v) = Sheaf.H.map (s2c_coverSheafScalar f ζ) n (c v))
    (v : Sheaf.H (s2c_characterSheaf f d hd m ζ) n) :
    T (c.symm (Sheaf.H.map (image.ι (s2c_characterProjector f d hd m ζ)) n v)) =
      ζ • c.symm (Sheaf.H.map (image.ι (s2c_characterProjector f d hd m ζ)) n v) := by
  apply c.injective
  rw [hcD, hcS]
  simp only [c.apply_symm_apply]
  let i := image.ι (s2c_characterProjector f d hd m ζ)
  have h := congrArg (fun q => Sheaf.H.map q n v)
    (s2v_characterImage_eigen f d hd m horder ζ hζ hζ0)
  exact (Sheaf.H.map_comp_apply i (s2c_coverSheafDeck f d hd) v).symm.trans
    (h.trans (Sheaf.H.map_comp_apply i (s2c_coverSheafScalar f ζ) v))

end HodgeLean.Foundations.Program
