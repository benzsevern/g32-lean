import HodgeLean.Foundations.Program.SchoenTowerFibreDefs
import HodgeLean.Foundations.Program.SchoenExceptional

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

theorem s2v_cohomology_homeomorph_injective {X Y : TopCat} (u : X ≃ₜ Y) (n : ℕ) :
    Function.Injective (cohomologyMap ℂ n (TopCat.ofHom ⟨u, u.continuous⟩)) := by
  intro v w hvw
  have hcomp : TopCat.ofHom ⟨u.symm, u.symm.continuous⟩ ≫
      TopCat.ofHom ⟨u, u.continuous⟩ = 𝟙 Y := by
    ext y
    exact u.apply_symm_apply y
  have hleft (v : Cohomology ℂ Y n) :
      cohomologyMap ℂ n (TopCat.ofHom ⟨u.symm, u.symm.continuous⟩)
        (cohomologyMap ℂ n (TopCat.ofHom ⟨u, u.continuous⟩) v) = v := by
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp, hcomp,
      cohomologyMap_id, LinearMap.id_apply]
  rw [← hleft v, ← hleft w, hvw]

theorem s2v_equivariant_homeomorph_eigenvector {X Y : TopCat}
    (u : X ≃ₜ Y) (f : X ⟶ X) (g : Y ⟶ Y)
    (hu : ∀ x, u (f x) = g (u x)) (n : ℕ) (μ : ℂ)
    (v : Cohomology ℂ X n) (hv : cohomologyMap ℂ n f v = μ • v) :
    cohomologyMap ℂ n g
      (cohomologyMap ℂ n (TopCat.ofHom ⟨u.symm, u.symm.continuous⟩) v) =
      μ • cohomologyMap ℂ n (TopCat.ofHom ⟨u.symm, u.symm.continuous⟩) v := by
  have he : g ≫ TopCat.ofHom ⟨u.symm, u.symm.continuous⟩ =
      TopCat.ofHom ⟨u.symm, u.symm.continuous⟩ ≫ f := by
    ext y
    apply u.injective
    change u (u.symm (g y)) = u (f (u.symm y))
    rw [u.apply_symm_apply]
    simpa only [u.apply_symm_apply] using (hu (u.symm y)).symm
  rw [← LinearMap.comp_apply, ← cohomologyMap_comp, he, cohomologyMap_comp,
    LinearMap.comp_apply, hv, map_smul]

theorem s2v_two_point_eigen_vanishing {X : TopCat}
    (m a : ℕ) (hm : 0 < m) (ha : ¬ m ∣ a)
    (c : ℂ) (hc : c ≠ 0) (u : X ≃ₜ s2c_twoPointFibre m a)
    (f : X ⟶ X) (hu : ∀ x, u (f x) = s2c_twoPointDeck m a c hc (u x))
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (n : ℕ)
    (v : Cohomology ℂ X n) (hv : cohomologyMap ℂ n f v = ζ • v) : v = 0 := by
  have hw := s2v_equivariant_homeomorph_eigenvector u f
    (TopCat.ofHom ⟨s2c_twoPointDeck m a c hc, (s2c_twoPointDeck m a c hc).continuous⟩) hu n ζ v hv
  have hz := s3_primitive_fibre_vanishing m a hm ha ζ hζ c hc n
    (cohomologyMap ℂ n (TopCat.ofHom ⟨u.symm, u.symm.continuous⟩) v) hw
  exact s2v_cohomology_homeomorph_injective
    (X := TopCat.of (s2c_twoPointFibre m a)) (Y := X) u.symm n (by rw [hz, map_zero])

theorem s2v_twoPointDeck_iterate_coe (m a : ℕ) (c : ℂ) (hc : c ≠ 0)
    (n : ℕ) (i : ZMod (Nat.gcd m a)) (z : ℂ) :
    (s2c_twoPointDeck m a c hc)^[n] (i, (z : OnePoint ℂ)) =
      (i + (n : ZMod (Nat.gcd m a)), ((c ^ n * z : ℂ) : OnePoint ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    change (i + (n : ZMod (Nat.gcd m a)) + 1,
      ((c * (c ^ n * z) : ℂ) : OnePoint ℂ)) = _
    congr 1
    · simp [Nat.cast_add, add_assoc]
    · congr 1
      rw [pow_succ]
      ring

end HodgeLean.Foundations.Program
