module

public import HodgeLean.Foundations.Program.SchoenExceptionalDefs
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import HodgeLean.Foundations.Program.SchoenExceptionalHomotopy
public import HodgeLean.Foundations.Program.SchoenExceptionalProper
public import HodgeLean.Foundations.Program.SchoenExceptionalProperVanishing

/-! # S3 proof obligations -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

theorem s3_blowup_chart_aux (m a : ℕ) (ha : a ≤ m) (x t v : ℂ) :
    (x * v) ^ m - x ^ a * (x * t) ^ (m - a) =
      x ^ m * (v ^ m - t ^ (m - a)) := by
  rw [mul_pow, mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_of_le ha]
  ring

theorem s3_inertia_stalk_aux (G Ω : Type) [Group G] [MulAction G Ω]
    (χ : G →* ℂˣ) (hχ : Function.Injective χ) (f : Ω → ℂ)
    (hf : ∀ g x, f (g • x) = (χ g : ℂ) * f x)
    (x : Ω) (g : G) (hg : g ≠ 1) (hfix : g • x = x) : f x = 0 := by
  have he : (χ g : ℂ) * f x = 1 * f x := by rw [← hf, hfix, one_mul]
  rcases mul_eq_mul_right_iff.mp he with h | h
  · exact False.elim (hg (hχ (Units.ext (by simpa using h))))
  · exact h

theorem s3_monodromy_differential_aux (m a : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (ha : ¬ m ∣ a) : Function.Bijective (fun z : ℂ => (ζ ^ a - 1) * z) := by
  have hn : ζ ^ a - 1 ≠ 0 := sub_ne_zero.mpr (fun h => ha ((hζ.pow_eq_one_iff_dvd a).mp h))
  exact ⟨mul_right_injective₀ hn, fun z => ⟨(ζ ^ a - 1)⁻¹ * z, by simp [hn]⟩⟩

theorem s3_fibre_iterate_homotopic_aux (d : ℕ) (hd : 0 < d) (c : ℂ) (hc : c ≠ 0) :
    ContinuousMap.Homotopic
      ⟨(s3_deck d c hc)^[d], (s3_deck d c hc).continuous.iterate d⟩
      (ContinuousMap.id (s3_Fibre d)) := by
  let u : ℂˣ := Units.mk0 (c ^ d) (pow_ne_zero _ hc)
  have he : (⟨(s3_deck d c hc)^[d], (s3_deck d c hc).continuous.iterate d⟩ :
      C(s3_Fibre d, s3_Fibre d)) =
      ⟨fun p => (p.1, OnePoint.map (fun w : ℂ => (u : ℂ) * w) p.2),
        continuous_fst.prodMk ((Homeomorph.onePointCongr
          (Homeomorph.mulLeft₀ (u : ℂ) u.ne_zero)).continuous.comp continuous_snd)⟩ := by
    apply ContinuousMap.ext
    rintro ⟨i, z⟩
    change (s3_deck d c hc)^[d] (i, z) = _
    rw [s3_deck_iterate]
    simp only [ZMod.natCast_self, add_zero]
    rfl
  rw [he]
  exact ⟨s3_dilation_homotopy d u⟩

theorem s3_cohomology_homotopy {X Y : TopCat} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (n : ℕ) : cohomologyMap ℂ n f = cohomologyMap ℂ n g := by
  unfold cohomologyMap
  rw [(HomologicalComplex.linearDualHomotopy
    (H.singularChainComplexFunctorObjMap (ModuleCat.of ℂ ℂ))).homologyMap_eq n]

theorem s3_cohomology_iterate {X : TopCat} (f : X ⟶ X) (n k : ℕ)
    (v : Cohomology ℂ X n) (μ : ℂ) (hv : cohomologyMap ℂ n f v = μ • v) :
    cohomologyMap ℂ n (TopCat.ofHom ⟨f^[k], f.hom.continuous.iterate k⟩) v = μ ^ k • v := by
  induction k with
  | zero =>
    change cohomologyMap ℂ n (𝟙 X) v = _
    simp only [cohomologyMap_id, LinearMap.id_apply, pow_zero, one_smul]
  | succ k ih =>
    have he : TopCat.ofHom ⟨f^[k+1], f.hom.continuous.iterate (k+1)⟩ =
        TopCat.ofHom ⟨f^[k], f.hom.continuous.iterate k⟩ ≫ f := by
      ext x
      exact Function.iterate_succ_apply' _ _ _
    rw [he, cohomologyMap_comp, LinearMap.comp_apply, hv, map_smul, ih, smul_smul,
      pow_succ']

theorem s3_fibre_eigen_vanishing_aux (d : ℕ) (hd : 0 < d) (c : ℂ) (hc : c ≠ 0)
    (μ : ℂ) (hμ : μ ^ d ≠ 1) (n : ℕ)
    (v : Cohomology ℂ (TopCat.of (s3_Fibre d)) n)
    (hv : cohomologyMap ℂ n (TopCat.ofHom ⟨s3_deck d c hc, (s3_deck d c hc).continuous⟩) v = μ • v) :
    v = 0 := by
  obtain ⟨H⟩ := s3_fibre_iterate_homotopic_aux d hd c hc
  have hi := s3_cohomology_iterate
    (TopCat.ofHom ⟨s3_deck d c hc, (s3_deck d c hc).continuous⟩) n d v μ hv
  have he := s3_cohomology_homotopy (f := TopCat.ofHom _) (g := 𝟙 _) H n
  rw [he, cohomologyMap_id, LinearMap.id_apply] at hi
  have hz : (μ ^ d - 1) • v = 0 := by rw [sub_smul, one_smul, ← hi, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hμ)

theorem s3_primitive_fibre_vanishing_aux (m a : ℕ) (hm : 0 < m) (ha : ¬ m ∣ a)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (c : ℂ) (hc : c ≠ 0) (n : ℕ)
    (v : Cohomology ℂ (TopCat.of (s3_Fibre (Nat.gcd m a))) n)
    (hv : cohomologyMap ℂ n
      (TopCat.ofHom ⟨s3_deck (Nat.gcd m a) c hc, (s3_deck (Nat.gcd m a) c hc).continuous⟩) v = ζ • v) : v = 0 := by
  apply s3_fibre_eigen_vanishing_aux (Nat.gcd m a) (Nat.gcd_pos_of_pos_left a hm) c hc ζ
    (fun he => ha (dvd_trans ((hζ.pow_eq_one_iff_dvd _).mp he) (Nat.gcd_dvd_right m a))) n v hv

theorem s3_proper_fibre_vanishing_aux (X Y : TopCat) [T2Space X] [T2Space Y]
    [LocallyCompactSpace X] [LocallyCompactSpace Y]
    (p : X ⟶ Y) (hp : IsProperMap p) (F : TopCat.Sheaf AddCommGrpCat X)
    (hF : ∀ (y : Y) (q : ℕ), Subsingleton
      (CategoryTheory.Sheaf.H ((TopCat.Sheaf.pullback AddCommGrpCat
        (s3_fibreInclusion p y)).obj F) q)) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F n) := by
  have hP := s3_proper_pushforward_isZero p hp F (fun y => hF y 0)
  cases n with
  | zero => exact s3_H_zero_of_pushforward_isZero p F hP
  | succ n =>
      have hz := s3_proper_cohomology_succ_eq_zero p hp F
        (fun y q => hF y (q + 1)) hP.injective n
      exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end HodgeLean.Foundations.Program
