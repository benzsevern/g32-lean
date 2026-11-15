import HodgeLean.Foundations.Program.G32PropFourSixPacked0201
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound016_points : Finset (Fin 240) :=
  {3, 6, 7, 15, 16, 28, 33, 36, 38, 50, 55, 58, 63, 66, 80, 91, 96, 99, 104, 107, 121, 127, 134, 144, 153, 156, 170, 182, 191, 225}

def g32p_centralizerBound016_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound016_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) := by
  decide +kernel

theorem g32p_centralizerBound016_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) := by
  decide +kernel

theorem g32p_centralizerBound016_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) := by
  decide +kernel

theorem g32p_centralizerBound016_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) := by
  decide +kernel

theorem g32p_centralizerBound016_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) := by
  decide +kernel

theorem g32p_centralizerBound016_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) := by
  decide +kernel

theorem g32p_centralizerBound016_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) := by
  decide +kernel

theorem g32p_centralizerBound016_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) := by
  decide +kernel

theorem g32p_centralizerBound016_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) := by
  decide +kernel

theorem g32p_centralizerBound016_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) := by
  decide +kernel

theorem g32p_centralizerBound016_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) := by
  decide +kernel

theorem g32p_centralizerBound016_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) := by
  decide +kernel

theorem g32p_centralizerBound016_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) := by
  decide +kernel

theorem g32p_centralizerBound016_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) := by
  decide +kernel

theorem g32p_centralizerBound016_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) := by
  decide +kernel

theorem g32p_centralizerBound016_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 16) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound016_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound016_point_block00 t
  · exact g32p_centralizerBound016_point_block01 t
  · exact g32p_centralizerBound016_point_block02 t
  · exact g32p_centralizerBound016_point_block03 t
  · exact g32p_centralizerBound016_point_block04 t
  · exact g32p_centralizerBound016_point_block05 t
  · exact g32p_centralizerBound016_point_block06 t
  · exact g32p_centralizerBound016_point_block07 t
  · exact g32p_centralizerBound016_point_block08 t
  · exact g32p_centralizerBound016_point_block09 t
  · exact g32p_centralizerBound016_point_block10 t
  · exact g32p_centralizerBound016_point_block11 t
  · exact g32p_centralizerBound016_point_block12 t
  · exact g32p_centralizerBound016_point_block13 t
  · exact g32p_centralizerBound016_point_block14 t

theorem g32p_centralizerBound016_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 16) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 16)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound016_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound016_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 16) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 16)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound016_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound016_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 16) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 16)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound016_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound016_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 16) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 16)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound016_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound016_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 16) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 16)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound016_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound016_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 16) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 16) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound016_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 16) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 16)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound016_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound016_stabilizer_block00 t r
  · exact g32p_centralizerBound016_stabilizer_block01 t r
  · exact g32p_centralizerBound016_stabilizer_block02 t r
  · exact g32p_centralizerBound016_stabilizer_block03 t r
  · exact g32p_centralizerBound016_stabilizer_block04 t r

theorem g32p_centralizerBound016_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 16}) ≤ g32p_literalCentralizer 16 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 16 g32p_centralizerBound016_points
    g32p_centralizerBound016_stabilizers ?_ g32p_centralizerBound016_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound016_point_mem i (g32p_centralizer_point_moments 16 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound017_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 11, 14, 15, 16, 20, 25, 27, 28, 29, 31, 34, 35, 36, 38, 42, 47, 49, 50, 51, 53, 56, 57, 58, 62, 64, 66, 76, 79, 83, 88, 90, 91, 92, 94, 97, 98, 99, 103, 105, 107, 117, 120, 124, 127, 130, 134, 135, 141, 145, 147, 148, 152, 154, 156, 166, 169, 173, 178, 182, 183, 192, 194, 195, 199, 205, 215, 226}

def g32p_centralizerBound017_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound017_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) := by
  decide +kernel

theorem g32p_centralizerBound017_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) := by
  decide +kernel

theorem g32p_centralizerBound017_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) := by
  decide +kernel

theorem g32p_centralizerBound017_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) := by
  decide +kernel

theorem g32p_centralizerBound017_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) := by
  decide +kernel

theorem g32p_centralizerBound017_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) := by
  decide +kernel

theorem g32p_centralizerBound017_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) := by
  decide +kernel

theorem g32p_centralizerBound017_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) := by
  decide +kernel

theorem g32p_centralizerBound017_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) := by
  decide +kernel

theorem g32p_centralizerBound017_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) := by
  decide +kernel

theorem g32p_centralizerBound017_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) := by
  decide +kernel

theorem g32p_centralizerBound017_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) := by
  decide +kernel

theorem g32p_centralizerBound017_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) := by
  decide +kernel

theorem g32p_centralizerBound017_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) := by
  decide +kernel

theorem g32p_centralizerBound017_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) := by
  decide +kernel

theorem g32p_centralizerBound017_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 17) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound017_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound017_point_block00 t
  · exact g32p_centralizerBound017_point_block01 t
  · exact g32p_centralizerBound017_point_block02 t
  · exact g32p_centralizerBound017_point_block03 t
  · exact g32p_centralizerBound017_point_block04 t
  · exact g32p_centralizerBound017_point_block05 t
  · exact g32p_centralizerBound017_point_block06 t
  · exact g32p_centralizerBound017_point_block07 t
  · exact g32p_centralizerBound017_point_block08 t
  · exact g32p_centralizerBound017_point_block09 t
  · exact g32p_centralizerBound017_point_block10 t
  · exact g32p_centralizerBound017_point_block11 t
  · exact g32p_centralizerBound017_point_block12 t
  · exact g32p_centralizerBound017_point_block13 t
  · exact g32p_centralizerBound017_point_block14 t

theorem g32p_centralizerBound017_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 17) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 17)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound017_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound017_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 17) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 17)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound017_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound017_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 17) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 17)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound017_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound017_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 17) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 17)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound017_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound017_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 17) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 17)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound017_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound017_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 17) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 17) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound017_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 17) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 17)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound017_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound017_stabilizer_block00 t r
  · exact g32p_centralizerBound017_stabilizer_block01 t r
  · exact g32p_centralizerBound017_stabilizer_block02 t r
  · exact g32p_centralizerBound017_stabilizer_block03 t r
  · exact g32p_centralizerBound017_stabilizer_block04 t r

theorem g32p_centralizerBound017_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 17}) ≤ g32p_literalCentralizer 17 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 17 g32p_centralizerBound017_points
    g32p_centralizerBound017_stabilizers ?_ g32p_centralizerBound017_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound017_point_mem i (g32p_centralizer_point_moments 17 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound018_points : Finset (Fin 240) :=
  {3, 6, 9, 10, 11, 12, 13, 15, 18, 19, 20, 21, 22, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 40, 41, 42, 43, 44, 46, 48, 49, 50, 52, 53, 54, 55, 56, 57, 58, 59, 61, 62, 63, 64, 65, 67, 68, 69, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85, 87, 89, 90, 91, 93, 94, 95, 96, 97, 98, 99, 100, 102, 103, 104, 105, 106, 108, 109, 110, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 130, 131, 132, 133, 134, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 151, 152, 153, 154, 155, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 173, 174, 175, 176, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 202, 203, 204, 206, 209, 210, 212, 213, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 233, 234, 236, 237}

def g32p_centralizerBound018_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (18, 2), (22, 7), (24, 2), (30, 4), (36, 5), (53, 8), (63, 3), (68, 7)}

theorem g32p_centralizerBound018_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) := by
  decide +kernel

theorem g32p_centralizerBound018_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) := by
  decide +kernel

theorem g32p_centralizerBound018_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) := by
  decide +kernel

theorem g32p_centralizerBound018_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) := by
  decide +kernel

theorem g32p_centralizerBound018_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) := by
  decide +kernel

theorem g32p_centralizerBound018_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) := by
  decide +kernel

theorem g32p_centralizerBound018_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) := by
  decide +kernel

theorem g32p_centralizerBound018_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) := by
  decide +kernel

theorem g32p_centralizerBound018_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) := by
  decide +kernel

theorem g32p_centralizerBound018_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) := by
  decide +kernel

theorem g32p_centralizerBound018_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) := by
  decide +kernel

theorem g32p_centralizerBound018_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) := by
  decide +kernel

theorem g32p_centralizerBound018_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) := by
  decide +kernel

theorem g32p_centralizerBound018_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) := by
  decide +kernel

theorem g32p_centralizerBound018_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) := by
  decide +kernel

theorem g32p_centralizerBound018_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 18) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound018_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound018_point_block00 t
  · exact g32p_centralizerBound018_point_block01 t
  · exact g32p_centralizerBound018_point_block02 t
  · exact g32p_centralizerBound018_point_block03 t
  · exact g32p_centralizerBound018_point_block04 t
  · exact g32p_centralizerBound018_point_block05 t
  · exact g32p_centralizerBound018_point_block06 t
  · exact g32p_centralizerBound018_point_block07 t
  · exact g32p_centralizerBound018_point_block08 t
  · exact g32p_centralizerBound018_point_block09 t
  · exact g32p_centralizerBound018_point_block10 t
  · exact g32p_centralizerBound018_point_block11 t
  · exact g32p_centralizerBound018_point_block12 t
  · exact g32p_centralizerBound018_point_block13 t
  · exact g32p_centralizerBound018_point_block14 t

theorem g32p_centralizerBound018_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 18) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 18)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound018_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound018_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 18) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 18)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound018_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound018_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 18) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 18)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound018_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound018_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 18) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 18)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound018_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound018_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 18) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 18)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound018_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound018_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 18) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 18) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound018_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 18) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 18)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound018_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound018_stabilizer_block00 t r
  · exact g32p_centralizerBound018_stabilizer_block01 t r
  · exact g32p_centralizerBound018_stabilizer_block02 t r
  · exact g32p_centralizerBound018_stabilizer_block03 t r
  · exact g32p_centralizerBound018_stabilizer_block04 t r

theorem g32p_centralizerBound018_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 18}) ≤ g32p_literalCentralizer 18 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 18 g32p_centralizerBound018_points
    g32p_centralizerBound018_stabilizers ?_ g32p_centralizerBound018_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound018_point_mem i (g32p_centralizer_point_moments 18 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound019_points : Finset (Fin 240) :=
  {3, 6, 7, 10, 15, 16, 19, 27, 36, 38, 41, 49, 58, 62, 66, 68, 90, 99, 103, 107, 109, 152, 156, 158}

def g32p_centralizerBound019_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (4, 7), (6, 3), (7, 0), (12, 1), (18, 2), (25, 7), (27, 0), (29, 7), (31, 3), (38, 1), (45, 1), (50, 1), (59, 7), (61, 5), (62, 6), (64, 3), (68, 7)}

theorem g32p_centralizerBound019_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) := by
  decide +kernel

theorem g32p_centralizerBound019_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) := by
  decide +kernel

theorem g32p_centralizerBound019_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) := by
  decide +kernel

theorem g32p_centralizerBound019_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) := by
  decide +kernel

theorem g32p_centralizerBound019_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) := by
  decide +kernel

theorem g32p_centralizerBound019_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) := by
  decide +kernel

theorem g32p_centralizerBound019_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) := by
  decide +kernel

theorem g32p_centralizerBound019_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) := by
  decide +kernel

theorem g32p_centralizerBound019_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) := by
  decide +kernel

theorem g32p_centralizerBound019_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) := by
  decide +kernel

theorem g32p_centralizerBound019_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) := by
  decide +kernel

theorem g32p_centralizerBound019_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) := by
  decide +kernel

theorem g32p_centralizerBound019_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) := by
  decide +kernel

theorem g32p_centralizerBound019_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) := by
  decide +kernel

theorem g32p_centralizerBound019_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) := by
  decide +kernel

theorem g32p_centralizerBound019_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 19) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound019_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound019_point_block00 t
  · exact g32p_centralizerBound019_point_block01 t
  · exact g32p_centralizerBound019_point_block02 t
  · exact g32p_centralizerBound019_point_block03 t
  · exact g32p_centralizerBound019_point_block04 t
  · exact g32p_centralizerBound019_point_block05 t
  · exact g32p_centralizerBound019_point_block06 t
  · exact g32p_centralizerBound019_point_block07 t
  · exact g32p_centralizerBound019_point_block08 t
  · exact g32p_centralizerBound019_point_block09 t
  · exact g32p_centralizerBound019_point_block10 t
  · exact g32p_centralizerBound019_point_block11 t
  · exact g32p_centralizerBound019_point_block12 t
  · exact g32p_centralizerBound019_point_block13 t
  · exact g32p_centralizerBound019_point_block14 t

theorem g32p_centralizerBound019_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 19) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 19)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound019_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound019_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 19) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 19)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound019_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound019_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 19) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 19)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound019_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound019_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 19) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 19)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound019_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound019_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 19) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 19)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound019_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound019_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 19) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 19) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound019_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 19) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 19)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound019_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound019_stabilizer_block00 t r
  · exact g32p_centralizerBound019_stabilizer_block01 t r
  · exact g32p_centralizerBound019_stabilizer_block02 t r
  · exact g32p_centralizerBound019_stabilizer_block03 t r
  · exact g32p_centralizerBound019_stabilizer_block04 t r

theorem g32p_centralizerBound019_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 19}) ≤ g32p_literalCentralizer 19 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 19 g32p_centralizerBound019_points
    g32p_centralizerBound019_stabilizers ?_ g32p_centralizerBound019_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound019_point_mem i (g32p_centralizer_point_moments 19 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound020_points : Finset (Fin 240) :=
  {3, 6, 15, 33, 36, 55, 58, 85, 96, 99, 126, 140, 144, 175, 188, 191, 222, 225}

def g32p_centralizerBound020_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (26, 2), (53, 2), (70, 7)}

theorem g32p_centralizerBound020_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) := by
  decide +kernel

theorem g32p_centralizerBound020_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) := by
  decide +kernel

theorem g32p_centralizerBound020_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) := by
  decide +kernel

theorem g32p_centralizerBound020_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) := by
  decide +kernel

theorem g32p_centralizerBound020_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) := by
  decide +kernel

theorem g32p_centralizerBound020_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) := by
  decide +kernel

theorem g32p_centralizerBound020_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) := by
  decide +kernel

theorem g32p_centralizerBound020_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) := by
  decide +kernel

theorem g32p_centralizerBound020_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) := by
  decide +kernel

theorem g32p_centralizerBound020_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) := by
  decide +kernel

theorem g32p_centralizerBound020_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) := by
  decide +kernel

theorem g32p_centralizerBound020_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) := by
  decide +kernel

theorem g32p_centralizerBound020_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) := by
  decide +kernel

theorem g32p_centralizerBound020_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) := by
  decide +kernel

theorem g32p_centralizerBound020_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) := by
  decide +kernel

theorem g32p_centralizerBound020_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 20) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound020_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound020_point_block00 t
  · exact g32p_centralizerBound020_point_block01 t
  · exact g32p_centralizerBound020_point_block02 t
  · exact g32p_centralizerBound020_point_block03 t
  · exact g32p_centralizerBound020_point_block04 t
  · exact g32p_centralizerBound020_point_block05 t
  · exact g32p_centralizerBound020_point_block06 t
  · exact g32p_centralizerBound020_point_block07 t
  · exact g32p_centralizerBound020_point_block08 t
  · exact g32p_centralizerBound020_point_block09 t
  · exact g32p_centralizerBound020_point_block10 t
  · exact g32p_centralizerBound020_point_block11 t
  · exact g32p_centralizerBound020_point_block12 t
  · exact g32p_centralizerBound020_point_block13 t
  · exact g32p_centralizerBound020_point_block14 t

theorem g32p_centralizerBound020_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 20) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 20)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound020_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound020_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 20) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 20)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound020_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound020_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 20) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 20)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound020_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound020_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 20) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 20)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound020_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound020_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 20) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 20)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound020_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound020_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 20) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 20) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound020_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 20) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 20)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound020_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound020_stabilizer_block00 t r
  · exact g32p_centralizerBound020_stabilizer_block01 t r
  · exact g32p_centralizerBound020_stabilizer_block02 t r
  · exact g32p_centralizerBound020_stabilizer_block03 t r
  · exact g32p_centralizerBound020_stabilizer_block04 t r

theorem g32p_centralizerBound020_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 20}) ≤ g32p_literalCentralizer 20 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 20 g32p_centralizerBound020_points
    g32p_centralizerBound020_stabilizers ?_ g32p_centralizerBound020_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound020_point_mem i (g32p_centralizer_point_moments 20 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound021_points : Finset (Fin 240) :=
  {3, 6, 9, 11, 15, 18, 20, 33, 36, 40, 42, 55, 58, 63, 67, 80, 83, 96, 99, 104, 108, 121, 124, 133, 142, 144, 153, 157, 170, 173, 181, 189, 191, 218, 223, 225}

def g32p_centralizerBound021_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound021_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) := by
  decide +kernel

theorem g32p_centralizerBound021_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) := by
  decide +kernel

theorem g32p_centralizerBound021_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) := by
  decide +kernel

theorem g32p_centralizerBound021_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) := by
  decide +kernel

theorem g32p_centralizerBound021_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) := by
  decide +kernel

theorem g32p_centralizerBound021_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) := by
  decide +kernel

theorem g32p_centralizerBound021_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) := by
  decide +kernel

theorem g32p_centralizerBound021_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) := by
  decide +kernel

theorem g32p_centralizerBound021_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) := by
  decide +kernel

theorem g32p_centralizerBound021_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) := by
  decide +kernel

theorem g32p_centralizerBound021_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) := by
  decide +kernel

theorem g32p_centralizerBound021_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) := by
  decide +kernel

theorem g32p_centralizerBound021_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) := by
  decide +kernel

theorem g32p_centralizerBound021_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) := by
  decide +kernel

theorem g32p_centralizerBound021_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) := by
  decide +kernel

theorem g32p_centralizerBound021_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 21) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound021_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound021_point_block00 t
  · exact g32p_centralizerBound021_point_block01 t
  · exact g32p_centralizerBound021_point_block02 t
  · exact g32p_centralizerBound021_point_block03 t
  · exact g32p_centralizerBound021_point_block04 t
  · exact g32p_centralizerBound021_point_block05 t
  · exact g32p_centralizerBound021_point_block06 t
  · exact g32p_centralizerBound021_point_block07 t
  · exact g32p_centralizerBound021_point_block08 t
  · exact g32p_centralizerBound021_point_block09 t
  · exact g32p_centralizerBound021_point_block10 t
  · exact g32p_centralizerBound021_point_block11 t
  · exact g32p_centralizerBound021_point_block12 t
  · exact g32p_centralizerBound021_point_block13 t
  · exact g32p_centralizerBound021_point_block14 t

theorem g32p_centralizerBound021_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 21) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 21)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound021_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound021_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 21) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 21)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound021_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound021_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 21) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 21)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound021_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound021_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 21) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 21)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound021_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound021_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 21) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 21)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound021_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound021_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 21) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 21) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound021_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 21) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 21)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound021_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound021_stabilizer_block00 t r
  · exact g32p_centralizerBound021_stabilizer_block01 t r
  · exact g32p_centralizerBound021_stabilizer_block02 t r
  · exact g32p_centralizerBound021_stabilizer_block03 t r
  · exact g32p_centralizerBound021_stabilizer_block04 t r

theorem g32p_centralizerBound021_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 21}) ≤ g32p_literalCentralizer 21 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 21 g32p_centralizerBound021_points
    g32p_centralizerBound021_stabilizers ?_ g32p_centralizerBound021_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound021_point_mem i (g32p_centralizer_point_moments 21 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound022_points : Finset (Fin 240) :=
  {3, 6, 15, 36, 58, 63, 78, 79, 80, 99, 104, 119, 120, 121, 138, 145, 149, 153, 168, 169, 170, 186, 192, 196, 204, 206, 209, 226, 227, 233}

def g32p_centralizerBound022_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound022_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) := by
  decide +kernel

theorem g32p_centralizerBound022_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) := by
  decide +kernel

theorem g32p_centralizerBound022_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) := by
  decide +kernel

theorem g32p_centralizerBound022_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) := by
  decide +kernel

theorem g32p_centralizerBound022_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) := by
  decide +kernel

theorem g32p_centralizerBound022_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) := by
  decide +kernel

theorem g32p_centralizerBound022_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) := by
  decide +kernel

theorem g32p_centralizerBound022_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) := by
  decide +kernel

theorem g32p_centralizerBound022_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) := by
  decide +kernel

theorem g32p_centralizerBound022_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) := by
  decide +kernel

theorem g32p_centralizerBound022_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) := by
  decide +kernel

theorem g32p_centralizerBound022_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) := by
  decide +kernel

theorem g32p_centralizerBound022_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) := by
  decide +kernel

theorem g32p_centralizerBound022_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) := by
  decide +kernel

theorem g32p_centralizerBound022_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) := by
  decide +kernel

theorem g32p_centralizerBound022_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 22) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound022_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound022_point_block00 t
  · exact g32p_centralizerBound022_point_block01 t
  · exact g32p_centralizerBound022_point_block02 t
  · exact g32p_centralizerBound022_point_block03 t
  · exact g32p_centralizerBound022_point_block04 t
  · exact g32p_centralizerBound022_point_block05 t
  · exact g32p_centralizerBound022_point_block06 t
  · exact g32p_centralizerBound022_point_block07 t
  · exact g32p_centralizerBound022_point_block08 t
  · exact g32p_centralizerBound022_point_block09 t
  · exact g32p_centralizerBound022_point_block10 t
  · exact g32p_centralizerBound022_point_block11 t
  · exact g32p_centralizerBound022_point_block12 t
  · exact g32p_centralizerBound022_point_block13 t
  · exact g32p_centralizerBound022_point_block14 t

theorem g32p_centralizerBound022_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 22) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 22)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound022_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound022_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 22) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 22)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound022_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound022_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 22) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 22)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound022_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound022_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 22) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 22)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound022_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound022_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 22) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 22)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound022_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound022_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 22) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 22) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound022_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 22) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 22)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound022_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound022_stabilizer_block00 t r
  · exact g32p_centralizerBound022_stabilizer_block01 t r
  · exact g32p_centralizerBound022_stabilizer_block02 t r
  · exact g32p_centralizerBound022_stabilizer_block03 t r
  · exact g32p_centralizerBound022_stabilizer_block04 t r

theorem g32p_centralizerBound022_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 22}) ≤ g32p_literalCentralizer 22 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 22 g32p_centralizerBound022_points
    g32p_centralizerBound022_stabilizers ?_ g32p_centralizerBound022_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound022_point_mem i (g32p_centralizer_point_moments 22 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound023_points : Finset (Fin 240) :=
  {3, 6, 11, 12, 13, 15, 20, 21, 22, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 42, 43, 44, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 62, 65, 70, 71, 73, 74, 75, 76, 77, 79, 81, 83, 84, 85, 90, 92, 93, 94, 95, 96, 97, 98, 99, 100, 103, 106, 111, 112, 114, 115, 116, 117, 118, 120, 122, 124, 125, 126, 129, 132, 133, 135, 136, 137, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 152, 155, 160, 161, 163, 164, 165, 166, 167, 169, 171, 173, 174, 175, 177, 180, 181, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 198, 199, 200, 201, 203, 205, 208, 210, 212, 214, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 228, 229, 231, 232, 234, 236, 237, 238, 239}

def g32p_centralizerBound023_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (1, 3), (12, 7)}

theorem g32p_centralizerBound023_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) := by
  decide +kernel

theorem g32p_centralizerBound023_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) := by
  decide +kernel

theorem g32p_centralizerBound023_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) := by
  decide +kernel

theorem g32p_centralizerBound023_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) := by
  decide +kernel

theorem g32p_centralizerBound023_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) := by
  decide +kernel

theorem g32p_centralizerBound023_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) := by
  decide +kernel

theorem g32p_centralizerBound023_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) := by
  decide +kernel

theorem g32p_centralizerBound023_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) := by
  decide +kernel

theorem g32p_centralizerBound023_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) := by
  decide +kernel

theorem g32p_centralizerBound023_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) := by
  decide +kernel

theorem g32p_centralizerBound023_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) := by
  decide +kernel

theorem g32p_centralizerBound023_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) := by
  decide +kernel

theorem g32p_centralizerBound023_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) := by
  decide +kernel

theorem g32p_centralizerBound023_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) := by
  decide +kernel

theorem g32p_centralizerBound023_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) := by
  decide +kernel

theorem g32p_centralizerBound023_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 23) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound023_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound023_point_block00 t
  · exact g32p_centralizerBound023_point_block01 t
  · exact g32p_centralizerBound023_point_block02 t
  · exact g32p_centralizerBound023_point_block03 t
  · exact g32p_centralizerBound023_point_block04 t
  · exact g32p_centralizerBound023_point_block05 t
  · exact g32p_centralizerBound023_point_block06 t
  · exact g32p_centralizerBound023_point_block07 t
  · exact g32p_centralizerBound023_point_block08 t
  · exact g32p_centralizerBound023_point_block09 t
  · exact g32p_centralizerBound023_point_block10 t
  · exact g32p_centralizerBound023_point_block11 t
  · exact g32p_centralizerBound023_point_block12 t
  · exact g32p_centralizerBound023_point_block13 t
  · exact g32p_centralizerBound023_point_block14 t

theorem g32p_centralizerBound023_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 23) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 23)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound023_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound023_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 23) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 23)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound023_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound023_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 23) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 23)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound023_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound023_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 23) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 23)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound023_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound023_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 23) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 23)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound023_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound023_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 23) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 23) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound023_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 23) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 23)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound023_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound023_stabilizer_block00 t r
  · exact g32p_centralizerBound023_stabilizer_block01 t r
  · exact g32p_centralizerBound023_stabilizer_block02 t r
  · exact g32p_centralizerBound023_stabilizer_block03 t r
  · exact g32p_centralizerBound023_stabilizer_block04 t r

theorem g32p_centralizerBound023_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 23}) ≤ g32p_literalCentralizer 23 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 23 g32p_centralizerBound023_points
    g32p_centralizerBound023_stabilizers ?_ g32p_centralizerBound023_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound023_point_mem i (g32p_centralizer_point_moments 23 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound024_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 9, 11, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 31, 33, 36, 38, 40, 42, 43, 46, 47, 49, 53, 55, 58, 62, 65, 66, 67, 70, 72, 75, 76, 78, 82, 83, 84, 87, 88, 90, 94, 96, 99, 103, 106, 107, 108, 111, 113, 116, 117, 119, 123, 124, 125, 129, 131, 136, 138, 139, 144, 146, 149, 152, 155, 156, 157, 160, 162, 165, 166, 168, 172, 173, 174, 177, 179, 184, 186, 187, 191, 193, 196, 197, 198, 200, 202, 204, 206, 207, 209, 211, 212, 214, 216, 219, 221, 225, 227, 228, 230, 233, 235}

def g32p_centralizerBound024_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (1, 3), (12, 7), (20, 4), (24, 1), (26, 2)}

theorem g32p_centralizerBound024_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) := by
  decide +kernel

theorem g32p_centralizerBound024_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) := by
  decide +kernel

theorem g32p_centralizerBound024_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) := by
  decide +kernel

theorem g32p_centralizerBound024_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) := by
  decide +kernel

theorem g32p_centralizerBound024_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) := by
  decide +kernel

theorem g32p_centralizerBound024_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) := by
  decide +kernel

theorem g32p_centralizerBound024_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) := by
  decide +kernel

theorem g32p_centralizerBound024_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) := by
  decide +kernel

theorem g32p_centralizerBound024_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) := by
  decide +kernel

theorem g32p_centralizerBound024_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) := by
  decide +kernel

theorem g32p_centralizerBound024_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) := by
  decide +kernel

theorem g32p_centralizerBound024_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) := by
  decide +kernel

theorem g32p_centralizerBound024_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) := by
  decide +kernel

theorem g32p_centralizerBound024_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) := by
  decide +kernel

theorem g32p_centralizerBound024_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) := by
  decide +kernel

theorem g32p_centralizerBound024_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 24) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound024_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound024_point_block00 t
  · exact g32p_centralizerBound024_point_block01 t
  · exact g32p_centralizerBound024_point_block02 t
  · exact g32p_centralizerBound024_point_block03 t
  · exact g32p_centralizerBound024_point_block04 t
  · exact g32p_centralizerBound024_point_block05 t
  · exact g32p_centralizerBound024_point_block06 t
  · exact g32p_centralizerBound024_point_block07 t
  · exact g32p_centralizerBound024_point_block08 t
  · exact g32p_centralizerBound024_point_block09 t
  · exact g32p_centralizerBound024_point_block10 t
  · exact g32p_centralizerBound024_point_block11 t
  · exact g32p_centralizerBound024_point_block12 t
  · exact g32p_centralizerBound024_point_block13 t
  · exact g32p_centralizerBound024_point_block14 t

theorem g32p_centralizerBound024_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 24) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 24)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound024_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound024_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 24) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 24)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound024_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound024_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 24) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 24)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound024_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound024_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 24) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 24)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound024_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound024_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 24) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 24)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound024_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound024_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 24) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 24) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound024_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 24) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 24)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound024_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound024_stabilizer_block00 t r
  · exact g32p_centralizerBound024_stabilizer_block01 t r
  · exact g32p_centralizerBound024_stabilizer_block02 t r
  · exact g32p_centralizerBound024_stabilizer_block03 t r
  · exact g32p_centralizerBound024_stabilizer_block04 t r

theorem g32p_centralizerBound024_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 24}) ≤ g32p_literalCentralizer 24 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 24 g32p_centralizerBound024_points
    g32p_centralizerBound024_stabilizers ?_ g32p_centralizerBound024_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound024_point_mem i (g32p_centralizer_point_moments 24 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound025_points : Finset (Fin 240) :=
  {3, 6, 10, 11, 12, 13, 15, 19, 20, 21, 22, 30, 32, 33, 35, 36, 37, 41, 42, 43, 44, 52, 54, 55, 57, 58, 59, 65, 68, 71, 73, 74, 77, 78, 79, 81, 83, 84, 85, 93, 95, 96, 98, 99, 100, 106, 109, 112, 114, 115, 118, 119, 120, 122, 124, 125, 126, 136, 137, 138, 140, 141, 144, 145, 146, 148, 149, 155, 158, 161, 163, 164, 167, 168, 169, 171, 173, 174, 175, 184, 185, 186, 188, 191, 192, 193, 195, 196, 198, 200, 203, 204, 206, 209, 210, 212, 219, 220, 222, 225, 226, 227, 228, 231, 233, 234, 236, 237}

def g32p_centralizerBound025_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound025_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) := by
  decide +kernel

theorem g32p_centralizerBound025_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) := by
  decide +kernel

theorem g32p_centralizerBound025_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) := by
  decide +kernel

theorem g32p_centralizerBound025_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) := by
  decide +kernel

theorem g32p_centralizerBound025_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) := by
  decide +kernel

theorem g32p_centralizerBound025_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) := by
  decide +kernel

theorem g32p_centralizerBound025_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) := by
  decide +kernel

theorem g32p_centralizerBound025_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) := by
  decide +kernel

theorem g32p_centralizerBound025_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) := by
  decide +kernel

theorem g32p_centralizerBound025_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) := by
  decide +kernel

theorem g32p_centralizerBound025_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) := by
  decide +kernel

theorem g32p_centralizerBound025_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) := by
  decide +kernel

theorem g32p_centralizerBound025_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) := by
  decide +kernel

theorem g32p_centralizerBound025_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) := by
  decide +kernel

theorem g32p_centralizerBound025_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) := by
  decide +kernel

theorem g32p_centralizerBound025_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 25) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound025_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound025_point_block00 t
  · exact g32p_centralizerBound025_point_block01 t
  · exact g32p_centralizerBound025_point_block02 t
  · exact g32p_centralizerBound025_point_block03 t
  · exact g32p_centralizerBound025_point_block04 t
  · exact g32p_centralizerBound025_point_block05 t
  · exact g32p_centralizerBound025_point_block06 t
  · exact g32p_centralizerBound025_point_block07 t
  · exact g32p_centralizerBound025_point_block08 t
  · exact g32p_centralizerBound025_point_block09 t
  · exact g32p_centralizerBound025_point_block10 t
  · exact g32p_centralizerBound025_point_block11 t
  · exact g32p_centralizerBound025_point_block12 t
  · exact g32p_centralizerBound025_point_block13 t
  · exact g32p_centralizerBound025_point_block14 t

theorem g32p_centralizerBound025_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 25) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 25)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound025_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound025_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 25) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 25)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound025_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound025_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 25) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 25)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound025_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound025_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 25) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 25)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound025_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound025_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 25) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 25)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound025_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound025_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 25) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 25) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound025_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 25) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 25)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound025_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound025_stabilizer_block00 t r
  · exact g32p_centralizerBound025_stabilizer_block01 t r
  · exact g32p_centralizerBound025_stabilizer_block02 t r
  · exact g32p_centralizerBound025_stabilizer_block03 t r
  · exact g32p_centralizerBound025_stabilizer_block04 t r

theorem g32p_centralizerBound025_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 25}) ≤ g32p_literalCentralizer 25 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 25 g32p_centralizerBound025_points
    g32p_centralizerBound025_stabilizers ?_ g32p_centralizerBound025_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound025_point_mem i (g32p_centralizer_point_moments 25 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound026_points : Finset (Fin 240) :=
  {3, 6, 11, 15, 20, 36, 42, 58, 75, 79, 83, 99, 116, 120, 124, 138, 139, 145, 149, 165, 169, 173, 186, 187, 192, 196, 206, 221, 226, 227}

def g32p_centralizerBound026_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound026_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) := by
  decide +kernel

theorem g32p_centralizerBound026_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) := by
  decide +kernel

theorem g32p_centralizerBound026_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) := by
  decide +kernel

theorem g32p_centralizerBound026_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) := by
  decide +kernel

theorem g32p_centralizerBound026_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) := by
  decide +kernel

theorem g32p_centralizerBound026_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) := by
  decide +kernel

theorem g32p_centralizerBound026_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) := by
  decide +kernel

theorem g32p_centralizerBound026_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) := by
  decide +kernel

theorem g32p_centralizerBound026_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) := by
  decide +kernel

theorem g32p_centralizerBound026_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) := by
  decide +kernel

theorem g32p_centralizerBound026_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) := by
  decide +kernel

theorem g32p_centralizerBound026_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) := by
  decide +kernel

theorem g32p_centralizerBound026_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) := by
  decide +kernel

theorem g32p_centralizerBound026_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) := by
  decide +kernel

theorem g32p_centralizerBound026_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) := by
  decide +kernel

theorem g32p_centralizerBound026_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 26) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound026_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound026_point_block00 t
  · exact g32p_centralizerBound026_point_block01 t
  · exact g32p_centralizerBound026_point_block02 t
  · exact g32p_centralizerBound026_point_block03 t
  · exact g32p_centralizerBound026_point_block04 t
  · exact g32p_centralizerBound026_point_block05 t
  · exact g32p_centralizerBound026_point_block06 t
  · exact g32p_centralizerBound026_point_block07 t
  · exact g32p_centralizerBound026_point_block08 t
  · exact g32p_centralizerBound026_point_block09 t
  · exact g32p_centralizerBound026_point_block10 t
  · exact g32p_centralizerBound026_point_block11 t
  · exact g32p_centralizerBound026_point_block12 t
  · exact g32p_centralizerBound026_point_block13 t
  · exact g32p_centralizerBound026_point_block14 t

theorem g32p_centralizerBound026_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 26) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 26)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound026_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound026_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 26) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 26)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound026_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound026_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 26) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 26)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound026_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound026_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 26) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 26)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound026_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound026_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 26) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 26)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound026_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound026_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 26) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 26) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound026_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 26) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 26)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound026_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound026_stabilizer_block00 t r
  · exact g32p_centralizerBound026_stabilizer_block01 t r
  · exact g32p_centralizerBound026_stabilizer_block02 t r
  · exact g32p_centralizerBound026_stabilizer_block03 t r
  · exact g32p_centralizerBound026_stabilizer_block04 t r

theorem g32p_centralizerBound026_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 26}) ≤ g32p_literalCentralizer 26 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 26 g32p_centralizerBound026_points
    g32p_centralizerBound026_stabilizers ?_ g32p_centralizerBound026_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound026_point_mem i (g32p_centralizer_point_moments 26 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound027_points : Finset (Fin 240) :=
  {3, 6, 15, 33, 36, 55, 58, 82, 96, 99, 123, 144, 172, 191, 207, 211, 225, 235}

def g32p_centralizerBound027_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (26, 2), (53, 2), (70, 7)}

theorem g32p_centralizerBound027_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) := by
  decide +kernel

theorem g32p_centralizerBound027_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) := by
  decide +kernel

theorem g32p_centralizerBound027_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) := by
  decide +kernel

theorem g32p_centralizerBound027_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) := by
  decide +kernel

theorem g32p_centralizerBound027_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) := by
  decide +kernel

theorem g32p_centralizerBound027_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) := by
  decide +kernel

theorem g32p_centralizerBound027_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) := by
  decide +kernel

theorem g32p_centralizerBound027_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) := by
  decide +kernel

theorem g32p_centralizerBound027_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) := by
  decide +kernel

theorem g32p_centralizerBound027_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) := by
  decide +kernel

theorem g32p_centralizerBound027_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) := by
  decide +kernel

theorem g32p_centralizerBound027_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) := by
  decide +kernel

theorem g32p_centralizerBound027_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) := by
  decide +kernel

theorem g32p_centralizerBound027_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) := by
  decide +kernel

theorem g32p_centralizerBound027_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) := by
  decide +kernel

theorem g32p_centralizerBound027_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 27) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound027_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound027_point_block00 t
  · exact g32p_centralizerBound027_point_block01 t
  · exact g32p_centralizerBound027_point_block02 t
  · exact g32p_centralizerBound027_point_block03 t
  · exact g32p_centralizerBound027_point_block04 t
  · exact g32p_centralizerBound027_point_block05 t
  · exact g32p_centralizerBound027_point_block06 t
  · exact g32p_centralizerBound027_point_block07 t
  · exact g32p_centralizerBound027_point_block08 t
  · exact g32p_centralizerBound027_point_block09 t
  · exact g32p_centralizerBound027_point_block10 t
  · exact g32p_centralizerBound027_point_block11 t
  · exact g32p_centralizerBound027_point_block12 t
  · exact g32p_centralizerBound027_point_block13 t
  · exact g32p_centralizerBound027_point_block14 t

theorem g32p_centralizerBound027_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 27) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 27)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound027_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound027_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 27) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 27)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound027_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound027_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 27) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 27)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound027_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound027_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 27) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 27)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound027_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound027_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 27) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 27)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound027_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound027_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 27) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 27) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound027_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 27) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 27)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound027_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound027_stabilizer_block00 t r
  · exact g32p_centralizerBound027_stabilizer_block01 t r
  · exact g32p_centralizerBound027_stabilizer_block02 t r
  · exact g32p_centralizerBound027_stabilizer_block03 t r
  · exact g32p_centralizerBound027_stabilizer_block04 t r

theorem g32p_centralizerBound027_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 27}) ≤ g32p_literalCentralizer 27 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 27 g32p_centralizerBound027_points
    g32p_centralizerBound027_stabilizers ?_ g32p_centralizerBound027_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound027_point_mem i (g32p_centralizer_point_moments 27 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound028_points : Finset (Fin 240) :=
  {3, 6, 7, 10, 15, 16, 19, 26, 27, 28, 29, 36, 38, 41, 48, 49, 50, 51, 58, 61, 62, 65, 66, 68, 72, 79, 89, 90, 91, 92, 99, 102, 103, 106, 107, 109, 113, 120, 127, 132, 134, 135, 136, 143, 145, 146, 151, 152, 155, 156, 158, 162, 169, 180, 182, 183, 184, 190, 192, 193, 197, 198, 200, 202, 205, 212, 217, 219, 224, 226, 228, 230}

def g32p_centralizerBound028_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (27, 0), (27, 1), (27, 2), (27, 3), (27, 4), (27, 5), (27, 6), (27, 7), (27, 8), (31, 0), (31, 1), (31, 2), (31, 3), (31, 4), (31, 5), (31, 6), (31, 7), (31, 8), (64, 0), (64, 1), (64, 2), (64, 3), (64, 4), (64, 5), (64, 6), (64, 7), (64, 8)}

theorem g32p_centralizerBound028_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) := by
  decide +kernel

theorem g32p_centralizerBound028_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) := by
  decide +kernel

theorem g32p_centralizerBound028_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) := by
  decide +kernel

theorem g32p_centralizerBound028_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) := by
  decide +kernel

theorem g32p_centralizerBound028_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) := by
  decide +kernel

theorem g32p_centralizerBound028_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) := by
  decide +kernel

theorem g32p_centralizerBound028_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) := by
  decide +kernel

theorem g32p_centralizerBound028_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) := by
  decide +kernel

theorem g32p_centralizerBound028_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) := by
  decide +kernel

theorem g32p_centralizerBound028_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) := by
  decide +kernel

theorem g32p_centralizerBound028_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) := by
  decide +kernel

theorem g32p_centralizerBound028_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) := by
  decide +kernel

theorem g32p_centralizerBound028_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) := by
  decide +kernel

theorem g32p_centralizerBound028_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) := by
  decide +kernel

theorem g32p_centralizerBound028_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) := by
  decide +kernel

theorem g32p_centralizerBound028_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 28) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound028_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound028_point_block00 t
  · exact g32p_centralizerBound028_point_block01 t
  · exact g32p_centralizerBound028_point_block02 t
  · exact g32p_centralizerBound028_point_block03 t
  · exact g32p_centralizerBound028_point_block04 t
  · exact g32p_centralizerBound028_point_block05 t
  · exact g32p_centralizerBound028_point_block06 t
  · exact g32p_centralizerBound028_point_block07 t
  · exact g32p_centralizerBound028_point_block08 t
  · exact g32p_centralizerBound028_point_block09 t
  · exact g32p_centralizerBound028_point_block10 t
  · exact g32p_centralizerBound028_point_block11 t
  · exact g32p_centralizerBound028_point_block12 t
  · exact g32p_centralizerBound028_point_block13 t
  · exact g32p_centralizerBound028_point_block14 t

theorem g32p_centralizerBound028_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 28) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 28)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound028_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound028_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 28) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 28)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound028_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound028_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 28) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 28)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound028_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound028_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 28) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 28)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound028_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound028_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 28) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 28)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound028_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound028_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 28) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 28) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound028_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 28) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 28)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound028_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound028_stabilizer_block00 t r
  · exact g32p_centralizerBound028_stabilizer_block01 t r
  · exact g32p_centralizerBound028_stabilizer_block02 t r
  · exact g32p_centralizerBound028_stabilizer_block03 t r
  · exact g32p_centralizerBound028_stabilizer_block04 t r

theorem g32p_centralizerBound028_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 28}) ≤ g32p_literalCentralizer 28 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 28 g32p_centralizerBound028_points
    g32p_centralizerBound028_stabilizers ?_ g32p_centralizerBound028_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound028_point_mem i (g32p_centralizer_point_moments 28 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound029_points : Finset (Fin 240) :=
  {3, 6, 10, 11, 12, 13, 15, 19, 20, 21, 22, 30, 32, 33, 35, 36, 37, 41, 42, 43, 44, 52, 54, 55, 57, 58, 59, 65, 68, 71, 73, 74, 77, 78, 79, 81, 83, 84, 85, 93, 95, 96, 98, 99, 100, 106, 109, 112, 114, 115, 118, 119, 120, 122, 124, 125, 126, 136, 137, 138, 140, 141, 144, 145, 146, 148, 149, 155, 158, 161, 163, 164, 167, 168, 169, 171, 173, 174, 175, 184, 185, 186, 188, 191, 192, 193, 195, 196, 198, 200, 203, 204, 206, 209, 210, 212, 219, 220, 222, 225, 226, 227, 228, 231, 233, 234, 236, 237}

def g32p_centralizerBound029_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound029_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) := by
  decide +kernel

theorem g32p_centralizerBound029_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) := by
  decide +kernel

theorem g32p_centralizerBound029_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) := by
  decide +kernel

theorem g32p_centralizerBound029_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) := by
  decide +kernel

theorem g32p_centralizerBound029_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) := by
  decide +kernel

theorem g32p_centralizerBound029_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) := by
  decide +kernel

theorem g32p_centralizerBound029_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) := by
  decide +kernel

theorem g32p_centralizerBound029_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) := by
  decide +kernel

theorem g32p_centralizerBound029_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) := by
  decide +kernel

theorem g32p_centralizerBound029_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) := by
  decide +kernel

theorem g32p_centralizerBound029_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) := by
  decide +kernel

theorem g32p_centralizerBound029_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) := by
  decide +kernel

theorem g32p_centralizerBound029_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) := by
  decide +kernel

theorem g32p_centralizerBound029_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) := by
  decide +kernel

theorem g32p_centralizerBound029_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) := by
  decide +kernel

theorem g32p_centralizerBound029_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 29) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound029_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound029_point_block00 t
  · exact g32p_centralizerBound029_point_block01 t
  · exact g32p_centralizerBound029_point_block02 t
  · exact g32p_centralizerBound029_point_block03 t
  · exact g32p_centralizerBound029_point_block04 t
  · exact g32p_centralizerBound029_point_block05 t
  · exact g32p_centralizerBound029_point_block06 t
  · exact g32p_centralizerBound029_point_block07 t
  · exact g32p_centralizerBound029_point_block08 t
  · exact g32p_centralizerBound029_point_block09 t
  · exact g32p_centralizerBound029_point_block10 t
  · exact g32p_centralizerBound029_point_block11 t
  · exact g32p_centralizerBound029_point_block12 t
  · exact g32p_centralizerBound029_point_block13 t
  · exact g32p_centralizerBound029_point_block14 t

theorem g32p_centralizerBound029_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 29) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 29)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound029_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound029_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 29) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 29)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound029_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound029_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 29) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 29)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound029_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound029_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 29) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 29)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound029_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound029_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 29) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 29)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound029_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound029_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 29) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 29) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound029_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 29) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 29)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound029_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound029_stabilizer_block00 t r
  · exact g32p_centralizerBound029_stabilizer_block01 t r
  · exact g32p_centralizerBound029_stabilizer_block02 t r
  · exact g32p_centralizerBound029_stabilizer_block03 t r
  · exact g32p_centralizerBound029_stabilizer_block04 t r

theorem g32p_centralizerBound029_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 29}) ≤ g32p_literalCentralizer 29 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 29 g32p_centralizerBound029_points
    g32p_centralizerBound029_stabilizers ?_ g32p_centralizerBound029_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound029_point_mem i (g32p_centralizer_point_moments 29 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound030_points : Finset (Fin 240) :=
  {3, 6, 9, 15, 18, 26, 27, 36, 40, 48, 49, 58, 61, 62, 67, 89, 90, 99, 102, 103, 108, 133, 136, 142, 146, 151, 152, 157, 181, 184, 189, 193, 198, 218, 219, 223}

def g32p_centralizerBound030_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound030_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) := by
  decide +kernel

theorem g32p_centralizerBound030_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) := by
  decide +kernel

theorem g32p_centralizerBound030_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) := by
  decide +kernel

theorem g32p_centralizerBound030_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) := by
  decide +kernel

theorem g32p_centralizerBound030_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) := by
  decide +kernel

theorem g32p_centralizerBound030_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) := by
  decide +kernel

theorem g32p_centralizerBound030_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) := by
  decide +kernel

theorem g32p_centralizerBound030_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) := by
  decide +kernel

theorem g32p_centralizerBound030_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) := by
  decide +kernel

theorem g32p_centralizerBound030_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) := by
  decide +kernel

theorem g32p_centralizerBound030_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) := by
  decide +kernel

theorem g32p_centralizerBound030_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) := by
  decide +kernel

theorem g32p_centralizerBound030_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) := by
  decide +kernel

theorem g32p_centralizerBound030_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) := by
  decide +kernel

theorem g32p_centralizerBound030_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) := by
  decide +kernel

theorem g32p_centralizerBound030_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 30) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound030_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound030_point_block00 t
  · exact g32p_centralizerBound030_point_block01 t
  · exact g32p_centralizerBound030_point_block02 t
  · exact g32p_centralizerBound030_point_block03 t
  · exact g32p_centralizerBound030_point_block04 t
  · exact g32p_centralizerBound030_point_block05 t
  · exact g32p_centralizerBound030_point_block06 t
  · exact g32p_centralizerBound030_point_block07 t
  · exact g32p_centralizerBound030_point_block08 t
  · exact g32p_centralizerBound030_point_block09 t
  · exact g32p_centralizerBound030_point_block10 t
  · exact g32p_centralizerBound030_point_block11 t
  · exact g32p_centralizerBound030_point_block12 t
  · exact g32p_centralizerBound030_point_block13 t
  · exact g32p_centralizerBound030_point_block14 t

theorem g32p_centralizerBound030_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 30) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 30)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound030_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound030_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 30) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 30)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound030_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound030_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 30) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 30)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound030_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound030_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 30) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 30)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound030_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound030_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 30) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 30)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound030_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound030_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 30) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 30) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound030_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 30) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 30)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound030_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound030_stabilizer_block00 t r
  · exact g32p_centralizerBound030_stabilizer_block01 t r
  · exact g32p_centralizerBound030_stabilizer_block02 t r
  · exact g32p_centralizerBound030_stabilizer_block03 t r
  · exact g32p_centralizerBound030_stabilizer_block04 t r

theorem g32p_centralizerBound030_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 30}) ≤ g32p_literalCentralizer 30 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 30 g32p_centralizerBound030_points
    g32p_centralizerBound030_stabilizers ?_ g32p_centralizerBound030_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound030_point_mem i (g32p_centralizer_point_moments 30 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound031_points : Finset (Fin 240) :=
  {3, 6, 7, 8, 9, 10, 11, 15, 16, 17, 18, 19, 20, 23, 26, 28, 30, 36, 38, 39, 40, 41, 42, 45, 48, 50, 52, 58, 61, 64, 65, 66, 67, 68, 71, 73, 78, 79, 83, 85, 86, 89, 91, 93, 99, 102, 105, 106, 107, 108, 109, 112, 114, 119, 120, 124, 126, 127, 130, 134, 136, 140, 145, 146, 151, 154, 155, 156, 157, 158, 161, 163, 168, 169, 173, 175, 178, 182, 184, 188, 192, 193, 198, 200, 203, 204, 209, 212, 215, 219, 222, 226, 228, 231, 233, 237}

def g32p_centralizerBound031_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 6), (0, 7)}

theorem g32p_centralizerBound031_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) := by
  decide +kernel

theorem g32p_centralizerBound031_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) := by
  decide +kernel

theorem g32p_centralizerBound031_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) := by
  decide +kernel

theorem g32p_centralizerBound031_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) := by
  decide +kernel

theorem g32p_centralizerBound031_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) := by
  decide +kernel

theorem g32p_centralizerBound031_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) := by
  decide +kernel

theorem g32p_centralizerBound031_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) := by
  decide +kernel

theorem g32p_centralizerBound031_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) := by
  decide +kernel

theorem g32p_centralizerBound031_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) := by
  decide +kernel

theorem g32p_centralizerBound031_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) := by
  decide +kernel

theorem g32p_centralizerBound031_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) := by
  decide +kernel

theorem g32p_centralizerBound031_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) := by
  decide +kernel

theorem g32p_centralizerBound031_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) := by
  decide +kernel

theorem g32p_centralizerBound031_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) := by
  decide +kernel

theorem g32p_centralizerBound031_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) := by
  decide +kernel

theorem g32p_centralizerBound031_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 31) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound031_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound031_point_block00 t
  · exact g32p_centralizerBound031_point_block01 t
  · exact g32p_centralizerBound031_point_block02 t
  · exact g32p_centralizerBound031_point_block03 t
  · exact g32p_centralizerBound031_point_block04 t
  · exact g32p_centralizerBound031_point_block05 t
  · exact g32p_centralizerBound031_point_block06 t
  · exact g32p_centralizerBound031_point_block07 t
  · exact g32p_centralizerBound031_point_block08 t
  · exact g32p_centralizerBound031_point_block09 t
  · exact g32p_centralizerBound031_point_block10 t
  · exact g32p_centralizerBound031_point_block11 t
  · exact g32p_centralizerBound031_point_block12 t
  · exact g32p_centralizerBound031_point_block13 t
  · exact g32p_centralizerBound031_point_block14 t

theorem g32p_centralizerBound031_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 31) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 31)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound031_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound031_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 31) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 31)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound031_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound031_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 31) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 31)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound031_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound031_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 31) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 31)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound031_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound031_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 31) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 31)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound031_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound031_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 31) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 31) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound031_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 31) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 31)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound031_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound031_stabilizer_block00 t r
  · exact g32p_centralizerBound031_stabilizer_block01 t r
  · exact g32p_centralizerBound031_stabilizer_block02 t r
  · exact g32p_centralizerBound031_stabilizer_block03 t r
  · exact g32p_centralizerBound031_stabilizer_block04 t r

theorem g32p_centralizerBound031_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 31}) ≤ g32p_literalCentralizer 31 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 31 g32p_centralizerBound031_points
    g32p_centralizerBound031_stabilizers ?_ g32p_centralizerBound031_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound031_point_mem i (g32p_centralizer_point_moments 31 x i hi.symm)

end HodgeLean.Foundations.Program

end
end
