import Mathlib
-- PATCH VERSION: 2026-09-02-v29 FINAL-CLEAN-ATTEMPT

-- PATCH VERSION: 2026-09-02-v26 LOCAL-CLOSE-1


/-!
# Ulam 165 — all-in-one formalization file

This file is the mechanically integrated single-file version of the current
Ulam165 formalization sources.  Internal `import Ulam165.*` dependencies have
been removed and the components are ordered topologically.

Current source components, in order:
1. Basic
2. Anchors
3. ModuleGeometry
4. ModuleMinimization
5. State
6. CanonicalFrame
7. FreshArithmetic
8. Initial
9. FreshModule
10. FreshLocal

Important verification note: integration into one file does not by itself
certify compilation.  The file must still be checked with Lean/mathlib, and
the final infinite dense construction/main theorem remain separate completion
goals if they are not present below.
-/

noncomputable section



/-! ==========================================================================
## Component: Basic
========================================================================== -/

open scoped BigOperators Topology
open Set Filter

namespace Ulam165

/-- We split R^(d+1) into an equatorial R^d coordinate and the last coordinate. -/
abbrev Ambient (d : ℕ) := (Fin d → ℝ) × ℝ

/-- Squared Euclidean norm in the split coordinates. -/
def normSq {d : ℕ} (x : Ambient d) : ℝ :=
  (∑ i, (x.1 i) ^ 2) + x.2 ^ 2

/-- The chordal unit sphere. -/
def Sphere (d : ℕ) := {x : Ambient d // normSq x = 1}

instance (d : ℕ) : Coe (Sphere d) (Ambient d) := ⟨Subtype.val⟩

/-- The sphere carries the induced Euclidean metric/topology. -/
instance (d : ℕ) : MetricSpace (Sphere d) := by
  unfold Sphere
  infer_instance

instance (d : ℕ) : SecondCountableTopology (Sphere d) := by
  unfold Sphere
  infer_instance

namespace Sphere

variable {d : ℕ}

@[ext]
theorem ext {x y : Sphere d} (hhead : x.1.1 = y.1.1) (hlast : x.1.2 = y.1.2) : x = y := by
  apply Subtype.ext
  exact Prod.ext hhead hlast

/-- Euclidean inner product in split coordinates. -/
def dot (x y : Sphere d) : ℝ :=
  (∑ i, x.1.1 i * y.1.1 i) + x.1.2 * y.1.2

/-- Squared chordal distance. We use squared distances throughout the finite
    Lipschitz bookkeeping, taking square roots only in the greedy objective. -/
def distSq (x y : Sphere d) : ℝ :=
  (∑ i, (x.1.1 i - y.1.1 i) ^ 2) + (x.1.2 - y.1.2) ^ 2

/-- Chordal distance. -/
def chordDist (x y : Sphere d) : ℝ := Real.sqrt (distSq x y)

lemma normSq_val (x : Sphere d) :
    (∑ i, (x.1.1 i) ^ 2) + x.1.2 ^ 2 = 1 := x.2

lemma dot_self (x : Sphere d) : dot x x = 1 := by
  unfold dot
  have hsum : (∑ i, x.1.1 i * x.1.1 i) = ∑ i, (x.1.1 i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  have hlast : x.1.2 * x.1.2 = x.1.2 ^ 2 := by ring
  rw [hlast]
  exact normSq_val x

lemma distSq_eq_two_sub_two_dot (x y : Sphere d) :
    distSq x y = 2 - 2 * dot x y := by
  have hx : (∑ i, (x.1.1 i) ^ 2) + x.1.2 ^ 2 = 1 := normSq_val x
  have hy : (∑ i, (y.1.1 i) ^ 2) + y.1.2 ^ 2 = 1 := normSq_val y
  have hsum :
      (∑ i, (x.1.1 i - y.1.1 i) ^ 2) =
        (∑ i, (x.1.1 i) ^ 2) -
          2 * (∑ i, x.1.1 i * y.1.1 i) +
            (∑ i, (y.1.1 i) ^ 2) := by
    calc
      (∑ i, (x.1.1 i - y.1.1 i) ^ 2) =
          ∑ i, ((x.1.1 i) ^ 2 - 2 * (x.1.1 i * y.1.1 i) + (y.1.1 i) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i, ((x.1.1 i) ^ 2 - 2 * (x.1.1 i * y.1.1 i))) +
            (∑ i, (y.1.1 i) ^ 2) := by
            rw [Finset.sum_add_distrib]
      _ = ((∑ i, (x.1.1 i) ^ 2) - (∑ i, 2 * (x.1.1 i * y.1.1 i))) +
            (∑ i, (y.1.1 i) ^ 2) := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ i, (x.1.1 i) ^ 2) -
            2 * (∑ i, x.1.1 i * y.1.1 i) +
              (∑ i, (y.1.1 i) ^ 2) := by
            rw [Finset.mul_sum]
  rw [distSq, dot, hsum]
  nlinarith

lemma distSq_nonneg (x y : Sphere d) : 0 ≤ distSq x y := by
  unfold distSq
  positivity

lemma distSq_comm (x y : Sphere d) : distSq x y = distSq y x := by
  unfold distSq
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    ring
  · ring

lemma distSq_self (x : Sphere d) : distSq x x = 0 := by
  simp [distSq]

lemma distSq_eq_zero_iff (x y : Sphere d) : distSq x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hsum : (∑ i, (x.1.1 i - y.1.1 i) ^ 2) = 0 := by
      have h1 : 0 ≤ (∑ i, (x.1.1 i - y.1.1 i) ^ 2) := by positivity
      have h2 : 0 ≤ (x.1.2 - y.1.2) ^ 2 := sq_nonneg _
      unfold distSq at h
      nlinarith
    have hlastsq : (x.1.2 - y.1.2) ^ 2 = 0 := by
      have h1 : 0 ≤ (∑ i, (x.1.1 i - y.1.1 i) ^ 2) := by positivity
      have h2 : 0 ≤ (x.1.2 - y.1.2) ^ 2 := sq_nonneg _
      unfold distSq at h
      nlinarith
    have hlast : x.1.2 = y.1.2 := by nlinarith
    have hcoord : ∀ i, x.1.1 i = y.1.1 i := by
      intro i
      have hi : (x.1.1 i - y.1.1 i) ^ 2 ≤
          ∑ j, (x.1.1 j - y.1.1 j) ^ 2 := by
        exact Finset.single_le_sum (fun j _ => sq_nonneg (x.1.1 j - y.1.1 j)) (Finset.mem_univ i)
      have : (x.1.1 i - y.1.1 i) ^ 2 = 0 := by nlinarith [hsum]
      nlinarith
    apply Sphere.ext
    · funext i
      exact hcoord i
    · exact hlast
  · rintro rfl
    exact distSq_self x

lemma distSq_pos {x y : Sphere d} (hxy : x ≠ y) : 0 < distSq x y := by
  have hn := distSq_nonneg x y
  exact lt_of_le_of_ne hn (Ne.symm (mt (distSq_eq_zero_iff x y).mp hxy))

lemma chordDist_nonneg (x y : Sphere d) : 0 ≤ chordDist x y := Real.sqrt_nonneg _

lemma chordDist_sq (x y : Sphere d) : (chordDist x y) ^ 2 = distSq x y := by
  unfold chordDist
  simpa using Real.sq_sqrt (distSq_nonneg x y)

lemma chordDist_eq_zero_iff (x y : Sphere d) : chordDist x y = 0 ↔ x = y := by
  rw [chordDist, Real.sqrt_eq_zero (distSq_nonneg x y), distSq_eq_zero_iff]

/-- Reflection in the equator. -/
def reflect (x : Sphere d) : Sphere d :=
  ⟨(x.1.1, -x.1.2), by
    simpa [normSq] using x.2⟩

@[simp] lemma reflect_head (x : Sphere d) : (reflect x).1.1 = x.1.1 := rfl
@[simp] lemma reflect_last (x : Sphere d) : (reflect x).1.2 = -x.1.2 := rfl
@[simp] lemma reflect_reflect (x : Sphere d) : reflect (reflect x) = x := by
  ext <;> simp [reflect]

/-- Ulam's fold into the closed northern hemisphere. -/
def fold (x : Sphere d) : Sphere d :=
  ⟨(x.1.1, |x.1.2|), by
    simpa [normSq, sq_abs] using x.2⟩

@[simp] lemma fold_head (x : Sphere d) : (fold x).1.1 = x.1.1 := rfl
@[simp] lemma fold_last (x : Sphere d) : (fold x).1.2 = |x.1.2| := rfl

lemma fold_eq_self_of_nonneg {x : Sphere d} (hx : 0 ≤ x.1.2) : fold x = x := by
  ext
  · rfl
  · simp [fold, abs_of_nonneg hx]

lemma fold_reflect (x : Sphere d) : fold (reflect x) = fold x := by
  ext
  · rfl
  · simp [fold, reflect, abs_neg]

lemma fold_distSq_le (x y : Sphere d) : distSq (fold x) (fold y) ≤ distSq x y := by
  unfold distSq fold
  simp only
  have habs : abs (abs x.1.2 - abs y.1.2) ≤ abs (x.1.2 - y.1.2) := by
    apply abs_le.2
    constructor
    · have hrev := abs_sub_abs_le_abs_sub y.1.2 x.1.2
      have hs : abs (y.1.2 - x.1.2) = abs (x.1.2 - y.1.2) := by
        rw [abs_sub_comm]
      rw [hs] at hrev
      nlinarith
    · exact abs_sub_abs_le_abs_sub _ _
  have hsq : (abs x.1.2 - abs y.1.2) ^ 2 ≤ (x.1.2 - y.1.2) ^ 2 := by
    have h1 : 0 ≤ abs (abs x.1.2 - abs y.1.2) := abs_nonneg _
    have h2 : 0 ≤ abs (x.1.2 - y.1.2) := abs_nonneg _
    have hs1 : (abs (abs x.1.2 - abs y.1.2)) ^ 2 =
        (abs x.1.2 - abs y.1.2) ^ 2 := by
      rw [sq_abs]
    have hs2 : (abs (x.1.2 - y.1.2)) ^ 2 = (x.1.2 - y.1.2) ^ 2 := by
      rw [sq_abs]
    nlinarith
  nlinarith

lemma fold_fiber_iff (x y : Sphere d) : fold x = fold y ↔ y = x ∨ y = reflect x := by
  constructor
  · intro h
    have hh : y.1.1 = x.1.1 := by
      have := congrArg (fun z : Sphere d => z.1.1) h
      simpa [fold] using this.symm
    have hl : |y.1.2| = |x.1.2| := by
      have := congrArg (fun z : Sphere d => z.1.2) h
      simpa [fold] using this.symm
    have hs : y.1.2 = x.1.2 ∨ y.1.2 = -x.1.2 := (abs_eq_abs.mp hl)
    rcases hs with hs | hs
    · left
      apply Sphere.ext hh hs
    · right
      apply Sphere.ext
      · simpa [reflect] using hh
      · simpa [reflect] using hs
  · rintro (rfl | rfl)
    · rfl
    · exact (fold_reflect x).symm

/-- A point has rational coordinates. -/
def RationalPoint (x : Sphere d) : Prop :=
  (∀ i, ∃ q : ℚ, x.1.1 i = (q : ℝ)) ∧ ∃ q : ℚ, x.1.2 = (q : ℝ)

lemma rational_reflect {x : Sphere d} (hx : RationalPoint x) : RationalPoint (reflect x) := by
  rcases hx with ⟨hh, ⟨q, hq⟩⟩
  constructor
  · simpa [reflect] using hh
  · refine ⟨-q, ?_⟩
    simp [reflect, hq]

lemma rational_fold {x : Sphere d} (hx : RationalPoint x) : RationalPoint (fold x) := by
  rcases hx with ⟨hh, ⟨q, hq⟩⟩
  constructor
  · simpa [fold] using hh
  · refine ⟨|q|, ?_⟩
    simp [fold, hq]

end Sphere

open Sphere

/-- Maximum of a finite list of nonnegative quantities, with default 0. -/
def listMax : List ℝ → ℝ
  | [] => 0
  | x :: xs => max x (listMax xs)

lemma listMax_nonneg (xs : List ℝ) : 0 ≤ listMax xs := by
  induction xs with
  | nil => simp [listMax]
  | cons x xs ih => simp [listMax, le_max_of_le_right ih]

lemma le_listMax_of_mem {x : ℝ} {xs : List ℝ} (hx : x ∈ xs) : x ≤ listMax xs := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (ih hx) (le_max_right _ _)

lemma listMax_le {xs : List ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ xs, x ≤ C) : listMax xs ≤ C := by
  induction xs with
  | nil => simpa [listMax] using hC
  | cons a xs ih =>
      simp only [listMax]
      apply max_le
      · exact h a (by simp)
      · apply ih
        intro x hx
        exact h x (by simp [hx])

lemma listMax_eq_of_mem_of_bound {xs : List ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmem : C ∈ xs) (h : ∀ x ∈ xs, x ≤ C) : listMax xs = C := by
  apply le_antisymm
  · exact listMax_le hC h
  · exact le_listMax_of_mem hmem

/-- List of all ordered squared Lipschitz ratios of a finite graph. Diagonal
    ratios are harmless because division by zero in a field is 0. -/
def ratioList {d : ℕ} (g : List (Sphere d × Sphere d)) : List ℝ :=
  g.flatMap fun a => g.map fun b => distSq a.2 b.2 / distSq a.1 b.1

/-- Squared forward Lipschitz constant of a finite graph. -/
def forwardLipSq {d : ℕ} (g : List (Sphere d × Sphere d)) : ℝ :=
  listMax (ratioList g)

/-- Squared inverse Lipschitz constant. -/
def inverseLipSq {d : ℕ} (g : List (Sphere d × Sphere d)) : ℝ :=
  forwardLipSq (g.map Prod.swap)

/-- Ulam objective, expressed via squared finite Lipschitz constants. -/
def greedyCost {d : ℕ} (g : List (Sphere d × Sphere d)) : ℝ :=
  Real.sqrt (forwardLipSq g) + Real.sqrt (inverseLipSq g)

lemma ratio_mem_ratioList {d : ℕ} {g : List (Sphere d × Sphere d)}
    {a b : Sphere d × Sphere d} (ha : a ∈ g) (hb : b ∈ g) :
    distSq a.2 b.2 / distSq a.1 b.1 ∈ ratioList g := by
  unfold ratioList
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, ?_⟩
  exact List.mem_map.mpr ⟨b, hb, rfl⟩

lemma ratio_le_forwardLipSq {d : ℕ} {g : List (Sphere d × Sphere d)}
    {a b : Sphere d × Sphere d} (ha : a ∈ g) (hb : b ∈ g) :
    distSq a.2 b.2 / distSq a.1 b.1 ≤ forwardLipSq g := by
  exact le_listMax_of_mem (ratio_mem_ratioList ha hb)

lemma inverse_ratio_le_inverseLipSq {d : ℕ} {g : List (Sphere d × Sphere d)}
    {a b : Sphere d × Sphere d} (ha : a ∈ g) (hb : b ∈ g) :
    distSq a.1 b.1 / distSq a.2 b.2 ≤ inverseLipSq g := by
  unfold inverseLipSq forwardLipSq
  apply le_listMax_of_mem
  unfold ratioList
  apply List.mem_flatMap.mpr
  refine ⟨a.swap, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨a, ha, rfl⟩
  · apply List.mem_map.mpr
    exact ⟨b.swap, List.mem_map.mpr ⟨b, hb, rfl⟩, by rfl⟩

lemma forwardLipSq_nonneg {d : ℕ} (g : List (Sphere d × Sphere d)) :
    0 ≤ forwardLipSq g := listMax_nonneg _

lemma inverseLipSq_nonneg {d : ℕ} (g : List (Sphere d × Sphere d)) :
    0 ≤ inverseLipSq g := forwardLipSq_nonneg _

/-- Graph of the fold on a finite ordered source list. -/
def foldGraph {d : ℕ} (src : List (Sphere d)) : List (Sphere d × Sphere d) :=
  src.map fun p => (p, fold p)

/-- Add a candidate image for a new source to the current fold graph. -/
def candidateGraph {d : ℕ} (src : List (Sphere d)) (x y : Sphere d) :
    List (Sphere d × Sphere d) := foldGraph src ++ [(x,y)]

lemma foldGraph_mem {d : ℕ} {src : List (Sphere d)} {p : Sphere d} (hp : p ∈ src) :
    (p, fold p) ∈ foldGraph src := by
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

lemma candidate_old_mem {d : ℕ} {src : List (Sphere d)} {x y p : Sphere d}
    (hp : p ∈ src) : (p, fold p) ∈ candidateGraph src x y := by
  simp [candidateGraph, foldGraph_mem hp]

lemma candidate_new_mem {d : ℕ} (src : List (Sphere d)) (x y : Sphere d) :
    (x,y) ∈ candidateGraph src x y := by
  simp [candidateGraph]

lemma forwardLipSq_le_of_bound {d : ℕ} {g : List (Sphere d × Sphere d)} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ a ∈ g, ∀ b ∈ g,
      distSq a.2 b.2 / distSq a.1 b.1 ≤ C) :
    forwardLipSq g ≤ C := by
  unfold forwardLipSq
  apply listMax_le hC
  intro r hr
  unfold ratioList at hr
  rcases List.mem_flatMap.mp hr with ⟨a, ha, hr⟩
  rcases List.mem_map.mp hr with ⟨b, hb, rfl⟩
  exact h a ha b hb

lemma inverseLipSq_le_of_bound {d : ℕ} {g : List (Sphere d × Sphere d)} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ a ∈ g, ∀ b ∈ g,
      distSq a.1 b.1 / distSq a.2 b.2 ≤ C) :
    inverseLipSq g ≤ C := by
  unfold inverseLipSq
  apply forwardLipSq_le_of_bound hC
  intro a ha b hb
  rcases List.mem_map.mp ha with ⟨a0, ha0, rfl⟩
  rcases List.mem_map.mp hb with ⟨b0, hb0, rfl⟩
  simpa using h a0 ha0 b0 hb0

lemma forwardLipSq_eq_of_bound_witness {d : ℕ} {g : List (Sphere d × Sphere d)} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ a ∈ g, ∀ b ∈ g,
      distSq a.2 b.2 / distSq a.1 b.1 ≤ C)
    {a b : Sphere d × Sphere d} (ha : a ∈ g) (hb : b ∈ g)
    (hw : distSq a.2 b.2 / distSq a.1 b.1 = C) :
    forwardLipSq g = C := by
  apply le_antisymm
  · exact forwardLipSq_le_of_bound hC h
  · rw [← hw]
    exact ratio_le_forwardLipSq ha hb

lemma inverseLipSq_eq_of_bound_witness {d : ℕ} {g : List (Sphere d × Sphere d)} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ a ∈ g, ∀ b ∈ g,
      distSq a.1 b.1 / distSq a.2 b.2 ≤ C)
    {a b : Sphere d × Sphere d} (ha : a ∈ g) (hb : b ∈ g)
    (hw : distSq a.1 b.1 / distSq a.2 b.2 = C) :
    inverseLipSq g = C := by
  apply le_antisymm
  · exact inverseLipSq_le_of_bound hC h
  · rw [← hw]
    exact inverse_ratio_le_inverseLipSq ha hb


end Ulam165


/-! ==========================================================================
## Component: Anchors
========================================================================== -/

open scoped BigOperators
open Set

namespace Ulam165
open Sphere

variable {d : ℕ}

/-- Positive equatorial coordinate vector. -/
def epos (i : Fin d) : Sphere d :=
  ⟨(fun j => if j = i then 1 else 0, 0), by
    simp [normSq]⟩

/-- Negative equatorial coordinate vector. -/
def eneg (i : Fin d) : Sphere d :=
  ⟨(fun j => if j = i then -1 else 0, 0), by
    simp [normSq]⟩

/-- North pole. -/
def north (d : ℕ) : Sphere d :=
  ⟨(fun _ => 0, 1), by simp [normSq]⟩

/-- South pole. -/
def south (d : ℕ) : Sphere d :=
  ⟨(fun _ => 0, -1), by simp [normSq]⟩

@[simp] lemma fold_epos (i : Fin d) : fold (epos i) = epos i := by
  apply fold_eq_self_of_nonneg
  simp [epos]

@[simp] lemma fold_eneg (i : Fin d) : fold (eneg i) = eneg i := by
  apply fold_eq_self_of_nonneg
  simp [eneg]

@[simp] lemma fold_south : fold (south d) = north d := by
  ext <;> simp [fold, south, north]

@[simp] lemma fold_north : fold (north d) = north d := by
  apply fold_eq_self_of_nonneg
  simp [north]

/-- The rational northern anchor a=(20/101)e_1+(99/101)e_{d+1}. -/
def anchorA (i : Fin d) : Sphere d :=
  ⟨(fun j => if j = i then (20 : ℝ) / 101 else 0, (99 : ℝ) / 101), by
    simp [normSq]
    norm_num⟩

@[simp] lemma anchorA_last (i : Fin d) : (anchorA i).1.2 = (99 : ℝ) / 101 := rfl

@[simp] lemma fold_anchorA (i : Fin d) : fold (anchorA i) = anchorA i := by
  apply fold_eq_self_of_nonneg
  simp [anchorA]
  norm_num

lemma rational_epos (i : Fin d) : RationalPoint (epos i) := by
  constructor
  · intro j
    by_cases h : j = i
    · subst h; exact ⟨1, by simp [epos]⟩
    · exact ⟨0, by simp [epos, h]⟩
  · exact ⟨0, by simp [epos]⟩

lemma rational_eneg (i : Fin d) : RationalPoint (eneg i) := by
  constructor
  · intro j
    by_cases h : j = i
    · subst h; exact ⟨-1, by simp [eneg]⟩
    · exact ⟨0, by simp [eneg, h]⟩
  · exact ⟨0, by simp [eneg]⟩

lemma rational_south : RationalPoint (south d) := by
  constructor
  · intro i; exact ⟨0, by simp [south]⟩
  · exact ⟨-1, by simp [south]⟩

lemma rational_north : RationalPoint (north d) := by
  constructor
  · intro i; exact ⟨0, by simp [north]⟩
  · exact ⟨1, by simp [north]⟩

lemma rational_anchorA (i : Fin d) : RationalPoint (anchorA i) := by
  constructor
  · intro j
    by_cases h : j = i
    · subst h
      exact ⟨20/101, by norm_num [anchorA]⟩
    · exact ⟨0, by simp [anchorA, h]⟩
  · exact ⟨99/101, by norm_num [anchorA]⟩

lemma dot_epos (x : Sphere d) (i : Fin d) : dot x (epos i) = x.1.1 i := by
  simp [dot, epos]

lemma dot_eneg (x : Sphere d) (i : Fin d) : dot x (eneg i) = -x.1.1 i := by
  simp [dot, eneg]

lemma dot_north (x : Sphere d) : dot x (north d) = x.1.2 := by
  simp [dot, north]

lemma dot_south (x : Sphere d) : dot x (south d) = -x.1.2 := by
  simp [dot, south]

lemma distSq_epos (x : Sphere d) (i : Fin d) :
    distSq x (epos i) = 2 - 2 * x.1.1 i := by
  rw [distSq_eq_two_sub_two_dot, dot_epos]

lemma distSq_eneg (x : Sphere d) (i : Fin d) :
    distSq x (eneg i) = 2 + 2 * x.1.1 i := by
  rw [distSq_eq_two_sub_two_dot, dot_eneg]
  ring

lemma distSq_north (x : Sphere d) :
    distSq x (north d) = 2 - 2 * x.1.2 := by
  rw [distSq_eq_two_sub_two_dot, dot_north]

lemma distSq_south (x : Sphere d) :
    distSq x (south d) = 2 + 2 * x.1.2 := by
  rw [distSq_eq_two_sub_two_dot, dot_south]
  ring

lemma dot_anchorA (x : Sphere d) (i : Fin d) :
    dot x (anchorA i) = ((20 : ℝ) / 101) * x.1.1 i + ((99 : ℝ) / 101) * x.1.2 := by
  simp [dot, anchorA]
  ring

lemma distSq_reflect_anchorA_sub (x : Sphere d) (i : Fin d) :
    distSq (reflect x) (anchorA i) - distSq x (anchorA i) =
      4 * x.1.2 * ((99 : ℝ) / 101) := by
  rw [distSq_eq_two_sub_two_dot, distSq_eq_two_sub_two_dot]
  rw [dot_anchorA, dot_anchorA]
  simp [reflect]
  ring

/-- Coordinate pinning: if a candidate image respects all forward 1-Lipschitz
    inequalities against the finite anchor set, it is exactly the fold image. -/
theorem fold_pinning (i0 : Fin d) (x y : Sphere d)
    (hpos : ∀ i : Fin d, distSq y (epos i) ≤ distSq x (epos i))
    (hneg : ∀ i : Fin d, distSq y (eneg i) ≤ distSq x (eneg i))
    (hsouth : distSq y (north d) ≤ distSq x (south d))
    (ha : distSq y (anchorA i0) ≤ distSq x (anchorA i0)) :
    y = fold x := by
  have hhead : y.1.1 = x.1.1 := by
    funext i
    have hp := hpos i
    have hn := hneg i
    rw [distSq_epos, distSq_epos] at hp
    rw [distSq_eneg, distSq_eneg] at hn
    nlinarith
  have hsq : y.1.2 ^ 2 = x.1.2 ^ 2 := by
    have hy := y.2
    have hx := x.2
    simp only [normSq] at hy hx
    rw [hhead] at hy
    nlinarith
  by_cases hxneg : x.1.2 < 0
  · have hs := hsouth
    rw [distSq_north, distSq_south] at hs
    have hylast : y.1.2 = -x.1.2 := by
      nlinarith
    apply Sphere.ext
    · simpa [fold] using hhead
    · simp [fold, abs_of_neg hxneg, hylast]
  · have hxnonneg : 0 ≤ x.1.2 := le_of_not_gt hxneg
    by_cases hxzero : x.1.2 = 0
    · have hyzero : y.1.2 = 0 := by nlinarith
      apply Sphere.ext
      · simpa [fold] using hhead
      · simp [fold, hxzero, hyzero]
    · have hxpos : 0 < x.1.2 := lt_of_le_of_ne hxnonneg (Ne.symm hxzero)
      by_cases hyneg : y.1.2 < 0
      · have hylast : y.1.2 = -x.1.2 := by nlinarith
        have href : y = reflect x := by
          apply Sphere.ext
          · simpa [reflect] using hhead
          · simp [reflect, hylast]
        have hdiff := distSq_reflect_anchorA_sub x i0
        have ha' := ha
        rw [href] at ha'
        have hapos : 0 < (99 : ℝ) / 101 := by norm_num
        nlinarith
      · have hynonneg : 0 ≤ y.1.2 := le_of_not_gt hyneg
        have hylast : y.1.2 = x.1.2 := by nlinarith
        apply Sphere.ext
        · simpa [fold] using hhead
        · simp [fold, abs_of_nonneg hxnonneg, hylast]

/-- The squared inverse ratio of the exceptional initial pair S,a is 100. -/
lemma south_anchorA_inverse_ratio (i0 : Fin d) :
    distSq (south d) (anchorA i0) / distSq (north d) (anchorA i0) = 100 := by
  rw [distSq_comm (south d) (anchorA i0), distSq_comm (north d) (anchorA i0)]
  rw [distSq_south, distSq_north]
  simp [anchorA]
  norm_num

/-- A convenient ordered initial source list. -/
def anchorSources (d : ℕ) (i0 : Fin d) : List (Sphere d) :=
  (List.ofFn fun i : Fin d => epos i) ++
  (List.ofFn fun i : Fin d => eneg i) ++
  [south d, anchorA i0]

lemma epos_mem_anchorSources (i0 i : Fin d) : epos i ∈ anchorSources d i0 := by
  simp [anchorSources]

lemma eneg_mem_anchorSources (i0 i : Fin d) : eneg i ∈ anchorSources d i0 := by
  simp [anchorSources]

lemma south_mem_anchorSources (i0 : Fin d) : south d ∈ anchorSources d i0 := by
  simp [anchorSources]

lemma anchorA_mem_anchorSources (i0 : Fin d) : anchorA i0 ∈ anchorSources d i0 := by
  simp [anchorSources]

end Ulam165


/-! ==========================================================================
## Component: ModuleGeometry
========================================================================== -/

open scoped BigOperators
open Set

namespace Ulam165
open Sphere

variable {d : ℕ}

/-- An orthonormal equatorial 2-frame. -/
structure EqFrame (d : ℕ) where
  z : Fin d → ℝ
  v : Fin d → ℝ
  z_norm : ∑ i, z i ^ 2 = 1
  v_norm : ∑ i, v i ^ 2 = 1
  zv_orth : ∑ i, z i * v i = 0

namespace EqFrame

lemma vz_orth (E : EqFrame d) : ∑ i, E.v i * E.z i = 0 := by
  calc
    (∑ i, E.v i * E.z i) = ∑ i, E.z i * E.v i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := E.zv_orth

lemma sum_z_z (E : EqFrame d) (a b : ℝ) :
    (∑ i, (a * E.z i) * (b * E.z i)) = a * b := by
  calc
    (∑ i, (a * E.z i) * (b * E.z i)) =
        (a * b) * ∑ i, E.z i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = a * b := by rw [E.z_norm, mul_one]

lemma sum_z_v (E : EqFrame d) (a b : ℝ) :
    (∑ i, (a * E.z i) * (b * E.v i)) = 0 := by
  calc
    (∑ i, (a * E.z i) * (b * E.v i)) =
        (a * b) * ∑ i, E.z i * E.v i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := by rw [E.zv_orth, mul_zero]

lemma norm_z_smul (E : EqFrame d) (a : ℝ) :
    ∑ i, (a * E.z i) ^ 2 = a ^ 2 := by
  calc
    (∑ i, (a * E.z i) ^ 2) = a ^ 2 * ∑ i, E.z i ^ 2 := by
      simp_rw [mul_pow]
      rw [← Finset.mul_sum]
    _ = a ^ 2 := by rw [E.z_norm, mul_one]

lemma norm_v_smul (E : EqFrame d) (a : ℝ) :
    ∑ i, (a * E.v i) ^ 2 = a ^ 2 := by
  calc
    (∑ i, (a * E.v i) ^ 2) = a ^ 2 * ∑ i, E.v i ^ 2 := by
      simp_rw [mul_pow]
      rw [← Finset.mul_sum]
    _ = a ^ 2 := by rw [E.v_norm, mul_one]

lemma norm_lincomb (E : EqFrame d) (a b : ℝ) :
    ∑ i, (a * E.z i + b * E.v i) ^ 2 = a ^ 2 + b ^ 2 := by
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [E.norm_z_smul, E.norm_v_smul]
  have hcross : ∑ i, 2 * (a * E.z i) * (b * E.v i) = 0 := by
    calc
      (∑ i, 2 * (a * E.z i) * (b * E.v i)) =
          (2*a*b) * ∑ i, E.z i * E.v i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 0 := by rw [E.zv_orth, mul_zero]
  rw [hcross, add_zero]

/-- Equatorial frame center. -/
def zeta (E : EqFrame d) : Sphere d :=
  ⟨(E.z, 0), by simp [normSq, E.z_norm]⟩

@[simp] lemma zeta_head (E : EqFrame d) : (E.zeta).1.1 = E.z := rfl
@[simp] lemma zeta_last (E : EqFrame d) : (E.zeta).1.2 = 0 := rfl

end EqFrame

/-- Scalar data for the spherical five-point module. The three identities say
    that (t,h), (ca,sa), and (cb,sb) lie on the unit circle. -/
structure ModuleScalars where
  t : ℝ
  h : ℝ
  ca : ℝ
  sa : ℝ
  cb : ℝ
  sb : ℝ
  th_unit : t^2 + h^2 = 1
  a_unit : ca^2 + sa^2 = 1
  b_unit : cb^2 + sb^2 = 1

namespace ModuleScalars

variable (E : EqFrame d) (s : ModuleScalars)

/-- Center y0. -/
def center : Sphere d :=
  ⟨(fun i => s.t * E.z i, s.h), by
    rw [normSq, E.norm_z_smul]
    exact s.th_unit⟩

/-- Upper pin P_+. -/
def pinPlus : Sphere d :=
  ⟨(fun i => (s.ca*s.t - s.sa*s.h) * E.z i,
      s.ca*s.h + s.sa*s.t), by
    rw [normSq, E.norm_z_smul]
    nlinarith [s.th_unit, s.a_unit]⟩

/-- Upper pin P_-. -/
def pinMinus : Sphere d :=
  ⟨(fun i => (s.ca*s.t + s.sa*s.h) * E.z i,
      s.ca*s.h - s.sa*s.t), by
    rw [normSq, E.norm_z_smul]
    nlinarith [s.th_unit, s.a_unit]⟩

/-- Guard target G_+. -/
def guardPlus : Sphere d :=
  ⟨(fun i => (s.cb*s.t) * E.z i + s.sb * E.v i, s.cb*s.h), by
    rw [normSq, E.norm_lincomb]
    nlinarith [s.th_unit, s.b_unit]⟩

/-- Guard target G_-. -/
def guardMinus : Sphere d :=
  ⟨(fun i => (s.cb*s.t) * E.z i - s.sb * E.v i, s.cb*s.h), by
    have hnorm : ∑ i, ((s.cb*s.t) * E.z i - s.sb * E.v i) ^ 2 =
        (s.cb*s.t)^2 + s.sb^2 := by
      simpa [sub_eq_add_neg] using E.norm_lincomb (s.cb*s.t) (-s.sb)
    rw [normSq, hnorm]
    nlinarith [s.th_unit, s.b_unit]⟩

/-- Guard source JG_+. -/
def guardSourcePlus : Sphere d := reflect (s.guardPlus E)

/-- Guard source JG_-. -/
def guardSourceMinus : Sphere d := reflect (s.guardMinus E)

@[simp] lemma center_head : (s.center E).1.1 = fun i => s.t * E.z i := rfl
@[simp] lemma center_last : (s.center E).1.2 = s.h := rfl
@[simp] lemma pinPlus_last : (s.pinPlus E).1.2 = s.ca*s.h + s.sa*s.t := rfl
@[simp] lemma pinMinus_last : (s.pinMinus E).1.2 = s.ca*s.h - s.sa*s.t := rfl
@[simp] lemma guardPlus_last : (s.guardPlus E).1.2 = s.cb*s.h := rfl
@[simp] lemma guardMinus_last : (s.guardMinus E).1.2 = s.cb*s.h := rfl

lemma dot_center_pinPlus : dot (s.center E) (s.pinPlus E) = s.ca := by
  unfold dot center pinPlus
  rw [E.sum_z_z]
  change s.t * (s.ca*s.t - s.sa*s.h) +
      s.h * (s.ca*s.h + s.sa*s.t) = s.ca
  calc
    _ = s.ca * (s.t^2 + s.h^2) := by ring
    _ = s.ca := by rw [s.th_unit]; ring

lemma dot_center_pinMinus : dot (s.center E) (s.pinMinus E) = s.ca := by
  unfold dot center pinMinus
  rw [E.sum_z_z]
  change s.t * (s.ca*s.t + s.sa*s.h) +
      s.h * (s.ca*s.h - s.sa*s.t) = s.ca
  calc
    _ = s.ca * (s.t^2 + s.h^2) := by ring
    _ = s.ca := by rw [s.th_unit]; ring

lemma dot_center_guardPlus : dot (s.center E) (s.guardPlus E) = s.cb := by
  unfold dot center guardPlus
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, E.sum_z_z, E.sum_z_v]
  change s.t * (s.cb*s.t) + 0 + s.h * (s.cb*s.h) = s.cb
  calc
    _ = s.cb * (s.t^2 + s.h^2) := by ring
    _ = s.cb := by rw [s.th_unit]; ring

lemma dot_center_guardMinus : dot (s.center E) (s.guardMinus E) = s.cb := by
  unfold dot center guardMinus
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, E.sum_z_z, E.sum_z_v]
  change s.t * (s.cb*s.t) - 0 + s.h * (s.cb*s.h) = s.cb
  calc
    _ = s.cb * (s.t^2 + s.h^2) := by ring
    _ = s.cb := by rw [s.th_unit]; ring

lemma center_pinPlus_distSq : distSq (s.center E) (s.pinPlus E) = 2 - 2*s.ca := by
  rw [distSq_eq_two_sub_two_dot, s.dot_center_pinPlus E]

lemma center_pinMinus_distSq : distSq (s.center E) (s.pinMinus E) = 2 - 2*s.ca := by
  rw [distSq_eq_two_sub_two_dot, s.dot_center_pinMinus E]

lemma center_guardPlus_distSq : distSq (s.center E) (s.guardPlus E) = 2 - 2*s.cb := by
  rw [distSq_eq_two_sub_two_dot, s.dot_center_guardPlus E]

lemma center_guardMinus_distSq : distSq (s.center E) (s.guardMinus E) = 2 - 2*s.cb := by
  rw [distSq_eq_two_sub_two_dot, s.dot_center_guardMinus E]

lemma center_guardSourcePlus_distSq :
    distSq (s.center E) (s.guardSourcePlus E) =
      (2 - 2*s.cb) + 4*s.h^2*s.cb := by
  rw [distSq_eq_two_sub_two_dot]
  unfold dot guardSourcePlus reflect guardPlus center
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, E.sum_z_z, E.sum_z_v]
  calc
    _ = 2 - 2*s.cb*(s.t^2 - s.h^2) := by ring
    _ = (2 - 2*s.cb) + 4*s.h^2*s.cb := by
      rw [show s.t^2 = 1 - s.h^2 by nlinarith [s.th_unit]]
      ring_nf

lemma center_guardSourceMinus_distSq :
    distSq (s.center E) (s.guardSourceMinus E) =
      (2 - 2*s.cb) + 4*s.h^2*s.cb := by
  rw [distSq_eq_two_sub_two_dot]
  unfold dot guardSourceMinus reflect guardMinus center
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, E.sum_z_z, E.sum_z_v]
  calc
    _ = 2 - 2*s.cb*(s.t^2 - s.h^2) := by ring
    _ = (2 - 2*s.cb) + 4*s.h^2*s.cb := by
      rw [show s.t^2 = 1 - s.h^2 by nlinarith [s.th_unit]]
      ring_nf

/-- Sum of the two pin inner products; the tangent terms cancel. -/
lemma dot_pin_sum (y : Sphere d) :
    dot y (s.pinPlus E) + dot y (s.pinMinus E) = 2*s.ca*dot y (s.center E) := by
  unfold dot pinPlus pinMinus center
  change
    ((∑ i, y.1.1 i * ((s.ca*s.t-s.sa*s.h) * E.z i)) +
      y.1.2 * (s.ca*s.h+s.sa*s.t)) +
    ((∑ i, y.1.1 i * ((s.ca*s.t+s.sa*s.h) * E.z i)) +
      y.1.2 * (s.ca*s.h-s.sa*s.t)) =
    2*s.ca * ((∑ i, y.1.1 i * (s.t*E.z i)) + y.1.2*s.h)
  have hsum :
      (∑ i, y.1.1 i * ((s.ca*s.t-s.sa*s.h) * E.z i)) +
        (∑ i, y.1.1 i * ((s.ca*s.t+s.sa*s.h) * E.z i)) =
      2*s.ca * (∑ i, y.1.1 i * (s.t * E.z i)) := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ i, (y.1.1 i * ((s.ca*s.t-s.sa*s.h) * E.z i) +
          y.1.1 i * ((s.ca*s.t+s.sa*s.h) * E.z i))) =
          ∑ i, 2*s.ca * (y.1.1 i * (s.t * E.z i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 2*s.ca * (∑ i, y.1.1 i * (s.t * E.z i)) := by
            rw [Finset.mul_sum]
  linear_combination hsum

/-- Exact averaged pin distance identity. -/
lemma pin_average_distSq (y : Sphere d) :
    (distSq y (s.pinPlus E) + distSq y (s.pinMinus E)) / 2 =
      (2 - 2*s.ca) + s.ca * distSq y (s.center E) := by
  rw [distSq_eq_two_sub_two_dot, distSq_eq_two_sub_two_dot,
      distSq_eq_two_sub_two_dot]
  have hsum := s.dot_pin_sum E y
  nlinarith

lemma dot_guard_sum (y : Sphere d) :
    dot y (s.guardPlus E) + dot y (s.guardMinus E) = 2*s.cb*dot y (s.center E) := by
  unfold dot guardPlus guardMinus center
  change
    ((∑ i, y.1.1 i * (s.cb*s.t*E.z i+s.sb*E.v i)) + y.1.2*(s.cb*s.h)) +
    ((∑ i, y.1.1 i * (s.cb*s.t*E.z i-s.sb*E.v i)) + y.1.2*(s.cb*s.h)) =
    2*s.cb * ((∑ i, y.1.1 i * (s.t*E.z i)) + y.1.2*s.h)
  have hsum :
      (∑ i, y.1.1 i * (s.cb*s.t*E.z i + s.sb*E.v i)) +
        (∑ i, y.1.1 i * (s.cb*s.t*E.z i - s.sb*E.v i)) =
      2*s.cb * (∑ i, y.1.1 i * (s.t * E.z i)) := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ i, (y.1.1 i * (s.cb*s.t*E.z i + s.sb*E.v i) +
          y.1.1 i * (s.cb*s.t*E.z i - s.sb*E.v i))) =
          ∑ i, 2*s.cb * (y.1.1 i * (s.t * E.z i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 2*s.cb * (∑ i, y.1.1 i * (s.t * E.z i)) := by
            rw [Finset.mul_sum]
  linear_combination hsum

/-- Exact averaged guard-target distance identity. -/
lemma guard_average_distSq (y : Sphere d) :
    (distSq y (s.guardPlus E) + distSq y (s.guardMinus E)) / 2 =
      (2 - 2*s.cb) + s.cb * distSq y (s.center E) := by
  rw [distSq_eq_two_sub_two_dot, distSq_eq_two_sub_two_dot,
      distSq_eq_two_sub_two_dot]
  have hsum := s.dot_guard_sum E y
  nlinarith

lemma exists_pin_radial_lower (y : Sphere d) :
    ∃ P ∈ [s.pinPlus E, s.pinMinus E],
      (2 - 2*s.ca) + s.ca * distSq y (s.center E) ≤ distSq y P := by
  let A := distSq y (s.pinPlus E)
  let B := distSq y (s.pinMinus E)
  let R := (2 - 2*s.ca) + s.ca * distSq y (s.center E)
  have havg : (A+B)/2 = R := by simpa [A,B,R] using s.pin_average_distSq E y
  by_cases hAB : A ≤ B
  · refine ⟨s.pinMinus E, by simp, ?_⟩
    nlinarith
  · have hBA : B ≤ A := le_of_not_ge hAB
    refine ⟨s.pinPlus E, by simp, ?_⟩
    nlinarith

lemma exists_guard_radial_upper (y : Sphere d) :
    ∃ G ∈ [s.guardPlus E, s.guardMinus E],
      distSq y G ≤ (2 - 2*s.cb) + s.cb * distSq y (s.center E) := by
  let A := distSq y (s.guardPlus E)
  let B := distSq y (s.guardMinus E)
  let R := (2 - 2*s.cb) + s.cb * distSq y (s.center E)
  have havg : (A+B)/2 = R := by simpa [A,B,R] using s.guard_average_distSq E y
  by_cases hAB : A ≤ B
  · refine ⟨s.guardPlus E, by simp, ?_⟩
    nlinarith
  · have hBA : B ≤ A := le_of_not_ge hAB
    refine ⟨s.guardMinus E, by simp, ?_⟩
    nlinarith

end ModuleScalars

/-- Rational half-angle cosine. -/
def qCos (r : ℚ) : ℚ := (1-r^2)/(1+r^2)
/-- Rational half-angle sine. -/
def qSin (r : ℚ) : ℚ := (2*r)/(1+r^2)

lemma qCos_sq_add_qSin_sq (r : ℚ) : qCos r ^ 2 + qSin r ^ 2 = 1 := by
  unfold qCos qSin
  have h : 1 + r^2 ≠ 0 := by positivity
  field_simp
  ring

/-- Turn three rational half-angle parameters into exact real module scalars. -/
def rationalModuleScalars (s a b : ℚ) : ModuleScalars where
  t := (qCos s : ℚ)
  h := (qSin s : ℚ)
  ca := (qCos a : ℚ)
  sa := (qSin a : ℚ)
  cb := (qCos b : ℚ)
  sb := (qSin b : ℚ)
  th_unit := by exact_mod_cast qCos_sq_add_qSin_sq s
  a_unit := by exact_mod_cast qCos_sq_add_qSin_sq a
  b_unit := by exact_mod_cast qCos_sq_add_qSin_sq b

end Ulam165

namespace Ulam165
open Sphere
namespace ModuleScalars

variable {d : ℕ} (E : EqFrame d) (s : ModuleScalars)

/-- Pins and guard targets are separated by the same distance, independently
of both signs. -/
lemma dot_pinPlus_guardPlus : dot (s.pinPlus E) (s.guardPlus E) = s.ca*s.cb := by
  unfold dot pinPlus guardPlus
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, E.sum_z_z, E.sum_z_v]
  calc
    _ = s.ca*s.cb*(s.t^2+s.h^2) := by ring
    _ = s.ca*s.cb := by rw [s.th_unit]; ring
lemma dot_pinPlus_guardMinus : dot (s.pinPlus E) (s.guardMinus E) = s.ca*s.cb := by
  unfold dot pinPlus guardMinus
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, E.sum_z_z, E.sum_z_v]
  calc
    _ = s.ca*s.cb*(s.t^2+s.h^2) := by ring
    _ = s.ca*s.cb := by rw [s.th_unit]; ring
lemma dot_pinMinus_guardPlus : dot (s.pinMinus E) (s.guardPlus E) = s.ca*s.cb := by
  unfold dot pinMinus guardPlus
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, E.sum_z_z, E.sum_z_v]
  calc
    _ = s.ca*s.cb*(s.t^2+s.h^2) := by ring
    _ = s.ca*s.cb := by rw [s.th_unit]; ring
lemma dot_pinMinus_guardMinus : dot (s.pinMinus E) (s.guardMinus E) = s.ca*s.cb := by
  unfold dot pinMinus guardMinus
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, E.sum_z_z, E.sum_z_v]
  calc
    _ = s.ca*s.cb*(s.t^2+s.h^2) := by ring
    _ = s.ca*s.cb := by rw [s.th_unit]; ring
lemma pinPlus_guardPlus_distSq :
    distSq (s.pinPlus E) (s.guardPlus E) = 2-2*s.ca*s.cb := by
  rw [distSq_eq_two_sub_two_dot, s.dot_pinPlus_guardPlus E]
  ring

lemma pinPlus_guardMinus_distSq :
    distSq (s.pinPlus E) (s.guardMinus E) = 2-2*s.ca*s.cb := by
  rw [distSq_eq_two_sub_two_dot, s.dot_pinPlus_guardMinus E]
  ring

lemma pinMinus_guardPlus_distSq :
    distSq (s.pinMinus E) (s.guardPlus E) = 2-2*s.ca*s.cb := by
  rw [distSq_eq_two_sub_two_dot, s.dot_pinMinus_guardPlus E]
  ring

lemma pinMinus_guardMinus_distSq :
    distSq (s.pinMinus E) (s.guardMinus E) = 2-2*s.ca*s.cb := by
  rw [distSq_eq_two_sub_two_dot, s.dot_pinMinus_guardMinus E]
  ring

/-- The plus pin is the worst pin for inverse interaction with a reflected
    guard. -/
lemma dot_pinPlus_guardSourcePlus :
    dot (s.pinPlus E) (s.guardSourcePlus E) =
      s.cb * (s.ca*(1-2*s.h^2) - 2*s.sa*s.h*s.t) := by
  unfold dot pinPlus guardSourcePlus reflect guardPlus
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, E.sum_z_z, E.sum_z_v]
  linear_combination s.ca * s.cb * s.th_unit

lemma dot_pinPlus_guardSourceMinus :
    dot (s.pinPlus E) (s.guardSourceMinus E) =
      s.cb * (s.ca*(1-2*s.h^2) - 2*s.sa*s.h*s.t) := by
  unfold dot pinPlus guardSourceMinus reflect guardMinus
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, E.sum_z_z, E.sum_z_v]
  linear_combination s.ca * s.cb * s.th_unit

lemma dot_pinMinus_guardSourcePlus :
    dot (s.pinMinus E) (s.guardSourcePlus E) =
      s.cb * (s.ca*(1-2*s.h^2) + 2*s.sa*s.h*s.t) := by
  unfold dot pinMinus guardSourcePlus reflect guardPlus
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, E.sum_z_z, E.sum_z_v]
  linear_combination s.ca * s.cb * s.th_unit

lemma dot_pinMinus_guardSourceMinus :
    dot (s.pinMinus E) (s.guardSourceMinus E) =
      s.cb * (s.ca*(1-2*s.h^2) + 2*s.sa*s.h*s.t) := by
  unfold dot pinMinus guardSourceMinus reflect guardMinus
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, E.sum_z_z, E.sum_z_v]
  linear_combination s.ca * s.cb * s.th_unit
lemma pinPlus_guardSourcePlus_distSq :
    distSq (s.pinPlus E) (s.guardSourcePlus E) =
      2 - 2*s.cb*(s.ca*(1-2*s.h^2)-2*s.sa*s.h*s.t) := by
  rw [distSq_eq_two_sub_two_dot, s.dot_pinPlus_guardSourcePlus E]
  ring

lemma pinPlus_guardSourceMinus_distSq :
    distSq (s.pinPlus E) (s.guardSourceMinus E) =
      2 - 2*s.cb*(s.ca*(1-2*s.h^2)-2*s.sa*s.h*s.t) := by
  rw [distSq_eq_two_sub_two_dot, s.dot_pinPlus_guardSourceMinus E]
  ring

lemma pinMinus_guardSourcePlus_distSq :
    distSq (s.pinMinus E) (s.guardSourcePlus E) =
      2 - 2*s.cb*(s.ca*(1-2*s.h^2)+2*s.sa*s.h*s.t) := by
  rw [distSq_eq_two_sub_two_dot, s.dot_pinMinus_guardSourcePlus E]
  ring

lemma pinMinus_guardSourceMinus_distSq :
    distSq (s.pinMinus E) (s.guardSourceMinus E) =
      2 - 2*s.cb*(s.ca*(1-2*s.h^2)+2*s.sa*s.h*s.t) := by
  rw [distSq_eq_two_sub_two_dot, s.dot_pinMinus_guardSourceMinus E]
  ring

end ModuleScalars
end Ulam165


/-! ==========================================================================
## Component: ModuleMinimization
========================================================================== -/

open scoped BigOperators
open Set

namespace Ulam165
open Sphere

/-- The one-variable inequality behind the exact module minimization.
    This is an algebraic replacement for the derivative argument in the paper. -/
theorem strict_radial_inequality
    {b a2 x : ℝ}
    (hb : 10 ≤ b) (ha2pos : 0 < a2) (ha2 : a2 ≤ (441 : ℝ)/100)
    (hx : 0 < x) :
    1 + b < Real.sqrt (1 + (b^2/a2)*x) + b / Real.sqrt (1+x) := by
  let u : ℝ := Real.sqrt (1+x)
  have h1x : 0 < 1+x := by linarith
  have hu0 : 0 < u := by
    dsimp [u]
    exact Real.sqrt_pos_of_pos h1x
  have hu2 : u^2 = 1+x := by
    dsimp [u]
    exact Real.sq_sqrt (le_of_lt h1x)
  have hu : 1 < u := by
    have hu_nonneg : 0 ≤ u := le_of_lt hu0
    by_contra h
    have hule : u ≤ 1 := le_of_not_gt h
    nlinarith
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  let v : ℝ := u - 1
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have hv3 : 0 ≤ v^3 := by positivity
  have hg_lower :
      2 + ((59 : ℝ)/100)*v + 4*v^2 ≤
        u^2*(u+1) - a2*(u-1) := by
    have ha_gap : 0 ≤ ((441 : ℝ)/100) - a2 := by linarith
    have hprod : 0 ≤ (((441 : ℝ)/100) - a2) * v := mul_nonneg ha_gap hv
    dsimp [v] at hv hv3 ⊢
    nlinarith
  have hg_pos : 0 < u^2*(u+1) - a2*(u-1) := by
    have hq : 0 ≤ v^2 := sq_nonneg v
    nlinarith [hg_lower]
  have hbmul :
      10 * (u^2*(u+1) - a2*(u-1)) ≤
        b * (u^2*(u+1) - a2*(u-1)) := by
    have := mul_nonneg (sub_nonneg.mpr hb) (le_of_lt hg_pos)
    nlinarith
  have haumul : 2*a2*u ≤ ((882 : ℝ)/100)*u := by
    have hu_nonneg : 0 ≤ u := le_of_lt hu0
    have := mul_nonneg (sub_nonneg.mpr ha2) hu_nonneg
    nlinarith
  have hquad : 0 < (1118 : ℝ)/100 - ((292 : ℝ)/100)*v + 40*v^2 := by
    have hs := sq_nonneg (v - (73 : ℝ)/2000)
    nlinarith
  have hH : 0 < b*(u^2*(u+1) - a2*(u-1)) - 2*a2*u := by
    have hlow := hg_lower
    nlinarith [hbmul, haumul, hquad]
  let R : ℝ := 1+b-b/u
  have hR : 0 < R := by
    have hbu : b/u < b := by
      rw [div_lt_iff₀ hu0]
      have : b < b*u := by nlinarith [mul_pos hbpos (sub_pos.mpr hu)]
      exact this
    dsimp [R]
    linarith
  let rad : ℝ := 1 + (b^2/a2)*x
  have hrad : 0 < rad := by
    dsimp [rad]
    have : 0 < (b^2/a2)*x := by positivity
    linarith
  have hid :
      a2*u^2*(rad - R^2) =
        (u-1)*b*(b*(u^2*(u+1)-a2*(u-1))-2*a2*u) := by
    have hxU : x = u^2 - 1 := by nlinarith [hu2]
    dsimp [rad, R]
    rw [hxU]
    have ha2ne : a2 ≠ 0 := ne_of_gt ha2pos
    have hune : u ≠ 0 := ne_of_gt hu0
    field_simp [ha2ne, hune]
    ring
  have hdiff : 0 < rad - R^2 := by
    have hleft : 0 < a2*u^2 := by positivity
    have hright : 0 < (u-1)*b*(b*(u^2*(u+1)-a2*(u-1))-2*a2*u) := by
      positivity
    rw [← hid] at hright
    rcases (mul_pos_iff.mp hright) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge (le_of_lt hleft) hneg.1).elim
  have hsqrtR : R < Real.sqrt rad := by
    by_contra h
    have hsle : Real.sqrt rad ≤ R := le_of_not_gt h
    have hsnonneg := Real.sqrt_nonneg rad
    have hs2 : (Real.sqrt rad)^2 = rad := Real.sq_sqrt (le_of_lt hrad)
    have hsquares : (Real.sqrt rad)^2 ≤ R^2 := by nlinarith
    nlinarith
  dsimp [R, rad, u] at hsqrtR ⊢
  have hsqrt_ne : Real.sqrt (1+x) ≠ 0 := by positivity
  nlinarith

variable {d : ℕ}

/-- The four scaffold pairs of one module. -/
def scaffoldGraph (E : EqFrame d) (s : ModuleScalars) : List (Sphere d × Sphere d) :=
  [ (s.pinPlus E, s.pinPlus E),
    (s.pinMinus E, s.pinMinus E),
    (s.guardSourcePlus E, s.guardPlus E),
    (s.guardSourceMinus E, s.guardMinus E) ]

lemma pinPlus_pair_mem (E : EqFrame d) (s : ModuleScalars) :
    (s.pinPlus E, s.pinPlus E) ∈ scaffoldGraph E s := by simp [scaffoldGraph]
lemma pinMinus_pair_mem (E : EqFrame d) (s : ModuleScalars) :
    (s.pinMinus E, s.pinMinus E) ∈ scaffoldGraph E s := by simp [scaffoldGraph]
lemma guardPlus_pair_mem (E : EqFrame d) (s : ModuleScalars) :
    (s.guardSourcePlus E, s.guardPlus E) ∈ scaffoldGraph E s := by simp [scaffoldGraph]
lemma guardMinus_pair_mem (E : EqFrame d) (s : ModuleScalars) :
    (s.guardSourceMinus E, s.guardMinus E) ∈ scaffoldGraph E s := by simp [scaffoldGraph]

/-- Any graph containing the scaffold and a candidate center pair has a strict
    cost lower bound away from the intended center. This is the machine-facing
    form of the paper's Exact Module Minimization Lemma. -/
theorem exact_module_radial_lower
    (E : EqFrame d) (s : ModuleScalars)
    (g : List (Sphere d × Sphere d)) (y : Sphere d)
    (hsc : ∀ a ∈ scaffoldGraph E s, a ∈ g)
    (hcenter : (s.center E, y) ∈ g)
    (hycenter : y ≠ s.center E)
    (hyGp : y ≠ s.guardPlus E) (hyGm : y ≠ s.guardMinus E)
    (hca : 0 < s.ca) (hcb : 0 < s.cb) (hcbca : s.cb < s.ca)
    (hd2 : 0 < 2 - 2*s.cb)
    (hrho2 : 0 < 2 - 2*s.ca)
    (hB2 : 100 ≤ ((2 - 2*s.cb) + 4*s.h^2*s.cb) / (2 - 2*s.cb))
    (hastar :
      ((2 - 2*s.ca) *
          (((2 - 2*s.cb) + 4*s.h^2*s.cb) / (2 - 2*s.cb)) /
          (2 - 2*s.cb)) ≤ (441 : ℝ)/100) :
    1 + Real.sqrt (((2 - 2*s.cb) + 4*s.h^2*s.cb) / (2 - 2*s.cb)) <
      greedyCost g := by
  let rho2 : ℝ := 2 - 2*s.ca
  let d2 : ℝ := 2 - 2*s.cb
  let B2 : ℝ := (d2 + 4*s.h^2*s.cb) / d2
  let astar2 : ℝ := rho2*B2/d2
  let atilde2 : ℝ := astar2*s.cb/s.ca
  let t2 : ℝ := distSq y (s.center E)
  let x : ℝ := s.cb/d2*t2
  have ht2 : 0 < t2 := by
    dsimp [t2]
    exact distSq_pos hycenter
  have hB2pos : 0 < B2 := by dsimp [B2, d2]; linarith
  have hB : 10 ≤ Real.sqrt B2 := by
    have h100 : (100 : ℝ) ≤ B2 := by simpa [B2, d2] using hB2
    have hs := Real.sqrt_le_sqrt h100
    norm_num at hs
    exact hs
  have hastar_pos : 0 < astar2 := by
    dsimp [astar2, rho2, B2, d2]
    positivity
  have hatilde_pos : 0 < atilde2 := by
    dsimp [atilde2]
    positivity
  have hcbca_nonneg : 0 ≤ s.cb/s.ca := by positivity
  have hratio_lt_one : s.cb/s.ca < 1 := by
    rw [div_lt_one hca]
    exact hcbca
  have hatilde_le_astar : atilde2 ≤ astar2 := by
    have hm := mul_le_mul_of_nonneg_left (le_of_lt hratio_lt_one) (le_of_lt hastar_pos)
    calc
      atilde2 = astar2 * (s.cb / s.ca) := by dsimp [atilde2]; ring
      _ ≤ astar2 * 1 := hm
      _ = astar2 := by ring
  have hatilde_bound : atilde2 ≤ (441 : ℝ)/100 := by
    have hastar_bound : astar2 ≤ (441 : ℝ)/100 := by
      simpa [astar2, rho2, B2, d2] using hastar
    exact le_trans hatilde_le_astar hastar_bound
  have hx : 0 < x := by
    dsimp [x]
    positivity

  rcases s.exists_pin_radial_lower E y with ⟨P, hPmem, hP⟩
  have hPcases : P = s.pinPlus E ∨ P = s.pinMinus E := by
    simpa using hPmem
  have hPpair : (P,P) ∈ g := by
    rcases hPcases with hpp | hpm
    · subst P
      exact hsc _ (pinPlus_pair_mem E s)
    · subst P
      exact hsc _ (pinMinus_pair_mem E s)
  have hFratio := ratio_le_forwardLipSq hcenter hPpair
  have hFden : distSq (s.center E) P = rho2 := by
    rcases hPcases with hpp | hpm
    · subst P
      simpa [rho2] using s.center_pinPlus_distSq E
    · subst P
      simpa [rho2] using s.center_pinMinus_distSq E
  have hFbound : 1 + (B2/atilde2)*x ≤ forwardLipSq g := by
    have hP' : rho2 + s.ca*t2 ≤ distSq y P := by
      simpa [rho2, t2] using hP
    have hratio : (rho2 + s.ca*t2)/rho2 ≤ distSq y P / rho2 := by
      exact div_le_div_of_nonneg_right hP' (le_of_lt hrho2)
    have hd2ne : d2 ≠ 0 := by dsimp [d2]; linarith
    have hrho2ne : rho2 ≠ 0 := by dsimp [rho2]; linarith
    have hidcoef : (B2/atilde2)*x = s.ca*t2/rho2 := by
      dsimp [atilde2, astar2, x]
      field_simp [ne_of_gt hca, ne_of_gt hcb, hd2ne, hrho2ne,
        ne_of_gt hB2pos]
    have hratmem : distSq y P / rho2 ≤ forwardLipSq g := by
      rw [hFden] at hFratio
      simpa using hFratio
    rw [hidcoef]
    have hrewrite : 1 + s.ca*t2/rho2 = (rho2+s.ca*t2)/rho2 := by
      field_simp [hrho2ne]
    rw [hrewrite]
    exact le_trans hratio hratmem

  rcases s.exists_guard_radial_upper E y with ⟨G, hGmem, hG⟩
  have hGcases : G = s.guardPlus E ∨ G = s.guardMinus E := by
    simpa using hGmem
  have hGpair : ∃ JG, (JG,G) ∈ g ∧
      distSq (s.center E) JG = d2 + 4*s.h^2*s.cb := by
    rcases hGcases with hgp | hgm
    · subst G
      refine ⟨s.guardSourcePlus E, hsc _ (guardPlus_pair_mem E s), ?_⟩
      simpa [d2] using s.center_guardSourcePlus_distSq E
    · subst G
      refine ⟨s.guardSourceMinus E, hsc _ (guardMinus_pair_mem E s), ?_⟩
      simpa [d2] using s.center_guardSourceMinus_distSq E
  rcases hGpair with ⟨JG, hJGmem, hJGdist⟩
  have hIdenPos : 0 < distSq y G := by
    rcases hGcases with hgp | hgm
    · subst G
      exact distSq_pos hyGp
    · subst G
      exact distSq_pos hyGm
  have hIratio := inverse_ratio_le_inverseLipSq hcenter hJGmem
  have hG' : distSq y G ≤ d2 + s.cb*t2 := by
    simpa [d2, t2] using hG
  have hnum : distSq (s.center E) JG = B2*d2 := by
    have hd2ne : d2 ≠ 0 := by dsimp [d2]; linarith
    rw [hJGdist]
    dsimp [B2]
    field_simp [hd2ne]
  have hIbound : B2/(1+x) ≤ inverseLipSq g := by
    have hdenpos : 0 < d2 + s.cb*t2 := by positivity
    have hfrac : (B2*d2)/(d2+s.cb*t2) ≤
        distSq (s.center E) JG / distSq y G := by
      rw [hnum]
      exact div_le_div_of_nonneg_left (by positivity) hIdenPos hG'
    have hmem : distSq (s.center E) JG / distSq y G ≤ inverseLipSq g := by
      simpa using hIratio
    have hd2ne : d2 ≠ 0 := by dsimp [d2]; linarith
    have hrewrite : B2/(1+x) = (B2*d2)/(d2+s.cb*t2) := by
      dsimp [x]
      field_simp [hd2ne]
    rw [hrewrite]
    exact le_trans hfrac hmem

  have hradF : 0 ≤ 1 + (B2/atilde2)*x := by positivity
  have hradI : 0 ≤ B2/(1+x) := by positivity
  have hsF : Real.sqrt (1 + (B2/atilde2)*x) ≤
      Real.sqrt (forwardLipSq g) := Real.sqrt_le_sqrt hFbound
  have hsI : Real.sqrt (B2/(1+x)) ≤ Real.sqrt (inverseLipSq g) :=
    Real.sqrt_le_sqrt hIbound
  have hB2sqrt : Real.sqrt B2 ^ 2 = B2 := Real.sq_sqrt (le_of_lt hB2pos)
  have hsdiv : Real.sqrt (B2/(1+x)) = Real.sqrt B2 / Real.sqrt (1+x) := by
    simpa using Real.sqrt_div (le_of_lt hB2pos) (1+x)
  have hstrict := strict_radial_inequality hB hatilde_pos hatilde_bound hx
  rw [hB2sqrt] at hstrict
  have hsI' : Real.sqrt B2 / Real.sqrt (1+x) ≤ Real.sqrt (inverseLipSq g) := by
    rw [← hsdiv]
    exact hsI
  unfold greedyCost
  have hsum :
      Real.sqrt (1 + (B2/atilde2)*x) + Real.sqrt B2 / Real.sqrt (1+x) ≤
        Real.sqrt (forwardLipSq g) + Real.sqrt (inverseLipSq g) := by
    linarith
  have : 1 + Real.sqrt B2 <
      Real.sqrt (forwardLipSq g) + Real.sqrt (inverseLipSq g) := lt_of_lt_of_le hstrict hsum
  simpa [B2, d2] using this

end Ulam165


/-! ==========================================================================
## Component: State
========================================================================== -/

open scoped BigOperators
open Set

namespace Ulam165
open Sphere

variable {d : ℕ}

/-- A candidate image must avoid the finite set of old images. -/
def ImageAdmissible (src : List (Sphere d)) (y : Sphere d) : Prop :=
  y ∉ src.map fold

/-- The exact unique greedy-step predicate used in the formal verification. -/
def UniqueGreedyStep (src : List (Sphere d)) (x y : Sphere d) : Prop :=
  x ∉ src ∧ ImageAdmissible src y ∧
    ∀ z : Sphere d, ImageAdmissible src z → z ≠ y →
      greedyCost (candidateGraph src x y) < greedyCost (candidateGraph src x z)

/-- Inductive certificate that every point appended after a base list was the
    unique greedy choice at the moment it was appended. -/
inductive GreedyBuiltFrom (base : List (Sphere d)) : List (Sphere d) → Prop
  | base : GreedyBuiltFrom base base
  | step {src : List (Sphere d)} {x : Sphere d} :
      GreedyBuiltFrom base src →
      UniqueGreedyStep src x (fold x) →
      GreedyBuiltFrom base (src ++ [x])

lemma forwardLipSq_mono_of_mem {g h : List (Sphere d × Sphere d)}
    (hsub : ∀ a ∈ g, a ∈ h) : forwardLipSq g ≤ forwardLipSq h := by
  apply forwardLipSq_le_of_bound (forwardLipSq_nonneg h)
  intro a ha b hb
  exact ratio_le_forwardLipSq (hsub a ha) (hsub b hb)

lemma inverseLipSq_mono_of_mem {g h : List (Sphere d × Sphere d)}
    (hsub : ∀ a ∈ g, a ∈ h) : inverseLipSq g ≤ inverseLipSq h := by
  apply inverseLipSq_le_of_bound (inverseLipSq_nonneg h)
  intro a ha b hb
  exact inverse_ratio_le_inverseLipSq (hsub a ha) (hsub b hb)

lemma foldGraph_append_single (src : List (Sphere d)) (x : Sphere d) :
    foldGraph (src ++ [x]) = candidateGraph src x (fold x) := by
  simp [foldGraph, candidateGraph]

lemma oldGraph_mem_candidate {src : List (Sphere d)} {x y : Sphere d}
    {a : Sphere d × Sphere d} (ha : a ∈ foldGraph src) :
    a ∈ candidateGraph src x y := by
  simp [candidateGraph, ha]

/-- The fold graph has forward Lipschitz constant exactly 1 as soon as it
    contains one pair of opposite equatorial anchors. -/
theorem forwardLipSq_foldGraph_eq_one
    (src : List (Sphere d)) (i : Fin d)
    (hpos : epos i ∈ src) (hneg : eneg i ∈ src) :
    forwardLipSq (foldGraph src) = 1 := by
  apply forwardLipSq_eq_of_bound_witness (by norm_num)
  · intro a ha b hb
    rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
    rcases List.mem_map.mp hb with ⟨q, hq, rfl⟩
    by_cases hpq : p = q
    · subst hpq
      simp [distSq_self]
    · have hden := distSq_pos hpq
      have hfold := fold_distSq_le p q
      rw [div_le_one hden]
      exact hfold
  · exact foldGraph_mem hpos
  · exact foldGraph_mem hneg
  · have hne : epos i ≠ eneg i := by
      intro h
      have hc := congrArg (fun p : Sphere d => p.1.1 i) h
      norm_num [epos, eneg] at hc
    have hden : 0 < distSq (epos i) (eneg i) := distSq_pos hne
    have hdenne : distSq (epos i) (eneg i) ≠ 0 := ne_of_gt hden
    rw [fold_epos, fold_eneg]
    exact div_self hdenne

/-- Exact inverse constant is preserved when a new fold pair has all cross
    inverse ratios bounded by the old exact constant. -/
theorem inverseLipSq_fold_append_eq
    (src : List (Sphere d)) (x : Sphere d) (B2 : ℝ)
    (hold : inverseLipSq (foldGraph src) = B2)
    (hB2 : 0 ≤ B2)
    (hxnew : x ∉ src)
    (hcross : ∀ p ∈ src,
      distSq x p / distSq (fold x) (fold p) ≤ B2) :
    inverseLipSq (foldGraph (src ++ [x])) = B2 := by
  have hle : inverseLipSq (foldGraph (src ++ [x])) ≤ B2 := by
    apply inverseLipSq_le_of_bound hB2
    intro a ha b hb
    rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
    rcases List.mem_map.mp hb with ⟨q, hq, rfl⟩
    simp only [List.mem_append, List.mem_singleton] at hp hq
    rcases hp with hp | rfl
    · rcases hq with hq | rfl
      · have hrat := inverse_ratio_le_inverseLipSq (foldGraph_mem hp) (foldGraph_mem hq)
        rw [hold] at hrat
        exact hrat
      · simpa [distSq_comm] using hcross p hp
    · rcases hq with hq | rfl
      · exact hcross q hq
      · simpa [distSq_self] using hB2
  have hge : B2 ≤ inverseLipSq (foldGraph (src ++ [x])) := by
    rw [← hold]
    apply inverseLipSq_mono_of_mem
    intro a ha
    rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
    exact foldGraph_mem (by simp [hp])
  exact le_antisymm hle hge

/-- An upper cross-inverse certificate is enough to make the intended fold
    image the unique Ulam greedy choice. -/
theorem fold_extension_unique_greedy
    (src : List (Sphere d)) (i0 : Fin d) (x : Sphere d) (B2 : ℝ)
    (hpos : ∀ i : Fin d, epos i ∈ src)
    (hneg : ∀ i : Fin d, eneg i ∈ src)
    (hsouth : south d ∈ src)
    (ha : anchorA i0 ∈ src)
    (holdInv : inverseLipSq (foldGraph src) = B2)
    (hB2 : 100 ≤ B2)
    (hxnew : x ∉ src)
    (hfoldnew : fold x ∉ src.map fold)
    (hcross : ∀ p ∈ src,
      distSq x p / distSq (fold x) (fold p) ≤ B2) :
    UniqueGreedyStep src x (fold x) := by
  have hB2nonneg : 0 ≤ B2 := by linarith
  have hforwardOld : forwardLipSq (foldGraph src) = 1 :=
    forwardLipSq_foldGraph_eq_one src i0 (hpos i0) (hneg i0)
  have hforwardIntended :
      forwardLipSq (candidateGraph src x (fold x)) = 1 := by
    rw [← foldGraph_append_single]
    exact forwardLipSq_foldGraph_eq_one (src ++ [x]) i0 (by simp [hpos i0]) (by simp [hneg i0])
  have hinvIntended :
      inverseLipSq (candidateGraph src x (fold x)) = B2 := by
    rw [← foldGraph_append_single]
    exact inverseLipSq_fold_append_eq src x B2 holdInv hB2nonneg hxnew hcross
  refine ⟨hxnew, hfoldnew, ?_⟩
  intro y hyadm hyne
  have hOldFle : 1 ≤ forwardLipSq (candidateGraph src x y) := by
    rw [← hforwardOld]
    apply forwardLipSq_mono_of_mem
    intro a ha0
    exact oldGraph_mem_candidate ha0
  have hOldIle : B2 ≤ inverseLipSq (candidateGraph src x y) := by
    rw [← holdInv]
    apply inverseLipSq_mono_of_mem
    intro a ha0
    exact oldGraph_mem_candidate ha0
  have hFstrict : 1 < forwardLipSq (candidateGraph src x y) := by
    apply lt_of_le_of_ne hOldFle
    intro heq
    have hFle : forwardLipSq (candidateGraph src x y) ≤ 1 := by linarith
    have hpinPos : ∀ i : Fin d, distSq y (epos i) ≤ distSq x (epos i) := by
      intro i
      have hr := ratio_le_forwardLipSq (candidate_new_mem src x y)
        (candidate_old_mem (hpos i))
      rw [fold_epos] at hr
      have hden : 0 < distSq x (epos i) := by
        apply distSq_pos
        intro hx
        apply hxnew
        simpa [hx] using hpos i
      have hratio : distSq y (epos i) / distSq x (epos i) ≤ 1 := le_trans hr hFle
      rwa [div_le_one hden] at hratio
    have hpinNeg : ∀ i : Fin d, distSq y (eneg i) ≤ distSq x (eneg i) := by
      intro i
      have hr := ratio_le_forwardLipSq (candidate_new_mem src x y)
        (candidate_old_mem (hneg i))
      rw [fold_eneg] at hr
      have hden : 0 < distSq x (eneg i) := by
        apply distSq_pos
        intro hx
        apply hxnew
        simpa [hx] using hneg i
      have hratio : distSq y (eneg i) / distSq x (eneg i) ≤ 1 := le_trans hr hFle
      rwa [div_le_one hden] at hratio
    have hpinSouth : distSq y (north d) ≤ distSq x (south d) := by
      have hr := ratio_le_forwardLipSq (candidate_new_mem src x y)
        (candidate_old_mem hsouth)
      rw [fold_south] at hr
      have hden : 0 < distSq x (south d) := by
        apply distSq_pos
        intro hx
        apply hxnew
        simpa [hx] using hsouth
      have hratio : distSq y (north d) / distSq x (south d) ≤ 1 := le_trans hr hFle
      rwa [div_le_one hden] at hratio
    have hpinA : distSq y (anchorA i0) ≤ distSq x (anchorA i0) := by
      have hr := ratio_le_forwardLipSq (candidate_new_mem src x y)
        (candidate_old_mem ha)
      rw [fold_anchorA] at hr
      have hden : 0 < distSq x (anchorA i0) := by
        apply distSq_pos
        intro hx
        apply hxnew
        simpa [hx] using ha
      have hratio : distSq y (anchorA i0) / distSq x (anchorA i0) ≤ 1 := le_trans hr hFle
      rwa [div_le_one hden] at hratio
    have hyfold := fold_pinning i0 x y hpinPos hpinNeg hpinSouth hpinA
    exact hyne hyfold
  have hsqrtF : 1 < Real.sqrt (forwardLipSq (candidateGraph src x y)) := by
    have := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) hFstrict
    simpa using this
  have hsqrtI : Real.sqrt B2 ≤ Real.sqrt (inverseLipSq (candidateGraph src x y)) :=
    Real.sqrt_le_sqrt hOldIle
  unfold greedyCost
  rw [hforwardIntended, hinvIntended]
  norm_num
  linarith

end Ulam165

namespace Ulam165
open Sphere
variable {d : ℕ}

/-- Uniform squared inverse-ratio safety of a finite source list under the
fold. -/
def FoldInverseSafe (src : List (Sphere d)) (B2 : ℝ) : Prop :=
  ∀ p ∈ src, ∀ q ∈ src,
    distSq p q / distSq (fold p) (fold q) ≤ B2

lemma foldInverseSafe_of_inverse_eq (src : List (Sphere d)) (B2 : ℝ)
    (h : inverseLipSq (foldGraph src) = B2) : FoldInverseSafe src B2 := by
  intro p hp q hq
  have hr := inverse_ratio_le_inverseLipSq (foldGraph_mem hp) (foldGraph_mem hq)
  simpa [h] using hr

lemma foldInverseSafe_mono {src big : List (Sphere d)} {B2 : ℝ}
    (hbig : FoldInverseSafe big B2)
    (hsub : ∀ p ∈ src, p ∈ big) : FoldInverseSafe src B2 := by
  intro p hp q hq
  exact hbig p (hsub p hp) q (hsub q hq)

/-- Appending a finite block of fold pairs is automatically a sequence of
unique greedy steps when the old inverse record stays exact, all ratios in the
whole enlarged block are below that record, and all fold images are distinct.
This is the bookkeeping lemma used for the four scaffold points and for the
separate density points. -/
theorem append_fold_block_greedily
    {base src xs : List (Sphere d)} (i0 : Fin d) (B2 : ℝ)
    (hbuilt : GreedyBuiltFrom base src)
    (hpos : ∀ i : Fin d, epos i ∈ src)
    (hneg : ∀ i : Fin d, eneg i ∈ src)
    (hsouth : south d ∈ src)
    (ha : anchorA i0 ∈ src)
    (holdInv : inverseLipSq (foldGraph src) = B2)
    (hB2 : 100 ≤ B2)
    (hsafe : FoldInverseSafe (src ++ xs) B2)
    (hnd : ((src ++ xs).map fold).Nodup) :
    GreedyBuiltFrom base (src ++ xs) ∧
      inverseLipSq (foldGraph (src ++ xs)) = B2 := by
  induction xs using List.reverseRecOn with
  | nil => simpa using And.intro hbuilt holdInv
  | append_singleton xs x ih =>
      have hsafe0 : FoldInverseSafe (src ++ xs) B2 :=
        foldInverseSafe_mono hsafe (by
          intro p hp
          simpa [List.append_assoc] using (List.mem_append_left [x] hp))
      have hndsplit : ((src ++ xs).map fold ++ [fold x]).Nodup := by
        simpa [List.append_assoc, List.map_append] using hnd
      have hnd0 : ((src ++ xs).map fold).Nodup :=
        (List.nodup_append.mp hndsplit).1
      obtain ⟨hbuilt0, hinv0⟩ := ih hsafe0 hnd0
      have hximage : fold x ∉ (src ++ xs).map fold := by
        have hdisj := (List.nodup_append.mp hndsplit).2.2
        intro hxmem
        exact (hdisj (fold x) hxmem (fold x) (by simp)) rfl
      have hxsource : x ∉ src ++ xs := by
        intro hx
        exact hximage (List.mem_map.mpr ⟨x,hx,rfl⟩)
      have hcross : ∀ p ∈ src ++ xs,
          distSq x p / distSq (fold x) (fold p) ≤ B2 := by
        intro p hp
        exact hsafe x (by simp) p
          (by
            have : p ∈ (src ++ xs) ++ [x] := List.mem_append_left [x] hp
            simpa [List.append_assoc] using this)
      have hstep : UniqueGreedyStep (src ++ xs) x (fold x) :=
        fold_extension_unique_greedy (src ++ xs) i0 x B2
          (fun i => by simp [hpos i]) (fun i => by simp [hneg i])
          (by simp [hsouth]) (by simp [ha]) hinv0 hB2 hxsource hximage hcross
      constructor
      · simpa [List.append_assoc] using GreedyBuiltFrom.step hbuilt0 hstep
      · have heq := inverseLipSq_fold_append_eq (src ++ xs) x B2
          hinv0 (by linarith) hxsource hcross
        simpa [List.append_assoc, foldGraph_append_single] using heq

end Ulam165

/-! ==========================================================================
## Component: CanonicalFrame
========================================================================== -/

open scoped BigOperators
open Set

namespace Ulam165
open Sphere

variable {d : ℕ}

/-- Coordinate zero, available in every positive dimension. -/
def idx0 (d : ℕ) (hd : 1 ≤ d) : Fin d := ⟨0, hd⟩

/-- Coordinate one, available in every dimension at least two. -/
def idx1 (d : ℕ) (hd : 2 ≤ d) : Fin d := ⟨1, hd⟩

lemma idx0_ne_idx1 (d : ℕ) (hd : 2 ≤ d) :
    idx0 d (le_trans (by norm_num) hd) ≠ idx1 d hd := by
  intro h
  have := congrArg Fin.val h
  norm_num [idx0, idx1] at this


lemma sum_two_ite {α : Type*} [Fintype α] [DecidableEq α]
    (i0 i1 : α) (h01 : i0 ≠ i1) (a b : ℝ) :
    (∑ j : α, if j = i0 then a else if j = i1 then b else 0) = a + b := by
  classical
  calc
    (∑ j : α, if j = i0 then a else if j = i1 then b else 0) =
        ∑ j : α, ((if j = i0 then a else 0) + (if j = i1 then b else 0)) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h0 : j = i0
      · subst j
        simp [h01]
      · by_cases h1 : j = i1
        · subst j
          simp [h0]
        · simp [h0, h1]
    _ = (∑ j : α, if j = i0 then a else 0) +
        (∑ j : α, if j = i1 then b else 0) := by
      rw [Finset.sum_add_distrib]
    _ = a + b := by simp

/-- A fixed rational equatorial orthonormal frame.  Using one fixed frame for
all fresh modules is enough: density is supplied by the separately inserted
source points, while the modules only need to shrink to an unused equatorial
point.  This avoids a Stiefel-density detour in the formal verification. -/
def canonicalFrame (d : ℕ) (hd : 2 ≤ d) : EqFrame d := by
  let i0 : Fin d := idx0 d (le_trans (by norm_num) hd)
  let i1 : Fin d := idx1 d hd
  have h01 : i0 ≠ i1 := idx0_ne_idx1 d hd
  let z : Fin d → ℝ := fun j =>
    if j = i0 then (3 : ℝ) / 5 else if j = i1 then (4 : ℝ) / 5 else 0
  let v : Fin d → ℝ := fun j =>
    if j = i0 then -(4 : ℝ) / 5 else if j = i1 then (3 : ℝ) / 5 else 0
  refine {
    z := z
    v := v
    z_norm := ?_
    v_norm := ?_
    zv_orth := ?_ }
  · dsimp [z]
    calc
      (∑ j, (if j = i0 then (3 : ℝ)/5 else if j = i1 then (4 : ℝ)/5 else 0)^2) =
          ∑ j, if j = i0 then ((3 : ℝ)/5)^2 else if j = i1 then ((4 : ℝ)/5)^2 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h0 : j = i0
        · subst j; simp
        · by_cases h1 : j = i1
          · subst j; simp [h0]
          · simp [h0, h1]
      _ = ((3 : ℝ)/5)^2 + ((4 : ℝ)/5)^2 := sum_two_ite i0 i1 h01 _ _
      _ = 1 := by norm_num
  · dsimp [v]
    calc
      (∑ j, (if j = i0 then -(4 : ℝ)/5 else if j = i1 then (3 : ℝ)/5 else 0)^2) =
          ∑ j, if j = i0 then (-(4 : ℝ)/5)^2 else if j = i1 then ((3 : ℝ)/5)^2 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h0 : j = i0
        · subst j; simp
        · by_cases h1 : j = i1
          · subst j; simp [h0]
          · simp [h0, h1]
      _ = (-(4 : ℝ)/5)^2 + ((3 : ℝ)/5)^2 := sum_two_ite i0 i1 h01 _ _
      _ = 1 := by norm_num
  · dsimp [z, v]
    calc
      (∑ j, (if j = i0 then (3 : ℝ)/5 else if j = i1 then (4 : ℝ)/5 else 0) *
          (if j = i0 then -(4 : ℝ)/5 else if j = i1 then (3 : ℝ)/5 else 0)) =
          ∑ j, if j = i0 then ((3 : ℝ)/5)*(-(4 : ℝ)/5)
            else if j = i1 then ((4 : ℝ)/5)*((3 : ℝ)/5) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h0 : j = i0
        · subst j; simp
        · by_cases h1 : j = i1
          · subst j; simp [h0]
          · simp [h0, h1]
      _ = ((3 : ℝ)/5)*(-(4 : ℝ)/5) + ((4 : ℝ)/5)*((3 : ℝ)/5) :=
        sum_two_ite i0 i1 h01 _ _
      _ = 0 := by norm_num

/-- The fixed module accumulation point. -/
def moduleZeta (d : ℕ) (hd : 2 ≤ d) : Sphere d :=
  (canonicalFrame d hd).zeta

lemma canonicalFrame_z_rational (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    ∃ q : ℚ, (canonicalFrame d hd).z i = (q : ℝ) := by
  let i0 : Fin d := idx0 d (le_trans (by norm_num) hd)
  let i1 : Fin d := idx1 d hd
  have h01 : i0 ≠ i1 := idx0_ne_idx1 d hd
  have h10 : i1 ≠ i0 := Ne.symm h01
  by_cases h0 : i = i0
  · refine ⟨3/5, ?_⟩
    simp [canonicalFrame, i0, h0]
  · by_cases h1 : i = i1
    · refine ⟨4/5, ?_⟩
      simp [canonicalFrame, i0, i1, h1, h10]
    · refine ⟨0, ?_⟩
      simp [canonicalFrame, i0, i1, h0, h1]

lemma canonicalFrame_v_rational (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    ∃ q : ℚ, (canonicalFrame d hd).v i = (q : ℝ) := by
  let i0 : Fin d := idx0 d (le_trans (by norm_num) hd)
  let i1 : Fin d := idx1 d hd
  have h01 : i0 ≠ i1 := idx0_ne_idx1 d hd
  have h10 : i1 ≠ i0 := Ne.symm h01
  by_cases h0 : i = i0
  · refine ⟨-4/5, ?_⟩
    simp [canonicalFrame, i0, h0]
  · by_cases h1 : i = i1
    · refine ⟨3/5, ?_⟩
      simp [canonicalFrame, i0, i1, h1, h10]
    · refine ⟨0, ?_⟩
      simp [canonicalFrame, i0, i1, h0, h1]

lemma rational_moduleZeta (d : ℕ) (hd : 2 ≤ d) :
    RationalPoint (moduleZeta d hd) := by
  constructor
  · intro i
    simpa [moduleZeta, EqFrame.zeta] using canonicalFrame_z_rational d hd i
  · exact ⟨0, by simp [moduleZeta, EqFrame.zeta]⟩

/-- Rationality of all module points follows from rationality of the frame and
of the six scalar parameters.  This generic lemma lets the later explicit
half-angle family discharge rationality without coordinate-by-coordinate
repetition. -/
def RationalScalars (s : ModuleScalars) : Prop :=
  (∃ q : ℚ, s.t = (q : ℝ)) ∧
  (∃ q : ℚ, s.h = (q : ℝ)) ∧
  (∃ q : ℚ, s.ca = (q : ℝ)) ∧
  (∃ q : ℚ, s.sa = (q : ℝ)) ∧
  (∃ q : ℚ, s.cb = (q : ℝ)) ∧
  (∃ q : ℚ, s.sb = (q : ℝ))

def RationalFrame (E : EqFrame d) : Prop :=
  (∀ i, ∃ q : ℚ, E.z i = (q : ℝ)) ∧
  (∀ i, ∃ q : ℚ, E.v i = (q : ℝ))

lemma canonicalFrame_rational (d : ℕ) (hd : 2 ≤ d) :
    RationalFrame (canonicalFrame d hd) :=
  ⟨canonicalFrame_z_rational d hd, canonicalFrame_v_rational d hd⟩

lemma rationalModuleScalars_rational (s a b : ℚ) :
    RationalScalars (rationalModuleScalars s a b) := by
  refine ⟨⟨qCos s, rfl⟩, ⟨qSin s, rfl⟩,
    ⟨qCos a, rfl⟩, ⟨qSin a, rfl⟩,
    ⟨qCos b, rfl⟩, ⟨qSin b, rfl⟩⟩

private lemma rat_add {x y : ℝ}
    (hx : ∃ q : ℚ, x = (q : ℝ)) (hy : ∃ q : ℚ, y = (q : ℝ)) :
    ∃ q : ℚ, x + y = (q : ℝ) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a+b, by norm_num⟩

private lemma rat_sub {x y : ℝ}
    (hx : ∃ q : ℚ, x = (q : ℝ)) (hy : ∃ q : ℚ, y = (q : ℝ)) :
    ∃ q : ℚ, x - y = (q : ℝ) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a-b, by norm_num⟩

private lemma rat_mul {x y : ℝ}
    (hx : ∃ q : ℚ, x = (q : ℝ)) (hy : ∃ q : ℚ, y = (q : ℝ)) :
    ∃ q : ℚ, x * y = (q : ℝ) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a*b, by norm_num⟩

lemma rational_center {E : EqFrame d} {s : ModuleScalars}
    (hE : RationalFrame E) (hs : RationalScalars s) :
    RationalPoint (s.center E) := by
  rcases hE with ⟨hz, hv⟩
  rcases hs with ⟨ht, hh, hca, hsa, hcb, hsb⟩
  constructor
  · intro i
    exact rat_mul ht (hz i)
  · simpa [ModuleScalars.center] using hh

lemma rational_pinPlus {E : EqFrame d} {s : ModuleScalars}
    (hE : RationalFrame E) (hs : RationalScalars s) :
    RationalPoint (s.pinPlus E) := by
  rcases hE with ⟨hz, hv⟩
  rcases hs with ⟨ht, hh, hca, hsa, hcb, hsb⟩
  have hcoef : ∃ q : ℚ, s.ca*s.t - s.sa*s.h = (q : ℝ) :=
    rat_sub (rat_mul hca ht) (rat_mul hsa hh)
  constructor
  · intro i
    exact rat_mul hcoef (hz i)
  · exact rat_add (rat_mul hca hh) (rat_mul hsa ht)

lemma rational_pinMinus {E : EqFrame d} {s : ModuleScalars}
    (hE : RationalFrame E) (hs : RationalScalars s) :
    RationalPoint (s.pinMinus E) := by
  rcases hE with ⟨hz, hv⟩
  rcases hs with ⟨ht, hh, hca, hsa, hcb, hsb⟩
  have hcoef : ∃ q : ℚ, s.ca*s.t + s.sa*s.h = (q : ℝ) :=
    rat_add (rat_mul hca ht) (rat_mul hsa hh)
  constructor
  · intro i
    exact rat_mul hcoef (hz i)
  · exact rat_sub (rat_mul hca hh) (rat_mul hsa ht)

lemma rational_guardPlus {E : EqFrame d} {s : ModuleScalars}
    (hE : RationalFrame E) (hs : RationalScalars s) :
    RationalPoint (s.guardPlus E) := by
  rcases hE with ⟨hz, hv⟩
  rcases hs with ⟨ht, hh, hca, hsa, hcb, hsb⟩
  constructor
  · intro i
    exact rat_add (rat_mul (rat_mul hcb ht) (hz i)) (rat_mul hsb (hv i))
  · exact rat_mul hcb hh

lemma rational_guardMinus {E : EqFrame d} {s : ModuleScalars}
    (hE : RationalFrame E) (hs : RationalScalars s) :
    RationalPoint (s.guardMinus E) := by
  rcases hE with ⟨hz, hv⟩
  rcases hs with ⟨ht, hh, hca, hsa, hcb, hsb⟩
  constructor
  · intro i
    exact rat_sub (rat_mul (rat_mul hcb ht) (hz i)) (rat_mul hsb (hv i))
  · exact rat_mul hcb hh

lemma rational_guardSourcePlus {E : EqFrame d} {s : ModuleScalars}
    (hE : RationalFrame E) (hs : RationalScalars s) :
    RationalPoint (s.guardSourcePlus E) := by
  exact rational_reflect (rational_guardPlus hE hs)

lemma rational_guardSourceMinus {E : EqFrame d} {s : ModuleScalars}
    (hE : RationalFrame E) (hs : RationalScalars s) :
    RationalPoint (s.guardSourceMinus E) := by
  exact rational_reflect (rational_guardMinus hE hs)

end Ulam165


/-! ==========================================================================
## Component: FreshArithmetic
========================================================================== -/

open scoped BigOperators
open Set

namespace Ulam165
open Sphere

/-- Fixed half-angle scale for the pins.  417/200 = 2.085 lies strictly
between 2.08 and 2.10. -/
def pinScale : ℚ := 417 / 200

lemma pinScale_pos : (0 : ℚ) < pinScale := by norm_num [pinScale]
lemma pinScale_gt_two : (2 : ℚ) < pinScale := by norm_num [pinScale]
lemma pinScale_lt_21_10 : pinScale < (21 : ℚ)/10 := by norm_num [pinScale]

/-- Real half-angle cosine, used for algebraic normalization of the rational
parameter family. -/
def halfCosR (r : ℝ) : ℝ := (1-r^2)/(1+r^2)
/-- Real half-angle sine. -/
def halfSinR (r : ℝ) : ℝ := (2*r)/(1+r^2)

lemma cast_qCos (r : ℚ) : ((qCos r : ℚ) : ℝ) = halfCosR (r : ℝ) := by
  norm_num [qCos, halfCosR]
lemma cast_qSin (r : ℚ) : ((qSin r : ℚ) : ℝ) = halfSinR (r : ℝ) := by
  norm_num [qSin, halfSinR]

lemma halfCos_sq_add_halfSin_sq (r : ℝ) :
    halfCosR r ^ 2 + halfSinR r ^ 2 = 1 := by
  unfold halfCosR halfSinR
  have h : 1+r^2 ≠ 0 := by positivity
  field_simp [h]
  ring

lemma halfCos_pos {r : ℝ} (hr : |r| < 1) : 0 < halfCosR r := by
  unfold halfCosR
  have hlo : -1 < r := neg_lt_of_abs_lt hr
  have hhi : r < 1 := lt_of_abs_lt hr
  have hp : 0 < (1-r)*(1+r) := mul_pos (by linarith) (by linarith)
  have hnum : 0 < 1-r^2 := by nlinarith
  have hden : 0 < 1+r^2 := by positivity
  positivity

lemma halfSin_pos {r : ℝ} (hr : 0 < r) : 0 < halfSinR r := by
  unfold halfSinR
  positivity

lemma halfCos_lt_one {r : ℝ} (hr : r ≠ 0) : halfCosR r < 1 := by
  unfold halfCosR
  have hr2 : 0 < r^2 := sq_pos_of_ne_zero hr
  have hden : 0 < 1+r^2 := by positivity
  rw [div_lt_one hden]
  nlinarith

lemma halfCos_mono_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    halfCosR b < halfCosR a := by
  unfold halfCosR
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have habsum : 0 < a+b := by nlinarith
  have hsprod : 0 < (b-a)*(a+b) := mul_pos (sub_pos.mpr hab) habsum
  have hsquares : a^2 < b^2 := by nlinarith
  have hda : 0 < 1+a^2 := by positivity
  have hdb : 0 < 1+b^2 := by positivity
  rw [div_lt_div_iff₀ hdb hda]
  nlinarith

/-- Exact record formula for a guard whose half-angle parameter is h/M. -/
lemma guard_record_formula
    {h M cb : ℝ} (hh : h ≠ 0) (hM : M ≠ 0)
    (hcb : cb = halfCosR (h/M)) :
    ((2-2*cb) + 4*h^2*cb) / (2-2*cb) = 1 + M^2 - h^2 := by
  rw [hcb]
  unfold halfCosR
  have hb : h/M ≠ 0 := div_ne_zero hh hM
  have hb2 : (h/M)^2 ≠ 0 := pow_ne_zero 2 hb
  have hden : 1+(h/M)^2 ≠ 0 := by positivity
  field_simp [hM, hh, hb, hb2, hden]
  ring

/-- Exact dimensionless pin parameter for the explicit half-angle family.
Here a=c h/M^2 and b=h/M. -/
lemma astar_formula
    {h M c ca cb : ℝ} (hh : h ≠ 0) (hM : M ≠ 0)
    (hca : ca = halfCosR (c*h/M^2))
    (hcb : cb = halfCosR (h/M)) :
    (2-2*ca) * (((2-2*cb)+4*h^2*cb)/(2-2*cb)) / (2-2*cb) =
      c^2 * (1+M^2-h^2) / M^2 *
        (1+h^2/M^2) / (1+c^2*h^2/M^4) := by
  rw [guard_record_formula hh hM hcb, hca, hcb]
  unfold halfCosR
  have hM2 : M^2 ≠ 0 := pow_ne_zero 2 hM
  have hb : h/M ≠ 0 := div_ne_zero hh hM
  have hb2 : (h/M)^2 ≠ 0 := pow_ne_zero 2 hb
  have hcah : 1+(c*h/M^2)^2 ≠ 0 := by positivity
  have hbh : 1+(h/M)^2 ≠ 0 := by positivity
  field_simp [hM, hM2, hh, hb, hb2, hcah, hbh]
  ring

/-- Exact worst pin--guard inverse ratio. -/
def worstPinGuardSq (s : ModuleScalars) : ℝ :=
  (2 - 2*s.cb*(s.ca*(1-2*s.h^2)-2*s.sa*s.h*s.t)) /
    (2 - 2*s.ca*s.cb)

/-- Closed-form gap between the new center--guard inverse record and the
worst pin--guard ratio for the explicit half-angle parameters. -/
lemma record_sub_worst_formula
    {h t M c ca sa cb : ℝ}
    (hh : h ≠ 0) (hM : M ≠ 0)
    (hca : ca = halfCosR (c*h/M^2))
    (hsa : sa = halfSinR (c*h/M^2))
    (hcb : cb = halfCosR (h/M)) :
    (1+M^2-h^2) -
      (2 - 2*cb*(ca*(1-2*h^2)-2*sa*h*t))/(2-2*ca*cb) =
      c*(M^2-h^2)*(M^2*(c-2*t)+c*h^2) /
        (M^2*(M^2+c^2)) := by
  rw [hca, hsa, hcb]
  have hM2 : M^2 ≠ 0 := pow_ne_zero 2 hM
  have hb : h/M ≠ 0 := div_ne_zero hh hM
  have hda : 1+(c*h/M^2)^2 ≠ 0 := by positivity
  have hdb : 1+(h/M)^2 ≠ 0 := by positivity
  have hsum : M^2+c^2 ≠ 0 := by
    have : 0 < M^2+c^2 := by positivity
    exact ne_of_gt this
  have habSum : (c*h/M^2)^2 + (h/M)^2 ≠ 0 := by
    have hb2pos : 0 < (h/M)^2 := sq_pos_of_ne_zero hb
    have ha2nonneg : 0 ≤ (c*h/M^2)^2 := sq_nonneg (c*h/M^2)
    nlinarith
  have hmainForm :
      2 - 2 * halfCosR (c*h/M^2) * halfCosR (h/M) =
        4 * ((c*h/M^2)^2 + (h/M)^2) /
          ((1+(c*h/M^2)^2) * (1+(h/M)^2)) := by
    unfold halfCosR
    field_simp [hda, hdb]
    ring
  rw [hmainForm]
  unfold halfCosR halfSinR
  field_simp [hM, hM2, hh, hb, hda, hdb, hsum, habSum]
  have hbig : M^2*h^2*c^2*2 + M^4*h^2*2 ≠ 0 := by
    have hM2pos : 0 < M^2 := sq_pos_of_ne_zero hM
    have hh2pos : 0 < h^2 := sq_pos_of_ne_zero hh
    have hsumpos : 0 < M^2 + c^2 := by positivity
    have heq : M^2*h^2*c^2*2 + M^4*h^2*2 = 2*M^2*h^2*(M^2+c^2) := by ring
    rw [heq]
    positivity
  field_simp [hbig]
  ring

/-- The exact algebraic gap has a uniform 1/8 margin in the range used by the
fresh-module construction. -/
lemma record_sub_worst_gt_eighth
    {h t M : ℝ}
    (hM2 : 99 ≤ M^2)
    (hh2 : h^2 < (1:ℝ)/256)
    (ht : t ≤ 1) :
    (1:ℝ)/8 <
      ((417:ℝ)/200)*(M^2-h^2)*
        (M^2*((417:ℝ)/200-2*t)+((417:ℝ)/200)*h^2) /
        (M^2*(M^2+((417:ℝ)/200)^2)) := by
  have hM2pos : 0 < M^2 := lt_of_lt_of_le (by norm_num) hM2
  have hMh : 0 < M^2-h^2 := by nlinarith
  have hc : 0 < (417:ℝ)/200 := by norm_num
  have hct : (17:ℝ)/200 ≤ (417:ℝ)/200 - 2*t := by nlinarith
  have hinner : M^2*((17:ℝ)/200) ≤
      M^2*((417:ℝ)/200-2*t)+((417:ℝ)/200)*h^2 := by
    have hh2nonneg : 0 ≤ h^2 := sq_nonneg h
    have hct0 : 0 ≤ (417:ℝ)/200 - 2*t := by linarith
    nlinarith [mul_nonneg hM2pos.le hct0]
  have hden : 0 < M^2*(M^2+((417:ℝ)/200)^2) := by positivity
  rw [lt_div_iff₀ hden]
  have hprod :
      ((417:ℝ)/200)*(M^2-h^2)*(M^2*((17:ℝ)/200)) ≤
      ((417:ℝ)/200)*(M^2-h^2)*
        (M^2*((417:ℝ)/200-2*t)+((417:ℝ)/200)*h^2) := by
    exact mul_le_mul_of_nonneg_left hinner (mul_nonneg hc.le hMh.le)
  have hbase :
      ((1:ℝ)/8) * (M^2*(M^2+((417:ℝ)/200)^2)) <
      ((417:ℝ)/200)*(M^2-h^2)*(M^2*((17:ℝ)/200)) := by
    have hhbound : h^2 < (1:ℝ)/256 := hh2
    nlinarith [sq_nonneg (M^2-99)]
  exact lt_of_lt_of_le hbase hprod

/-- Explicit rational module family.  Its center parameter is `s`; `M` fixes
how much the inverse record increases. -/
def freshScalars (s M : ℚ) : ModuleScalars :=
  let h := qSin s
  rationalModuleScalars s (pinScale*h/M^2) (h/M)

@[simp] lemma freshScalars_t (s M : ℚ) :
    (freshScalars s M).t = ((qCos s : ℚ) : ℝ) := rfl
@[simp] lemma freshScalars_h (s M : ℚ) :
    (freshScalars s M).h = ((qSin s : ℚ) : ℝ) := rfl
@[simp] lemma freshScalars_ca (s M : ℚ) :
    (freshScalars s M).ca = ((qCos (pinScale*qSin s/M^2) : ℚ) : ℝ) := rfl
@[simp] lemma freshScalars_sa (s M : ℚ) :
    (freshScalars s M).sa = ((qSin (pinScale*qSin s/M^2) : ℚ) : ℝ) := rfl
@[simp] lemma freshScalars_cb (s M : ℚ) :
    (freshScalars s M).cb = ((qCos (qSin s/M) : ℚ) : ℝ) := rfl
@[simp] lemma freshScalars_sb (s M : ℚ) :
    (freshScalars s M).sb = ((qSin (qSin s/M) : ℚ) : ℝ) := rfl

lemma freshScalars_rational (s M : ℚ) : RationalScalars (freshScalars s M) := by
  unfold freshScalars
  exact rationalModuleScalars_rational _ _ _

/-- Exact new squared inverse record of the explicit module. -/
lemma fresh_record_formula {s M : ℚ}
    (hs : qSin s ≠ 0) (hM : M ≠ 0) :
    let u := freshScalars s M
    ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb) =
      1 + (M:ℝ)^2 - ((qSin s:ℚ):ℝ)^2 := by
  dsimp only
  have hh : (((qSin s : ℚ) : ℝ)) ≠ 0 := by exact_mod_cast hs
  have hMr : (M:ℝ) ≠ 0 := by exact_mod_cast hM
  have hcb : (freshScalars s M).cb =
      halfCosR ((((qSin s : ℚ) : ℝ)) / (M:ℝ)) := by
    rw [freshScalars_cb, cast_qCos]
    congr 1
    norm_num
  exact guard_record_formula hh hMr hcb

/-- Picking M^2 in a short interval and a tiny nonzero center height gives the
paper's quantitative record increment. -/
lemma fresh_record_increment
    {B0sq : ℝ} {s M : ℚ}
    (hs : qSin s ≠ 0) (hM : M ≠ 0)
    (hMlow : B0sq - 1 + (5:ℝ)/256 < (M:ℝ)^2)
    (hMhigh : (M:ℝ)^2 < B0sq - 1 + (7:ℝ)/256)
    (hhsmall : ((qSin s:ℚ):ℝ)^2 < (1:ℝ)/256) :
    let u := freshScalars s M
    (1:ℝ)/64 <
      ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb) - B0sq ∧
    ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb) - B0sq < (1:ℝ)/32 := by
  dsimp only
  have hrec := fresh_record_formula (s:=s) (M:=M) hs hM
  change (1:ℝ)/64 <
      ((2-2*(freshScalars s M).cb)+4*(freshScalars s M).h^2*(freshScalars s M).cb) /
        (2-2*(freshScalars s M).cb) - B0sq ∧
    ((2-2*(freshScalars s M).cb)+4*(freshScalars s M).h^2*(freshScalars s M).cb) /
        (2-2*(freshScalars s M).cb) - B0sq < (1:ℝ)/32
  rw [hrec]
  constructor <;> nlinarith

/-- Existence of a rational M with its square in any prescribed positive open
square interval. -/
lemma exists_rat_sq_between {A B : ℝ}
    (hA : 0 ≤ A) (hAB : A < B) :
    ∃ M : ℚ, A < (M:ℝ)^2 ∧ (M:ℝ)^2 < B := by
  have hsqrt : Real.sqrt A < Real.sqrt B := by
    exact Real.sqrt_lt_sqrt hA hAB
  obtain ⟨M, hMl, hMu⟩ := exists_rat_btwn hsqrt
  refine ⟨M, ?_, ?_⟩
  · have hsA : (Real.sqrt A)^2 = A := Real.sq_sqrt hA
    have hsumpos : 0 < (M:ℝ) + Real.sqrt A := by
      have hsa : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
      linarith
    have hprod : 0 < ((M:ℝ) - Real.sqrt A) * ((M:ℝ) + Real.sqrt A) :=
      mul_pos (sub_pos.mpr hMl) hsumpos
    nlinarith
  · have hsB0 : 0 ≤ B := le_trans hA (le_of_lt hAB)
    have hsB : (Real.sqrt B)^2 = B := Real.sq_sqrt hsB0
    have hMnonneg : 0 ≤ (M:ℝ) := by
      have hsa : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
      linarith
    have hsumpos : 0 < Real.sqrt B + (M:ℝ) := by
      have hsb : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
      linarith
    have hprod : 0 < (Real.sqrt B - (M:ℝ)) * (Real.sqrt B + (M:ℝ)) :=
      mul_pos (sub_pos.mpr hMu) hsumpos
    nlinarith

/-- The short M-window needed at every fresh-module stage is nonempty. -/
lemma exists_record_parameter (B0sq : ℝ) (hB : 100 ≤ B0sq) :
    ∃ M : ℚ,
      B0sq - 1 + (5:ℝ)/256 < (M:ℝ)^2 ∧
      (M:ℝ)^2 < B0sq - 1 + (7:ℝ)/256 := by
  apply exists_rat_sq_between
  · nlinarith
  · norm_num

end Ulam165

namespace Ulam165
open Sphere

/-- Real counterpart of `rationalModuleScalars`, used only for the one-variable
continuity argument selecting a sufficiently small rational module. -/
def realModuleScalars (s a b : ℝ) : ModuleScalars where
  t := halfCosR s
  h := halfSinR s
  ca := halfCosR a
  sa := halfSinR a
  cb := halfCosR b
  sb := halfSinR b
  th_unit := halfCos_sq_add_halfSin_sq s
  a_unit := halfCos_sq_add_halfSin_sq a
  b_unit := halfCos_sq_add_halfSin_sq b

/-- Real one-parameter version of the explicit fresh module. -/
def freshScalarsR (s M : ℝ) : ModuleScalars :=
  let h := halfSinR s
  realModuleScalars s (((417:ℝ)/200)*h/M^2) (h/M)

@[simp] lemma freshScalarsR_zero (M : ℝ) :
    freshScalarsR 0 M = realModuleScalars 0 0 0 := by
  simp [freshScalarsR, halfSinR]

@[simp] lemma realModuleScalars_zero_t : (realModuleScalars 0 0 0).t = 1 := by
  norm_num [realModuleScalars, halfCosR]
@[simp] lemma realModuleScalars_zero_h : (realModuleScalars 0 0 0).h = 0 := by
  norm_num [realModuleScalars, halfSinR]
@[simp] lemma realModuleScalars_zero_ca : (realModuleScalars 0 0 0).ca = 1 := by
  norm_num [realModuleScalars, halfCosR]
@[simp] lemma realModuleScalars_zero_sa : (realModuleScalars 0 0 0).sa = 0 := by
  norm_num [realModuleScalars, halfSinR]
@[simp] lemma realModuleScalars_zero_cb : (realModuleScalars 0 0 0).cb = 1 := by
  norm_num [realModuleScalars, halfCosR]
@[simp] lemma realModuleScalars_zero_sb : (realModuleScalars 0 0 0).sb = 0 := by
  norm_num [realModuleScalars, halfSinR]

lemma center_zero (E : EqFrame d) :
    (realModuleScalars 0 0 0).center E = E.zeta := by
  ext <;> simp [ModuleScalars.center, EqFrame.zeta]
lemma pinPlus_zero (E : EqFrame d) :
    (realModuleScalars 0 0 0).pinPlus E = E.zeta := by
  ext <;> simp [ModuleScalars.pinPlus, EqFrame.zeta]
lemma pinMinus_zero (E : EqFrame d) :
    (realModuleScalars 0 0 0).pinMinus E = E.zeta := by
  ext <;> simp [ModuleScalars.pinMinus, EqFrame.zeta]
lemma guardPlus_zero (E : EqFrame d) :
    (realModuleScalars 0 0 0).guardPlus E = E.zeta := by
  ext <;> simp [ModuleScalars.guardPlus, EqFrame.zeta]
lemma guardMinus_zero (E : EqFrame d) :
    (realModuleScalars 0 0 0).guardMinus E = E.zeta := by
  ext <;> simp [ModuleScalars.guardMinus, EqFrame.zeta]
lemma guardSourcePlus_zero (E : EqFrame d) :
    (realModuleScalars 0 0 0).guardSourcePlus E = E.zeta := by
  rw [ModuleScalars.guardSourcePlus, guardPlus_zero]
  ext <;> simp [EqFrame.zeta, reflect]
lemma guardSourceMinus_zero (E : EqFrame d) :
    (realModuleScalars 0 0 0).guardSourceMinus E = E.zeta := by
  rw [ModuleScalars.guardSourceMinus, guardMinus_zero]
  ext <;> simp [EqFrame.zeta, reflect]

end Ulam165

/-! ==========================================================================
## Component: Initial
========================================================================== -/

open scoped BigOperators
open Set

namespace Ulam165
open Sphere

variable {d : ℕ}

lemma mem_anchorSources_iff {i0 : Fin d} {p : Sphere d} :
    p ∈ anchorSources d i0 ↔
      (∃ i : Fin d, p = epos i) ∨
      (∃ i : Fin d, p = eneg i) ∨
      p = south d ∨ p = anchorA i0 := by
  simp [anchorSources, eq_comm]

lemma self_ratio_le_hundred (x y : Sphere d) :
    distSq x y / distSq x y ≤ (100 : ℝ) := by
  by_cases h : distSq x y = 0
  · simp [h]
  · rw [div_self h]
    norm_num

lemma south_epos_inverse_ratio (i : Fin d) :
    distSq (south d) (epos i) / distSq (north d) (epos i) = 1 := by
  rw [distSq_comm (south d) (epos i), distSq_comm (north d) (epos i)]
  rw [distSq_south, distSq_north]
  simp [epos]

lemma south_eneg_inverse_ratio (i : Fin d) :
    distSq (south d) (eneg i) / distSq (north d) (eneg i) = 1 := by
  rw [distSq_comm (south d) (eneg i), distSq_comm (north d) (eneg i)]
  rw [distSq_south, distSq_north]
  simp [eneg]

lemma anchor_inverse_ratio_le_hundred (i0 : Fin d)
    {p q : Sphere d} (hp : p ∈ anchorSources d i0) (hq : q ∈ anchorSources d i0) :
    distSq p q / distSq (fold p) (fold q) ≤ (100 : ℝ) := by
  rw [mem_anchorSources_iff] at hp hq
  rcases hp with ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl | rfl <;>
    rcases hq with ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl | rfl
  · simpa [fold_epos] using self_ratio_le_hundred (epos i) (epos j)
  · simpa [fold_epos, fold_eneg] using self_ratio_le_hundred (epos i) (eneg j)
  · rw [fold_epos, fold_south,
        distSq_comm (epos i) (south d), distSq_comm (epos i) (north d),
        south_epos_inverse_ratio]
    norm_num
  · simpa [fold_epos, fold_anchorA] using self_ratio_le_hundred (epos i) (anchorA i0)
  · simpa [fold_eneg, fold_epos] using self_ratio_le_hundred (eneg i) (epos j)
  · simpa [fold_eneg] using self_ratio_le_hundred (eneg i) (eneg j)
  · rw [fold_eneg, fold_south,
        distSq_comm (eneg i) (south d), distSq_comm (eneg i) (north d),
        south_eneg_inverse_ratio]
    norm_num
  · simpa [fold_eneg, fold_anchorA] using self_ratio_le_hundred (eneg i) (anchorA i0)
  · rw [fold_south, fold_epos, south_epos_inverse_ratio]
    norm_num
  · rw [fold_south, fold_eneg, south_eneg_inverse_ratio]
    norm_num
  · simp [fold_south, distSq_self]
  · rw [fold_south, fold_anchorA, south_anchorA_inverse_ratio]
  · simpa [fold_anchorA, fold_epos] using self_ratio_le_hundred (anchorA i0) (epos j)
  · simpa [fold_anchorA, fold_eneg] using self_ratio_le_hundred (anchorA i0) (eneg j)
  · rw [fold_anchorA, fold_south,
        distSq_comm (anchorA i0) (south d), distSq_comm (anchorA i0) (north d),
        south_anchorA_inverse_ratio]
  · simpa [fold_anchorA] using self_ratio_le_hundred (anchorA i0) (anchorA i0)

/-- The initial fold graph has exactly the squared constants (1,100). -/
theorem initial_constants (i0 : Fin d) :
    forwardLipSq (foldGraph (anchorSources d i0)) = 1 ∧
    inverseLipSq (foldGraph (anchorSources d i0)) = 100 := by
  constructor
  · exact forwardLipSq_foldGraph_eq_one _ i0
      (epos_mem_anchorSources i0 i0) (eneg_mem_anchorSources i0 i0)
  · apply inverseLipSq_eq_of_bound_witness (by norm_num)
    · intro a ha b hb
      rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
      rcases List.mem_map.mp hb with ⟨q, hq, rfl⟩
      exact anchor_inverse_ratio_le_hundred i0 hp hq
    · exact foldGraph_mem (south_mem_anchorSources i0)
    · exact foldGraph_mem (anchorA_mem_anchorSources i0)
    · simpa [fold_south, fold_anchorA] using south_anchorA_inverse_ratio i0

/-- Every initial source has rational coordinates. -/
lemma anchorSources_rational (i0 : Fin d) :
    ∀ p ∈ anchorSources d i0, RationalPoint p := by
  intro p hp
  rw [mem_anchorSources_iff] at hp
  rcases hp with ⟨i,rfl⟩ | ⟨i,rfl⟩ | rfl | rfl
  · exact rational_epos i
  · exact rational_eneg i
  · exact rational_south
  · exact rational_anchorA i0

/-- The fixed accumulation point of modules can be chosen away from every
initial image. -/
lemma moduleZeta_not_initial_image (hd : 2 ≤ d) (i0 : Fin d) :
    moduleZeta d hd ∉ (anchorSources d i0).map fold := by
  intro hz
  rcases List.mem_map.mp hz with ⟨p,hp,hfold⟩
  rw [mem_anchorSources_iff] at hp
  rcases hp with ⟨i,rfl⟩ | ⟨i,rfl⟩ | rfl | rfl
  · rw [fold_epos] at hfold
    have hc := congrArg (fun x : Sphere d => x.1.1 (idx1 d hd)) hfold
    simp [moduleZeta, EqFrame.zeta, canonicalFrame, epos, idx0, idx1] at hc
    by_cases hi : i = idx1 d hd
    · subst hi; norm_num [idx1] at hc
    · have hni : idx1 d hd ≠ i := by exact fun h => hi h.symm
      have hidx : (⟨1, hd⟩ : Fin d) ≠ i := by simpa [idx1] using hni
      rw [if_neg hidx] at hc
      norm_num at hc
  · rw [fold_eneg] at hfold
    have hc := congrArg (fun x : Sphere d => x.1.1 (idx1 d hd)) hfold
    simp [moduleZeta, EqFrame.zeta, canonicalFrame, eneg, idx0, idx1] at hc
    by_cases hi : i = idx1 d hd
    · subst hi; norm_num [idx1] at hc
    · have hni : idx1 d hd ≠ i := by exact fun h => hi h.symm
      have hidx : (⟨1, hd⟩ : Fin d) ≠ i := by simpa [idx1] using hni
      rw [if_neg hidx] at hc
      norm_num at hc
  · rw [fold_south] at hfold
    have hc := congrArg (fun x : Sphere d => x.1.1 (idx1 d hd)) hfold
    norm_num [moduleZeta, EqFrame.zeta, canonicalFrame, north, idx0, idx1] at hc
  · rw [fold_anchorA] at hfold
    have hc := congrArg (fun x : Sphere d => x.1.1 (idx1 d hd)) hfold
    simp [moduleZeta, EqFrame.zeta, canonicalFrame, anchorA, idx0, idx1] at hc
    by_cases hi : i0 = idx1 d hd
    · subst hi; norm_num [idx1] at hc
    · have hni : idx1 d hd ≠ i0 := by exact fun h => hi h.symm
      have hidx : (⟨1, hd⟩ : Fin d) ≠ i0 := by simpa [idx1] using hni
      rw [if_neg hidx] at hc
      norm_num at hc

end Ulam165


/-! ==========================================================================
## Component: FreshModule
========================================================================== -/

open scoped BigOperators
open Set

namespace Ulam165
open Sphere

variable {d : ℕ}

/-- The four source points inserted before a module center. -/
def scaffoldSources (E : EqFrame d) (s : ModuleScalars) : List (Sphere d) :=
  [s.pinPlus E, s.pinMinus E, s.guardSourcePlus E, s.guardSourceMinus E]

/-- The complete five-source block. -/
def moduleSources (E : EqFrame d) (s : ModuleScalars) : List (Sphere d) :=
  scaffoldSources E s ++ [s.center E]

lemma pinPlus_mem_scaffoldSources (E : EqFrame d) (s : ModuleScalars) :
    s.pinPlus E ∈ scaffoldSources E s := by simp [scaffoldSources]
lemma pinMinus_mem_scaffoldSources (E : EqFrame d) (s : ModuleScalars) :
    s.pinMinus E ∈ scaffoldSources E s := by simp [scaffoldSources]
lemma guardSourcePlus_mem_scaffoldSources (E : EqFrame d) (s : ModuleScalars) :
    s.guardSourcePlus E ∈ scaffoldSources E s := by simp [scaffoldSources]
lemma guardSourceMinus_mem_scaffoldSources (E : EqFrame d) (s : ModuleScalars) :
    s.guardSourceMinus E ∈ scaffoldSources E s := by simp [scaffoldSources]

/-- Finite certificate sufficient for one full fresh-module step.  Its fields
are deliberately elementary: algebraic sign inequalities, finite inverse-ratio
bounds, rationality, and distinctness.  No conclusion about the greedy process
is stored in the certificate. -/
structure FreshModuleCertificate
    (src : List (Sphere d)) (i0 : Fin d) (B0sq Bsq : ℝ)
    (E : EqFrame d) (s : ModuleScalars) : Prop where
  B0_ge : 100 ≤ B0sq
  record_inc_low : (1:ℝ)/64 < Bsq-B0sq
  record_inc_high : Bsq-B0sq < (1:ℝ)/32
  ca_pos : 0 < s.ca
  cb_pos : 0 < s.cb
  cb_lt_ca : s.cb < s.ca
  d2_pos : 0 < 2-2*s.cb
  rho2_pos : 0 < 2-2*s.ca
  record_eq :
    ((2-2*s.cb)+4*s.h^2*s.cb)/(2-2*s.cb) = Bsq
  astar_upper :
    (2-2*s.ca) * Bsq / (2-2*s.cb) ≤ (441:ℝ)/100
  fold_pinPlus : fold (s.pinPlus E) = s.pinPlus E
  fold_pinMinus : fold (s.pinMinus E) = s.pinMinus E
  fold_guardPlus : fold (s.guardSourcePlus E) = s.guardPlus E
  fold_guardMinus : fold (s.guardSourceMinus E) = s.guardMinus E
  fold_center : fold (s.center E) = s.center E
  precenter_safe : FoldInverseSafe (src ++ scaffoldSources E s) B0sq
  full_safe : FoldInverseSafe (src ++ moduleSources E s) Bsq
  image_nodup : ((src ++ moduleSources E s).map fold).Nodup
  rational_pinPlus : RationalPoint (s.pinPlus E)
  rational_pinMinus : RationalPoint (s.pinMinus E)
  rational_guardSourcePlus : RationalPoint (s.guardSourcePlus E)
  rational_guardSourceMinus : RationalPoint (s.guardSourceMinus E)
  rational_center : RationalPoint (s.center E)

namespace FreshModuleCertificate

variable {src base : List (Sphere d)} {i0 : Fin d} {B0sq Bsq : ℝ}
  {E : EqFrame d} {s : ModuleScalars}

lemma Bsq_ge (C : FreshModuleCertificate src i0 B0sq Bsq E s) : 100 ≤ Bsq := by
  nlinarith [C.B0_ge, C.record_inc_low]

/-- Every source in the five-point fresh block has rational coordinates. -/
lemma moduleSources_rational
    (C : FreshModuleCertificate src i0 B0sq Bsq E s) :
    ∀ p ∈ moduleSources E s, RationalPoint p := by
  intro p hp
  simp [moduleSources, scaffoldSources] at hp
  rcases hp with (rfl | rfl | rfl | rfl | rfl)
  · exact C.rational_pinPlus
  · exact C.rational_pinMinus
  · exact C.rational_guardSourcePlus
  · exact C.rational_guardSourceMinus
  · exact C.rational_center

lemma scaffold_image_nodup (C : FreshModuleCertificate src i0 B0sq Bsq E s) :
    ((src ++ scaffoldSources E s).map fold).Nodup := by
  have hsplit : (src ++ moduleSources E s).map fold =
      (src ++ scaffoldSources E s).map fold ++ [fold (s.center E)] := by
    simp [moduleSources, scaffoldSources, List.map_append, List.append_assoc]
  have himg := C.image_nodup
  rw [hsplit] at himg
  exact (List.nodup_append.mp himg).1

lemma center_fresh_image (C : FreshModuleCertificate src i0 B0sq Bsq E s) :
    fold (s.center E) ∉ (src ++ scaffoldSources E s).map fold := by
  have hsplit : (src ++ moduleSources E s).map fold =
      (src ++ scaffoldSources E s).map fold ++ [fold (s.center E)] := by
    simp [moduleSources, List.map_append, List.append_assoc]
  have himg := C.image_nodup
  rw [hsplit] at himg
  have hdisj := (List.nodup_append.mp himg).2.2
  intro hmem
  exact (hdisj (fold (s.center E)) hmem (fold (s.center E)) (by simp)) rfl

lemma center_fresh_source (C : FreshModuleCertificate src i0 B0sq Bsq E s) :
    s.center E ∉ src ++ scaffoldSources E s := by
  intro h
  exact C.center_fresh_image (List.mem_map.mpr ⟨_,h,rfl⟩)

lemma scaffold_graph_embeds
    (C : FreshModuleCertificate src i0 B0sq Bsq E s) :
    ∀ a ∈ scaffoldGraph E s, a ∈ foldGraph (src ++ scaffoldSources E s) := by
  intro a ha
  simp [scaffoldGraph] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · have hm := foldGraph_mem (show s.pinPlus E ∈ src ++ scaffoldSources E s by
      simp [scaffoldSources])
    simpa [C.fold_pinPlus] using hm
  · have hm := foldGraph_mem (show s.pinMinus E ∈ src ++ scaffoldSources E s by
      simp [scaffoldSources])
    simpa [C.fold_pinMinus] using hm
  · have hm := foldGraph_mem (show s.guardSourcePlus E ∈ src ++ scaffoldSources E s by
      simp [scaffoldSources])
    simpa [C.fold_guardPlus] using hm
  · have hm := foldGraph_mem (show s.guardSourceMinus E ∈ src ++ scaffoldSources E s by
      simp [scaffoldSources])
    simpa [C.fold_guardMinus] using hm

lemma intended_center_forward
    (C : FreshModuleCertificate src i0 B0sq Bsq E s)
    (hpos : ∀ i : Fin d, epos i ∈ src)
    (hneg : ∀ i : Fin d, eneg i ∈ src) :
    forwardLipSq (candidateGraph (src ++ scaffoldSources E s)
      (s.center E) (s.center E)) = 1 := by
  have hfg := forwardLipSq_foldGraph_eq_one (src ++ scaffoldSources E s ++ [s.center E]) i0
    (by simp [hpos i0]) (by simp [hneg i0])
  rw [foldGraph_append_single] at hfg
  simpa [C.fold_center, List.append_assoc] using hfg

lemma intended_center_inverse
    (C : FreshModuleCertificate src i0 B0sq Bsq E s) :
    inverseLipSq (candidateGraph (src ++ scaffoldSources E s)
      (s.center E) (s.center E)) = Bsq := by
  have hEq : inverseLipSq (foldGraph ((src ++ scaffoldSources E s) ++ [s.center E])) = Bsq := by
    apply inverseLipSq_eq_of_bound_witness (by have := C.Bsq_ge; linarith)
    · intro a ha b hb
      rcases List.mem_map.mp ha with ⟨p,hp,rfl⟩
      rcases List.mem_map.mp hb with ⟨q,hq,rfl⟩
      exact C.full_safe p (by simpa [moduleSources, List.append_assoc] using hp)
        q (by simpa [moduleSources, List.append_assoc] using hq)
    · have hm := foldGraph_mem
          (src := (src ++ scaffoldSources E s) ++ [s.center E])
          (p := s.center E)
          (by simp [scaffoldSources])
      simpa [C.fold_center] using hm
    · have hm := foldGraph_mem
          (src := (src ++ scaffoldSources E s) ++ [s.center E])
          (p := s.guardSourcePlus E)
          (by simp [scaffoldSources])
      simpa [C.fold_guardPlus] using hm
    · have hnum := s.center_guardSourcePlus_distSq E
      have hden := s.center_guardPlus_distSq E
      change (s.center E).distSq (s.guardSourcePlus E) /
        (s.center E).distSq (s.guardPlus E) = Bsq
      rw [hnum, hden, C.record_eq]
  rw [foldGraph_append_single] at hEq
  simpa [C.fold_center] using hEq

/-- The module center is a unique greedy step once the scaffold has been
inserted. -/
theorem center_unique_greedy
    (C : FreshModuleCertificate src i0 B0sq Bsq E s)
    (hpos : ∀ i : Fin d, epos i ∈ src)
    (hneg : ∀ i : Fin d, eneg i ∈ src) :
    UniqueGreedyStep (src ++ scaffoldSources E s) (s.center E) (fold (s.center E)) := by
  rw [C.fold_center]
  have hF := C.intended_center_forward hpos hneg
  have hI := C.intended_center_inverse
  refine ⟨C.center_fresh_source, ?_, ?_⟩
  · simpa [ImageAdmissible, C.fold_center] using C.center_fresh_image
  · intro y hyadm hyne
    have hyGp : y ≠ s.guardPlus E := by
      intro h
      subst h
      apply hyadm
      exact List.mem_map.mpr ⟨s.guardSourcePlus E, by simp [scaffoldSources], C.fold_guardPlus⟩
    have hyGm : y ≠ s.guardMinus E := by
      intro h
      subst h
      apply hyadm
      exact List.mem_map.mpr ⟨s.guardSourceMinus E, by simp [scaffoldSources], C.fold_guardMinus⟩
    have hsc : ∀ a ∈ scaffoldGraph E s,
        a ∈ candidateGraph (src ++ scaffoldSources E s) (s.center E) y := by
      intro a ha
      exact oldGraph_mem_candidate (C.scaffold_graph_embeds a ha)
    have hcenter : (s.center E,y) ∈
        candidateGraph (src ++ scaffoldSources E s) (s.center E) y :=
      candidate_new_mem _ _ _
    have hrad := exact_module_radial_lower E s
      (candidateGraph (src ++ scaffoldSources E s) (s.center E) y) y
      hsc hcenter hyne hyGp hyGm C.ca_pos C.cb_pos C.cb_lt_ca
      C.d2_pos C.rho2_pos (by rw [C.record_eq]; exact C.Bsq_ge)
      (by rw [C.record_eq]; exact C.astar_upper)
    have hintended :
        greedyCost (candidateGraph (src ++ scaffoldSources E s)
          (s.center E) (s.center E)) = 1 + Real.sqrt Bsq := by
      unfold greedyCost
      rw [hF,hI]
      norm_num
    rw [hintended]
    simpa [C.record_eq] using hrad

/-- Applying a certified five-point module preserves the fold graph, makes all
five choices uniquely greedy, and raises the exact squared inverse record from
B0sq to Bsq. -/
theorem apply_fresh_module
    (C : FreshModuleCertificate src i0 B0sq Bsq E s)
    (hbuilt : GreedyBuiltFrom base src)
    (hpos : ∀ i : Fin d, epos i ∈ src)
    (hneg : ∀ i : Fin d, eneg i ∈ src)
    (hsouth : south d ∈ src)
    (ha : anchorA i0 ∈ src)
    (holdInv : inverseLipSq (foldGraph src) = B0sq) :
    GreedyBuiltFrom base (src ++ moduleSources E s) ∧
      inverseLipSq (foldGraph (src ++ moduleSources E s)) = Bsq := by
  have hsc := append_fold_block_greedily i0 B0sq hbuilt hpos hneg hsouth ha
    holdInv C.B0_ge C.precenter_safe C.scaffold_image_nodup
  rcases hsc with ⟨hbuiltSc, hinvSc⟩
  have hcenter := C.center_unique_greedy hpos hneg
  have hbuiltAll : GreedyBuiltFrom base
      ((src ++ scaffoldSources E s) ++ [s.center E]) :=
    GreedyBuiltFrom.step hbuiltSc hcenter
  have hinvAll : inverseLipSq
      (foldGraph ((src ++ scaffoldSources E s) ++ [s.center E])) = Bsq := by
    rw [foldGraph_append_single]
    simpa [C.fold_center] using C.intended_center_inverse
  constructor
  · simpa [moduleSources, List.append_assoc] using hbuiltAll
  · simpa [moduleSources, List.append_assoc] using hinvAll

end FreshModuleCertificate

end Ulam165


/-! ==========================================================================
## Component: FreshLocal
========================================================================== -/

open scoped BigOperators Topology
open Set Filter

namespace Ulam165
open Sphere

variable {d : ℕ}

lemma halfSinR_lt_two_mul {r : ℝ} (hr : 0 < r) :
    halfSinR r < 2*r := by
  unfold halfSinR
  have hden : 1 < 1+r^2 := by nlinarith [sq_pos_of_pos hr]
  have h2r : 0 < 2*r := by positivity
  rw [div_lt_iff₀ (by linarith : 0 < 1+r^2)]
  nlinarith

lemma halfCosR_pos_of_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < halfCosR r := by
  apply halfCos_pos
  rw [abs_of_nonneg hr0]
  exact hr1

lemma halfCosR_le_one (r : ℝ) : halfCosR r ≤ 1 := by
  unfold halfCosR
  have hd : 0 < 1+r^2 := by positivity
  rw [div_le_one hd]
  nlinarith [sq_nonneg r]

lemma halfSinR_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ halfSinR r := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · norm_num [halfSinR]
  · exact (halfSin_pos hr).le

/-- Small positive rational center parameters give a small positive height and
positive horizontal cosine. -/
lemma small_center_parameters {s : ℚ}
    (hs0 : 0 < s) (hs1 : s < 1/100) :
    let h : ℝ := ((qSin s : ℚ) : ℝ)
    let t : ℝ := ((qCos s : ℚ) : ℝ)
    0 < h ∧ h < (1:ℝ)/50 ∧ h^2 < (1:ℝ)/2500 ∧
      0 < t ∧ t < 1 := by
  dsimp
  have hs0r : (0:ℝ) < (s:ℝ) := by
    exact_mod_cast hs0
  have hs1r : (s:ℝ) < (1:ℝ)/100 := by
    calc
      (s:ℝ) < (((1:ℚ)/100 : ℚ) : ℝ) := by exact_mod_cast hs1
      _ = (1:ℝ)/100 := by norm_num
  rw [cast_qSin, cast_qCos]
  have hhpos : 0 < halfSinR (s:ℝ) := halfSin_pos hs0r
  have hhlt : halfSinR (s:ℝ) < 2*(s:ℝ) := halfSinR_lt_two_mul hs0r
  have hslt1 : (s:ℝ) < 1 := by linarith
  have htpos : 0 < halfCosR (s:ℝ) :=
    halfCosR_pos_of_lt_one hs0r.le hslt1
  have htlt : halfCosR (s:ℝ) < 1 :=
    halfCos_lt_one (by exact_mod_cast (ne_of_gt hs0))
  constructor
  · exact hhpos
  constructor
  · linarith
  constructor
  · nlinarith
  · exact ⟨htpos,htlt⟩

/-- The record parameter selected from the short square interval is positive
and in particular much larger than the fixed pin scale. -/
lemma record_parameter_bounds {B0sq : ℝ} {M : ℚ}
    (hB : 100 ≤ B0sq)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (hMpos : 0 < M) :
    99 < (M:ℝ)^2 ∧ (9:ℝ) < (M:ℝ) ∧ ((417:ℝ)/200) < (M:ℝ) := by
  have h99 : 99 < (M:ℝ)^2 := by nlinarith
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hMpos
  have hM9 : (9:ℝ) < (M:ℝ) := by nlinarith [sq_nonneg ((M:ℝ)-9)]
  constructor
  · exact h99
  constructor
  · exact hM9
  · norm_num at *
    linarith

/-- Positivity and ordering of the two module half-angle parameters. -/
lemma fresh_halfangle_order
    {B0sq : ℝ} {s M : ℚ}
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2) :
    let a : ℝ := ((pinScale*qSin s/M^2 : ℚ) : ℝ)
    let b : ℝ := ((qSin s/M : ℚ) : ℝ)
    0 < a ∧ a < b ∧ b < 1 := by
  dsimp
  obtain ⟨hh,hh50,hh2,ht,ht1⟩ := small_center_parameters hs0 hs1
  obtain ⟨hM2,hM9,hMc⟩ := record_parameter_bounds hB hMl hMpos
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hMpos
  have hc : 0 < (417:ℝ)/200 := by norm_num
  have haeq : ((pinScale*qSin s/M^2 : ℚ) : ℝ) =
      ((417:ℝ)/200) * ((qSin s:ℚ):ℝ) / (M:ℝ)^2 := by
    norm_num [pinScale]
  have hbeq : ((qSin s/M : ℚ) : ℝ) =
      ((qSin s:ℚ):ℝ)/(M:ℝ) := by norm_num
  rw [haeq,hbeq]
  have hapos : 0 < ((417:ℝ)/200) * ((qSin s:ℚ):ℝ) / (M:ℝ)^2 := by positivity
  have hab : ((417:ℝ)/200) * ((qSin s:ℚ):ℝ) / (M:ℝ)^2 <
      ((qSin s:ℚ):ℝ)/(M:ℝ) := by
    rw [div_lt_div_iff₀ (sq_pos_of_pos hMr) hMr]
    have hhpos : 0 < ((qSin s:ℚ):ℝ) := hh
    have hprodpos : 0 < ((M:ℝ) - (417:ℝ)/200) * ((qSin s:ℚ):ℝ) :=
      mul_pos (sub_pos.mpr hMc) hhpos
    nlinarith
  have hb1 : ((qSin s:ℚ):ℝ)/(M:ℝ) < 1 := by
    rw [div_lt_one hMr]
    linarith
  exact ⟨hapos,hab,hb1⟩

/-- The scalar inequalities required by exact module minimization. -/
lemma fresh_scalar_geometry
    {B0sq : ℝ} {s M : ℚ}
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2) :
    let u := freshScalars s M
    0 < u.ca ∧ 0 < u.cb ∧ u.cb < u.ca ∧
      0 < 2-2*u.cb ∧ 0 < 2-2*u.ca := by
  dsimp
  obtain ⟨ha,hab,hb1⟩ := fresh_halfangle_order hB hs0 hs1 hMpos hMl
  have hb0 : 0 < ((qSin s/M:ℚ):ℝ) := lt_trans ha hab
  have ha1 : ((pinScale*qSin s/M^2:ℚ):ℝ) < 1 := lt_trans hab hb1
  rw [cast_qCos, cast_qCos]
  have hcap : 0 < halfCosR ((pinScale*qSin s/M^2:ℚ):ℝ) :=
    halfCosR_pos_of_lt_one ha.le ha1
  have hcbp : 0 < halfCosR ((qSin s/M:ℚ):ℝ) :=
    halfCosR_pos_of_lt_one hb0.le hb1
  have horder : halfCosR ((qSin s/M:ℚ):ℝ) <
      halfCosR ((pinScale*qSin s/M^2:ℚ):ℝ) :=
    halfCos_mono_pos ha.le hab
  have hcalt : halfCosR ((pinScale*qSin s/M^2:ℚ):ℝ) < 1 :=
    halfCos_lt_one (ne_of_gt ha)
  have hcblt : halfCosR ((qSin s/M:ℚ):ℝ) < 1 :=
    halfCos_lt_one (ne_of_gt hb0)
  exact ⟨hcap,hcbp,horder,by linarith,by linarith⟩

/-- Both pins, both guard targets and the center lie strictly in the northern
hemisphere for the quantitative fresh family. -/
lemma fresh_northern
    (hd : 2 ≤ d) {B0sq : ℝ} {s M : ℚ}
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2) :
    let E := canonicalFrame d hd
    let u := freshScalars s M
    0 < (u.center E).1.2 ∧
      0 < (u.pinPlus E).1.2 ∧ 0 < (u.pinMinus E).1.2 ∧
      0 < (u.guardPlus E).1.2 ∧ 0 < (u.guardMinus E).1.2 := by
  dsimp
  obtain ⟨hh,hh50,hh2,ht,ht1⟩ := small_center_parameters hs0 hs1
  obtain ⟨hM2,hM9,hMc⟩ := record_parameter_bounds hB hMl hMpos
  obtain ⟨ha,hab,hb1⟩ := fresh_halfangle_order hB hs0 hs1 hMpos hMl
  obtain ⟨hca,hcb,hcbca,hd2,hr2⟩ := fresh_scalar_geometry hB hs0 hs1 hMpos hMl
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hMpos
  have ha_small : ((pinScale*qSin s/M^2:ℚ):ℝ) < (1:ℝ)/100 := by
    have haeq : ((pinScale*qSin s/M^2:ℚ):ℝ) =
        ((417:ℝ)/200)*((qSin s:ℚ):ℝ)/(M:ℝ)^2 := by norm_num [pinScale]
    rw [haeq]
    have : ((qSin s:ℚ):ℝ) < 1/50 := hh50
    have : 99 < (M:ℝ)^2 := hM2
    have hc : (0:ℝ) < 417/200 := by norm_num
    rw [div_lt_iff₀ (by positivity : 0 < (M:ℝ)^2)]
    nlinarith
  have hsa_bound : (freshScalars s M).sa < 2*((pinScale*qSin s/M^2:ℚ):ℝ) := by
    rw [freshScalars_sa, cast_qSin]
    exact halfSinR_lt_two_mul ha
  have hca_lower : (9:ℝ)/10 < (freshScalars s M).ca := by
    rw [freshScalars_ca, cast_qCos]
    unfold halfCosR
    have hden : 0 < 1+((pinScale*qSin s/M^2:ℚ):ℝ)^2 := by positivity
    rw [lt_div_iff₀ hden]
    nlinarith [sq_nonneg (((pinScale*qSin s/M^2:ℚ):ℝ))]
  have hpinminus : 0 < (freshScalars s M).ca*((qSin s:ℚ):ℝ) -
      (freshScalars s M).sa*((qCos s:ℚ):ℝ) := by
    have hsa_nonneg : 0 ≤ (freshScalars s M).sa := by
      rw [freshScalars_sa, cast_qSin]
      exact halfSinR_nonneg ha.le
    have ht_le : ((qCos s:ℚ):ℝ) ≤ 1 := by
      rw [cast_qCos]
      exact halfCosR_le_one _
    have hprod : (freshScalars s M).sa*((qCos s:ℚ):ℝ) ≤
        2*((pinScale*qSin s/M^2:ℚ):ℝ) := by
      calc
        _ ≤ (freshScalars s M).sa * 1 :=
          mul_le_mul_of_nonneg_left ht_le hsa_nonneg
        _ ≤ 2*((pinScale*qSin s/M^2:ℚ):ℝ) := by exact le_of_lt (by simpa using hsa_bound)
    have hleft : (9:ℝ)/10*((qSin s:ℚ):ℝ) <
        (freshScalars s M).ca*((qSin s:ℚ):ℝ) := by
      exact mul_lt_mul_of_pos_right hca_lower hh
    have hratio : 2*((pinScale*qSin s/M^2:ℚ):ℝ) <
        (1:ℝ)/20*((qSin s:ℚ):ℝ) := by
      have haeq : ((pinScale*qSin s/M^2:ℚ):ℝ) =
          ((417:ℝ)/200)*((qSin s:ℚ):ℝ)/(M:ℝ)^2 := by norm_num [pinScale]
      rw [haeq]
      have hM2pos : 0 < (M:ℝ)^2 := by positivity
      have hcoef : 2*((417:ℝ)/200)/(M:ℝ)^2 < (1:ℝ)/20 := by
        rw [div_lt_iff₀ hM2pos]
        nlinarith
      calc
        2 * (((417:ℝ)/200) * ((qSin s:ℚ):ℝ) / (M:ℝ)^2) =
            (2*((417:ℝ)/200)/(M:ℝ)^2) * ((qSin s:ℚ):ℝ) := by ring
        _ < (1:ℝ)/20 * ((qSin s:ℚ):ℝ) :=
          mul_lt_mul_of_pos_right hcoef hh
    nlinarith
  have hpinplus : 0 < (freshScalars s M).ca*((qSin s:ℚ):ℝ) +
      (freshScalars s M).sa*((qCos s:ℚ):ℝ) := by
    have hsa : 0 < (freshScalars s M).sa := by
      rw [freshScalars_sa, cast_qSin]
      exact halfSin_pos ha
    positivity
  have hguard : 0 < (freshScalars s M).cb*((qSin s:ℚ):ℝ) := by positivity
  simpa [ModuleScalars.center_last, ModuleScalars.pinPlus_last,
    ModuleScalars.pinMinus_last, ModuleScalars.guardPlus_last,
    ModuleScalars.guardMinus_last] using
      And.intro hh (And.intro hpinplus (And.intro hpinminus (And.intro hguard hguard)))

/-- Consequently the intended targets are exactly the fold images. -/
lemma fresh_fold_identities
    {B0sq : ℝ} {s M : ℚ} (hd : 2 ≤ d)
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2) :
    let E := canonicalFrame d hd
    let u := freshScalars s M
    fold (u.pinPlus E) = u.pinPlus E ∧
    fold (u.pinMinus E) = u.pinMinus E ∧
    fold (u.guardSourcePlus E) = u.guardPlus E ∧
    fold (u.guardSourceMinus E) = u.guardMinus E ∧
    fold (u.center E) = u.center E := by
  dsimp
  have hn := fresh_northern (d:=d) hd hB hs0 hs1 hMpos hMl
  rcases hn with ⟨hc,hpp,hpm,hgp,hgm⟩
  constructor
  · exact fold_eq_self_of_nonneg hpp.le
  constructor
  · exact fold_eq_self_of_nonneg hpm.le
  constructor
  · rw [ModuleScalars.guardSourcePlus, fold_reflect]
    exact fold_eq_self_of_nonneg hgp.le
  constructor
  · rw [ModuleScalars.guardSourceMinus, fold_reflect]
    exact fold_eq_self_of_nonneg hgm.le
  · exact fold_eq_self_of_nonneg hc.le

/-- The exact module record has the desired 1/64--1/32 increment. -/
lemma fresh_record_data
    {B0sq : ℝ} {s M : ℚ}
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (hMu : (M:ℝ)^2 < B0sq-1+(7:ℝ)/256) :
    let u := freshScalars s M
    let Bsq := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
    (1:ℝ)/64 < Bsq-B0sq ∧ Bsq-B0sq < (1:ℝ)/32 ∧ 100 < Bsq := by
  dsimp
  obtain ⟨hh,hh50,hh2,ht,ht1⟩ := small_center_parameters hs0 hs1
  have hsine : qSin s ≠ 0 := by
    have hr : ((qSin s:ℚ):ℝ) ≠ 0 := ne_of_gt hh
    exact_mod_cast hr
  have hMne : M ≠ 0 := ne_of_gt hMpos
  have hinc := fresh_record_increment hsine hMne hMl hMu (by nlinarith [hh2])
  rcases hinc with ⟨hl,hu⟩
  have h100 : 100 <
      ((2-2*(freshScalars s M).cb)+4*(freshScalars s M).h^2*(freshScalars s M).cb) /
        (2-2*(freshScalars s M).cb) := by
    nlinarith
  exact ⟨hl,hu,by simpa using h100⟩

/-- The dimensionless pin parameter stays below 2.10^2. -/
lemma fresh_astar_upper
    {B0sq : ℝ} {s M : ℚ}
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (hMu : (M:ℝ)^2 < B0sq-1+(7:ℝ)/256) :
    let u := freshScalars s M
    let Bsq := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
    (2-2*u.ca)*Bsq/(2-2*u.cb) ≤ (441:ℝ)/100 := by
  dsimp
  obtain ⟨hh,hh50,hh2,ht,ht1⟩ := small_center_parameters hs0 hs1
  obtain ⟨hM2,hM9,hMc⟩ := record_parameter_bounds hB hMl hMpos
  have hsine : qSin s ≠ 0 := by
    have hr : ((qSin s:ℚ):ℝ) ≠ 0 := ne_of_gt hh
    exact_mod_cast hr
  have hMne : M ≠ 0 := ne_of_gt hMpos
  have hca : (freshScalars s M).ca =
      halfCosR (((417:ℝ)/200)*((qSin s:ℚ):ℝ)/(M:ℝ)^2) := by
    rw [freshScalars_ca, cast_qCos]
    congr 2
    norm_num [pinScale]
  have hcb : (freshScalars s M).cb =
      halfCosR (((qSin s:ℚ):ℝ)/(M:ℝ)) := by
    rw [freshScalars_cb, cast_qCos]
    congr 2
    norm_num
  change (2-2*(freshScalars s M).ca) *
      (((2-2*(freshScalars s M).cb)+4*(freshScalars s M).h^2*(freshScalars s M).cb) /
        (2-2*(freshScalars s M).cb)) /
      (2-2*(freshScalars s M).cb) ≤ (441:ℝ)/100
  rw [freshScalars_h]
  rw [astar_formula (by exact_mod_cast hsine) (by exact_mod_cast hMne) hca hcb]
  have hBnew : 1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2 <
      B0sq + (7:ℝ)/256 := by nlinarith
  have hM2pos : 0 < (M:ℝ)^2 := by positivity
  have hsmallratio : ((qSin s:ℚ):ℝ)^2/(M:ℝ)^2 < (1:ℝ)/200000 := by
    rw [div_lt_iff₀ hM2pos]
    nlinarith [hM2, hh2]
  have hc2 : ((417:ℝ)/200)^2 < (435:ℝ)/100 := by norm_num
  have hratioM :
      (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2 < (1011:ℝ)/1000 := by
    rw [div_lt_iff₀ hM2pos]
    nlinarith [hM2, sq_nonneg ((qSin s:ℚ):ℝ)]
  have hratioM_pos : 0 <
      (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2 := by
    apply div_pos
    · nlinarith [hM2, hh2]
    · exact hM2pos
  have hfactor1 :
      ((417:ℝ)/200)^2 * (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2 <
      (435:ℝ)/100 * ((1011:ℝ)/1000) := by
    have h1 :
        ((417:ℝ)/200)^2 *
            ((1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2) <
          (435:ℝ)/100 *
            ((1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2) :=
      mul_lt_mul_of_pos_right hc2 hratioM_pos
    have h2 :
        (435:ℝ)/100 *
            ((1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2) <
          (435:ℝ)/100 * ((1011:ℝ)/1000) :=
      mul_lt_mul_of_pos_left hratioM (by norm_num)
    have hnorm :
        ((417:ℝ)/200)^2 * (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2 =
          ((417:ℝ)/200)^2 *
            ((1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2) := by ring
    rw [hnorm]
    exact lt_trans h1 h2
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hMpos
  have hM4pos : 0 < (M:ℝ)^4 := pow_pos hMr 4
  have hfactor2 :
      (1+((qSin s:ℚ):ℝ)^2/(M:ℝ)^2) /
        (1+((417:ℝ)/200)^2*((qSin s:ℚ):ℝ)^2/(M:ℝ)^4) ≤
      1+((qSin s:ℚ):ℝ)^2/(M:ℝ)^2 := by
    let N : ℝ := 1+((qSin s:ℚ):ℝ)^2/(M:ℝ)^2
    let D : ℝ := 1+((417:ℝ)/200)^2*((qSin s:ℚ):ℝ)^2/(M:ℝ)^4
    have hratioNonneg : 0 ≤ ((qSin s:ℚ):ℝ)^2/(M:ℝ)^2 :=
      div_nonneg (sq_nonneg _) hM2pos.le
    have hN : 0 ≤ N := by dsimp [N]; linarith
    have hterm : 0 ≤ ((417:ℝ)/200)^2*((qSin s:ℚ):ℝ)^2/(M:ℝ)^4 := by
      apply div_nonneg
      · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
      · exact hM4pos.le
    have hD : 1 ≤ D := by dsimp [D]; linarith
    have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
    change N / D ≤ N
    rw [div_le_iff₀ hDpos]
    have hDm1 : 0 ≤ D - 1 := by linarith
    nlinarith [mul_nonneg hN hDm1]
  have hfactor2b : 1+((qSin s:ℚ):ℝ)^2/(M:ℝ)^2 < (200001:ℝ)/200000 := by
    linarith
  have hc2nonneg : 0 ≤ ((417:ℝ)/200)^2 := sq_nonneg _
  have hpos1 : 0 ≤
      ((417:ℝ)/200)^2 * (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2 := by
    have hp : 0 ≤ ((417:ℝ)/200)^2 *
        ((1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2) :=
      mul_nonneg hc2nonneg hratioM_pos.le
    have hnorm :
        ((417:ℝ)/200)^2 * (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2 =
          ((417:ℝ)/200)^2 *
            ((1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2) := by ring
    rw [hnorm]
    exact hp
  have hNpos : 0 < 1+((qSin s:ℚ):ℝ)^2/(M:ℝ)^2 := by
    have hr0 : 0 ≤ ((qSin s:ℚ):ℝ)^2/(M:ℝ)^2 :=
      div_nonneg (sq_nonneg _) hM2pos.le
    linarith
  have hstep1 :
      ((417:ℝ)/200)^2 * (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2 *
          (1+((qSin s:ℚ):ℝ)^2/(M:ℝ)^2) /
            (1+((417:ℝ)/200)^2*((qSin s:ℚ):ℝ)^2/(M:ℝ)^4) ≤
      ((417:ℝ)/200)^2 * (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2 *
          (1+((qSin s:ℚ):ℝ)^2/(M:ℝ)^2) := by
    have hnorm :
        ((417:ℝ)/200)^2 * (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2 *
            (1+((qSin s:ℚ):ℝ)^2/(M:ℝ)^2) /
              (1+((417:ℝ)/200)^2*((qSin s:ℚ):ℝ)^2/(M:ℝ)^4) =
        (((417:ℝ)/200)^2 * (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2) *
          ((1+((qSin s:ℚ):ℝ)^2/(M:ℝ)^2) /
            (1+((417:ℝ)/200)^2*((qSin s:ℚ):ℝ)^2/(M:ℝ)^4)) := by ring
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hfactor2 hpos1
  have hstep2 :
      ((417:ℝ)/200)^2 * (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2 *
          (1+((qSin s:ℚ):ℝ)^2/(M:ℝ)^2) <
      ((435:ℝ)/100 * (1011:ℝ)/1000) * ((200001:ℝ)/200000) := by
    have h2a :
        ((417:ℝ)/200)^2 * (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2 *
            (1+((qSin s:ℚ):ℝ)^2/(M:ℝ)^2) <
        ((435:ℝ)/100 * (1011:ℝ)/1000) *
            (1+((qSin s:ℚ):ℝ)^2/(M:ℝ)^2) :=
      mul_lt_mul_of_pos_right (by
        calc
          ((417:ℝ)/200)^2 * (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2
              < (435:ℝ)/100 * ((1011:ℝ)/1000) := hfactor1
          _ = (435:ℝ)/100 * (1011:ℝ)/1000 := by ring) hNpos
    have h2b :
        ((435:ℝ)/100 * (1011:ℝ)/1000) *
            (1+((qSin s:ℚ):ℝ)^2/(M:ℝ)^2) <
        ((435:ℝ)/100 * (1011:ℝ)/1000) * ((200001:ℝ)/200000) :=
      mul_lt_mul_of_pos_left hfactor2b (by norm_num)
    exact lt_trans h2a h2b
  apply le_of_lt
  calc
    ((417:ℝ)/200)^2 * (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2 *
        (1+((qSin s:ℚ):ℝ)^2/(M:ℝ)^2) /
          (1+((417:ℝ)/200)^2*((qSin s:ℚ):ℝ)^2/(M:ℝ)^4)
        ≤ ((417:ℝ)/200)^2 * (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2)/(M:ℝ)^2 *
          (1+((qSin s:ℚ):ℝ)^2/(M:ℝ)^2) := hstep1
    _ < ((435:ℝ)/100 * (1011:ℝ)/1000) * ((200001:ℝ)/200000) := hstep2
    _ < (441:ℝ)/100 := by norm_num

/-- The worst pin--guard inverse ratio stays strictly below the old record. -/
lemma fresh_worst_pin_guard_lt_old
    {B0sq : ℝ} {s M : ℚ}
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (hMu : (M:ℝ)^2 < B0sq-1+(7:ℝ)/256) :
    let u := freshScalars s M
    worstPinGuardSq u < B0sq := by
  dsimp only
  obtain ⟨hh,hh50,hh2,ht,ht1⟩ := small_center_parameters hs0 hs1
  obtain ⟨hM2,hM9,hMc⟩ := record_parameter_bounds hB hMl hMpos
  have hsine : qSin s ≠ 0 := by
    have hr : ((qSin s:ℚ):ℝ) ≠ 0 := ne_of_gt hh
    exact_mod_cast hr
  have hMne : M ≠ 0 := ne_of_gt hMpos
  have hca : (freshScalars s M).ca =
      halfCosR (((417:ℝ)/200)*((qSin s:ℚ):ℝ)/(M:ℝ)^2) := by
    rw [freshScalars_ca, cast_qCos]
    congr 2
    norm_num [pinScale]
  have hsa : (freshScalars s M).sa =
      halfSinR (((417:ℝ)/200)*((qSin s:ℚ):ℝ)/(M:ℝ)^2) := by
    rw [freshScalars_sa, cast_qSin]
    congr 2
    norm_num [pinScale]
  have hcb : (freshScalars s M).cb =
      halfCosR (((qSin s:ℚ):ℝ)/(M:ℝ)) := by
    rw [freshScalars_cb, cast_qCos]
    congr 2
    norm_num
  have hgap := record_sub_worst_formula
    (h:=((qSin s:ℚ):ℝ)) (t:=((qCos s:ℚ):ℝ))
    (M:=(M:ℝ)) (c:=(417:ℝ)/200)
    (ca:=(freshScalars s M).ca) (sa:=(freshScalars s M).sa)
    (cb:=(freshScalars s M).cb)
    (by exact_mod_cast hsine) (by exact_mod_cast hMne) hca hsa hcb
  have hgap8 := record_sub_worst_gt_eighth
    (h:=((qSin s:ℚ):ℝ)) (t:=((qCos s:ℚ):ℝ)) (M:=(M:ℝ))
    (by linarith) (by nlinarith [hh2]) (by linarith)
  have hrec := fresh_record_data hB hs0 hs1 hMpos hMl hMu
  rcases hrec with ⟨hincL,hincU,hnew100⟩
  have hrecordEq := fresh_record_formula hsine hMne
  dsimp at hrecordEq hincL hincU hnew100
  rw [hrecordEq] at hincL hincU hnew100
  change worstPinGuardSq (freshScalars s M) < B0sq
  unfold worstPinGuardSq
  rw [freshScalars_h, freshScalars_t]
  have hWgap : (1+(M:ℝ)^2-((qSin s:ℚ):ℝ)^2) -
      ((2 - 2*(freshScalars s M).cb*
        ((freshScalars s M).ca*(1-2*((qSin s:ℚ):ℝ)^2) -
          2*(freshScalars s M).sa*((qSin s:ℚ):ℝ)*((qCos s:ℚ):ℝ))) /
        (2-2*(freshScalars s M).ca*(freshScalars s M).cb)) > (1:ℝ)/8 := by
    nlinarith [hgap, hgap8]
  nlinarith [hWgap, hincU]

end Ulam165

/-! ==========================================================================
## Component: FreshExistenceBridge

This section isolates the only genuinely global finite-stage input still
needed for a fresh module: old--new inverse safety and image avoidance.
All half-angle arithmetic, fold identities, record growth and rationality are
assembled automatically into `FreshModuleCertificate`.
========================================================================== -/

namespace Ulam165
open Sphere

variable {d : ℕ}

/-- Cross inverse safety between two finite source blocks.  Since squared
chordal distance is symmetric, one orientation is enough. -/
def FoldInverseCrossSafe (xs ys : List (Sphere d)) (B2 : ℝ) : Prop :=
  ∀ p ∈ xs, ∀ q ∈ ys,
    distSq p q / distSq (fold p) (fold q) ≤ B2

lemma foldInverseCrossSafe_weaken {xs ys : List (Sphere d)} {A B : ℝ}
    (h : FoldInverseCrossSafe xs ys A) (hAB : A ≤ B) :
    FoldInverseCrossSafe xs ys B := by
  intro p hp q hq
  exact le_trans (h p hp q hq) hAB

lemma foldInverseSafe_weaken {xs : List (Sphere d)} {A B : ℝ}
    (h : FoldInverseSafe xs A) (hAB : A ≤ B) :
    FoldInverseSafe xs B := by
  intro p hp q hq
  exact le_trans (h p hp q hq) hAB

/-- Internal safety of the two blocks plus cross safety gives safety of their
concatenation. -/
lemma foldInverseSafe_append_of_cross
    {xs ys : List (Sphere d)} {B2 : ℝ}
    (hx : FoldInverseSafe xs B2)
    (hy : FoldInverseSafe ys B2)
    (hxy : FoldInverseCrossSafe xs ys B2) :
    FoldInverseSafe (xs ++ ys) B2 := by
  intro p hp q hq
  simp only [List.mem_append] at hp hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact hx p hp q hq
  · exact hxy p hp q hq
  · have h := hxy q hq p hp
    rw [distSq_comm p q, distSq_comm (fold p) (fold q)]
    exact h
  · exact hy p hp q hq

/-- The finite geometric data not supplied by the universal half-angle
arithmetic.  This is deliberately a *bridge package*, not an extra hypothesis
in the final theorem: the next continuity step will construct it for every
finite old state by choosing the rational center parameter sufficiently small.
-/
structure FreshFiniteGeometry
    (src : List (Sphere d)) (B0sq Bsq : ℝ)
    (E : EqFrame d) (u : ModuleScalars) : Prop where
  old_safe : FoldInverseSafe src B0sq
  scaffold_local_safe : FoldInverseSafe (scaffoldSources E u) B0sq
  module_local_safe : FoldInverseSafe (moduleSources E u) Bsq
  old_scaffold_cross : FoldInverseCrossSafe src (scaffoldSources E u) B0sq
  old_module_cross : FoldInverseCrossSafe src (moduleSources E u) Bsq
  old_image_nodup : (src.map fold).Nodup
  module_image_nodup : ((moduleSources E u).map fold).Nodup
  image_disjoint : List.Disjoint (src.map fold) ((moduleSources E u).map fold)

namespace FreshFiniteGeometry

variable {src : List (Sphere d)} {B0sq Bsq : ℝ}
  {E : EqFrame d} {u : ModuleScalars}

lemma precenter_safe
    (G : FreshFiniteGeometry src B0sq Bsq E u) :
    FoldInverseSafe (src ++ scaffoldSources E u) B0sq :=
  foldInverseSafe_append_of_cross G.old_safe G.scaffold_local_safe
    G.old_scaffold_cross

lemma full_safe
    (G : FreshFiniteGeometry src B0sq Bsq E u)
    (hB0leBsq : B0sq ≤ Bsq) :
    FoldInverseSafe (src ++ moduleSources E u) Bsq := by
  exact foldInverseSafe_append_of_cross
    (foldInverseSafe_weaken G.old_safe hB0leBsq)
    G.module_local_safe G.old_module_cross

end FreshFiniteGeometry

/-- Positive version of the record-parameter selection lemma. -/
lemma exists_positive_record_parameter (B0sq : ℝ) (hB : 100 ≤ B0sq) :
    ∃ M : ℚ, 0 < M ∧
      B0sq - 1 + (5:ℝ)/256 < (M:ℝ)^2 ∧
      (M:ℝ)^2 < B0sq - 1 + (7:ℝ)/256 := by
  obtain ⟨M,hMl,hMu⟩ := exists_record_parameter B0sq hB
  have hM2 : 0 < (M:ℝ)^2 := by nlinarith
  have hMne : M ≠ 0 := by
    intro h
    subst M
    norm_num at hM2
  refine ⟨|M|, abs_pos.mpr hMne, ?_, ?_⟩
  · simpa [sq_abs] using hMl
  · simpa [sq_abs] using hMu

/-- Assembly theorem: once the finite old--new geometry is supplied, all
remaining fields of `FreshModuleCertificate` follow from the explicit rational
half-angle family. -/
theorem freshModuleCertificate_of_finite_geometry
    {src : List (Sphere d)} (hd : 2 ≤ d)
    {i0 : Fin d} {B0sq : ℝ} {s M : ℚ}
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (hMu : (M:ℝ)^2 < B0sq-1+(7:ℝ)/256)
    (G : let E := canonicalFrame d hd
         let u := freshScalars s M
         let Bsq := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
         FreshFiniteGeometry src B0sq Bsq E u) :
    let E := canonicalFrame d hd
    let u := freshScalars s M
    let Bsq := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
    FreshModuleCertificate src i0 B0sq Bsq E u := by
  dsimp only at G ⊢
  let E := canonicalFrame d hd
  let u := freshScalars s M
  let Bsq : ℝ := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
  have hgeom := fresh_scalar_geometry hB hs0 hs1 hMpos hMl
  have hfold := fresh_fold_identities (d:=d) hd hB hs0 hs1 hMpos hMl
  have hrec := fresh_record_data hB hs0 hs1 hMpos hMl hMu
  have hastar := fresh_astar_upper hB hs0 hs1 hMpos hMl hMu
  dsimp [E,u,Bsq] at hgeom hfold hrec hastar G ⊢
  rcases hgeom with ⟨hca,hcb,hcbca,hd2,hrho2⟩
  rcases hfold with ⟨hfpp,hfpm,hfgp,hfgm,hfc⟩
  rcases hrec with ⟨hincL,hincU,hBsq100⟩
  have hB0leBsq : B0sq ≤
      ((2-2*(freshScalars s M).cb)+
        4*(freshScalars s M).h^2*(freshScalars s M).cb) /
        (2-2*(freshScalars s M).cb) := by
    have hincL' : (1:ℝ)/64 <
        ((2-2*(freshScalars s M).cb)+
          4*(freshScalars s M).h^2*(freshScalars s M).cb) /
          (2-2*(freshScalars s M).cb) - B0sq := by
      simpa only [freshScalars_cb, freshScalars_h] using hincL
    have hpos : 0 <
        ((2-2*(freshScalars s M).cb)+
          4*(freshScalars s M).h^2*(freshScalars s M).cb) /
          (2-2*(freshScalars s M).cb) - B0sq :=
      lt_trans (by norm_num) hincL'
    exact le_of_lt (sub_pos.mp hpos)
  have hpre : FoldInverseSafe
      (src ++ scaffoldSources (canonicalFrame d hd) (freshScalars s M)) B0sq :=
    foldInverseSafe_append_of_cross G.old_safe G.scaffold_local_safe
      G.old_scaffold_cross
  have hfullOld : FoldInverseSafe src
      (((2-2*(freshScalars s M).cb)+
        4*(freshScalars s M).h^2*(freshScalars s M).cb) /
        (2-2*(freshScalars s M).cb)) :=
    foldInverseSafe_weaken G.old_safe hB0leBsq
  have hfull : FoldInverseSafe
      (src ++ moduleSources (canonicalFrame d hd) (freshScalars s M))
      (((2-2*(freshScalars s M).cb)+
        4*(freshScalars s M).h^2*(freshScalars s M).cb) /
        (2-2*(freshScalars s M).cb)) :=
    foldInverseSafe_append_of_cross hfullOld G.module_local_safe
      G.old_module_cross
  have himage : ((src ++ moduleSources (canonicalFrame d hd)
      (freshScalars s M)).map fold).Nodup := by
    rw [List.map_append]
    exact List.nodup_append'.mpr
      ⟨G.old_image_nodup, G.module_image_nodup, G.image_disjoint⟩
  have hRF := canonicalFrame_rational d hd
  have hRS := freshScalars_rational s M
  refine {
    B0_ge := hB
    record_inc_low := hincL
    record_inc_high := hincU
    ca_pos := hca
    cb_pos := hcb
    cb_lt_ca := hcbca
    d2_pos := hd2
    rho2_pos := hrho2
    record_eq := rfl
    astar_upper := hastar
    fold_pinPlus := hfpp
    fold_pinMinus := hfpm
    fold_guardPlus := hfgp
    fold_guardMinus := hfgm
    fold_center := hfc
    precenter_safe := hpre
    full_safe := hfull
    image_nodup := himage
    rational_pinPlus := rational_pinPlus hRF hRS
    rational_pinMinus := rational_pinMinus hRF hRS
    rational_guardSourcePlus := rational_guardSourcePlus hRF hRS
    rational_guardSourceMinus := rational_guardSourceMinus hRF hRS
    rational_center := rational_center hRF hRS
  }

end Ulam165

namespace Ulam165
open Sphere

variable {d : ℕ}

/-- Reflection preserves squared chordal distance. -/
lemma distSq_reflect_reflect (x y : Sphere d) :
    distSq (reflect x) (reflect y) = distSq x y := by
  unfold distSq reflect
  simp only
  ring

namespace ModuleScalars

variable (E : EqFrame d) (u : ModuleScalars)

/-- The two pins are separated by `4 sa^2`. -/
lemma pinPlus_pinMinus_distSq :
    distSq (u.pinPlus E) (u.pinMinus E) = 4*u.sa^2 := by
  unfold distSq pinPlus pinMinus
  have hz := E.z_norm
  calc
    (∑ i, (((u.ca*u.t-u.sa*u.h)*E.z i) -
      ((u.ca*u.t+u.sa*u.h)*E.z i))^2) +
        ((u.ca*u.h+u.sa*u.t) - (u.ca*u.h-u.sa*u.t))^2
      = 4*u.sa^2*u.h^2*(∑ i, E.z i^2) + 4*u.sa^2*u.t^2 := by
          congr 1
          · calc
              (∑ i, (((u.ca*u.t-u.sa*u.h)*E.z i) -
                ((u.ca*u.t+u.sa*u.h)*E.z i))^2)
                  = ∑ i, (4*u.sa^2*u.h^2)*(E.z i)^2 := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      ring
              _ = 4*u.sa^2*u.h^2*(∑ i, E.z i^2) := by
                    rw [Finset.mul_sum]
          · ring
    _ = 4*u.sa^2 := by rw [hz]; nlinarith [u.th_unit]

/-- The two guard targets are separated by `4 sb^2`. -/
lemma guardPlus_guardMinus_distSq :
    distSq (u.guardPlus E) (u.guardMinus E) = 4*u.sb^2 := by
  unfold distSq guardPlus guardMinus
  have hv := E.v_norm
  calc
    (∑ i, ((u.cb*u.t*E.z i + u.sb*E.v i) -
      (u.cb*u.t*E.z i - u.sb*E.v i))^2) +
        (u.cb*u.h-u.cb*u.h)^2
      = 4*u.sb^2*(∑ i, E.v i^2) := by
          rw [show (u.cb*u.h-u.cb*u.h)^2 = 0 by ring, add_zero]
          calc
            (∑ i, ((u.cb*u.t*E.z i + u.sb*E.v i) -
              (u.cb*u.t*E.z i - u.sb*E.v i))^2)
                = ∑ i, (4*u.sb^2)*(E.v i)^2 := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
            _ = 4*u.sb^2*(∑ i, E.v i^2) := by rw [Finset.mul_sum]
    _ = 4*u.sb^2 := by rw [hv]; ring

end ModuleScalars

lemma fresh_sa_sb_pos
    {B0sq : ℝ} {s M : ℚ}
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2) :
    0 < (freshScalars s M).sa ∧ 0 < (freshScalars s M).sb := by
  obtain ⟨ha,hab,hb1⟩ := fresh_halfangle_order hB hs0 hs1 hMpos hMl
  have hb : 0 < ((qSin s/M : ℚ) : ℝ) := lt_trans ha hab
  constructor
  · rw [freshScalars_sa, cast_qSin]
    exact halfSin_pos ha
  · rw [freshScalars_sb, cast_qSin]
    exact halfSin_pos hb

lemma fresh_pin_guard_den_pos
    {B0sq : ℝ} {s M : ℚ}
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2) :
    0 < 2-2*(freshScalars s M).ca*(freshScalars s M).cb := by
  obtain ⟨hca,hcb,hcbca,hd2,hrho2⟩ :=
    fresh_scalar_geometry hB hs0 hs1 hMpos hMl
  have hca1 : (freshScalars s M).ca < 1 := by linarith
  have hcb1 : (freshScalars s M).cb < 1 := lt_trans hcbca hca1
  have hprodca : (freshScalars s M).ca*(freshScalars s M).cb <
      (freshScalars s M).ca := by
    simpa using (mul_lt_mul_of_pos_left hcb1 hca)
  have hprod1 : (freshScalars s M).ca*(freshScalars s M).cb < 1 :=
    lt_trans hprodca hca1
  nlinarith

lemma fresh_pinPlus_guardSourcePlus_ratio_lt_old
    {B0sq : ℝ} {s M : ℚ} (hd : 2 ≤ d)
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (hMu : (M:ℝ)^2 < B0sq-1+(7:ℝ)/256) :
    let E := canonicalFrame d hd
    let u := freshScalars s M
    distSq (u.pinPlus E) (u.guardSourcePlus E) /
      distSq (fold (u.pinPlus E)) (fold (u.guardSourcePlus E)) < B0sq := by
  dsimp
  obtain ⟨hfpp,hfpm,hfgp,hfgm,hfc⟩ :=
    fresh_fold_identities (d:=d) hd hB hs0 hs1 hMpos hMl
  rw [hfpp,hfgp]
  rw [(freshScalars s M).pinPlus_guardSourcePlus_distSq (canonicalFrame d hd),
      (freshScalars s M).pinPlus_guardPlus_distSq (canonicalFrame d hd)]
  simpa [worstPinGuardSq] using
    (fresh_worst_pin_guard_lt_old hB hs0 hs1 hMpos hMl hMu)

lemma fresh_pinPlus_guardSourceMinus_ratio_lt_old
    {B0sq : ℝ} {s M : ℚ} (hd : 2 ≤ d)
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (hMu : (M:ℝ)^2 < B0sq-1+(7:ℝ)/256) :
    let E := canonicalFrame d hd
    let u := freshScalars s M
    distSq (u.pinPlus E) (u.guardSourceMinus E) /
      distSq (fold (u.pinPlus E)) (fold (u.guardSourceMinus E)) < B0sq := by
  dsimp
  obtain ⟨hfpp,hfpm,hfgp,hfgm,hfc⟩ :=
    fresh_fold_identities (d:=d) hd hB hs0 hs1 hMpos hMl
  rw [hfpp,hfgm]
  rw [(freshScalars s M).pinPlus_guardSourceMinus_distSq (canonicalFrame d hd),
      (freshScalars s M).pinPlus_guardMinus_distSq (canonicalFrame d hd)]
  simpa [worstPinGuardSq] using
    (fresh_worst_pin_guard_lt_old hB hs0 hs1 hMpos hMl hMu)

lemma fresh_pinMinus_guardSourcePlus_ratio_lt_old
    {B0sq : ℝ} {s M : ℚ} (hd : 2 ≤ d)
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (hMu : (M:ℝ)^2 < B0sq-1+(7:ℝ)/256) :
    let E := canonicalFrame d hd
    let u := freshScalars s M
    distSq (u.pinMinus E) (u.guardSourcePlus E) /
      distSq (fold (u.pinMinus E)) (fold (u.guardSourcePlus E)) < B0sq := by
  dsimp
  obtain ⟨hfpp,hfpm,hfgp,hfgm,hfc⟩ :=
    fresh_fold_identities (d:=d) hd hB hs0 hs1 hMpos hMl
  rw [hfpm,hfgp]
  rw [(freshScalars s M).pinMinus_guardSourcePlus_distSq (canonicalFrame d hd),
      (freshScalars s M).pinMinus_guardPlus_distSq (canonicalFrame d hd)]
  have hden := fresh_pin_guard_den_pos hB hs0 hs1 hMpos hMl
  obtain ⟨hh,hh50,hh2,ht,ht1⟩ := small_center_parameters hs0 hs1
  obtain ⟨hsa,hsb⟩ := fresh_sa_sb_pos hB hs0 hs1 hMpos hMl
  obtain ⟨hca,hcb,hcbca,hd2,hrho2⟩ :=
    fresh_scalar_geometry hB hs0 hs1 hMpos hMl
  have hterm : 0 ≤ (freshScalars s M).cb*(freshScalars s M).sa*
      (freshScalars s M).h*(freshScalars s M).t := by
    have hh' : 0 < (freshScalars s M).h := by simpa using hh
    have ht' : 0 < (freshScalars s M).t := by simpa using ht
    positivity
  have hnumle :
      2 - 2*(freshScalars s M).cb*
          ((freshScalars s M).ca*(1-2*(freshScalars s M).h^2) +
            2*(freshScalars s M).sa*(freshScalars s M).h*(freshScalars s M).t)
      ≤
      2 - 2*(freshScalars s M).cb*
          ((freshScalars s M).ca*(1-2*(freshScalars s M).h^2) -
            2*(freshScalars s M).sa*(freshScalars s M).h*(freshScalars s M).t) := by
    nlinarith
  have hratio :
      (2 - 2*(freshScalars s M).cb*
          ((freshScalars s M).ca*(1-2*(freshScalars s M).h^2) +
            2*(freshScalars s M).sa*(freshScalars s M).h*(freshScalars s M).t)) /
        (2-2*(freshScalars s M).ca*(freshScalars s M).cb)
      ≤ worstPinGuardSq (freshScalars s M) := by
    unfold worstPinGuardSq
    exact (div_le_div_iff_of_pos_right hden).2 hnumle
  exact lt_of_le_of_lt hratio
    (fresh_worst_pin_guard_lt_old hB hs0 hs1 hMpos hMl hMu)

lemma fresh_pinMinus_guardSourceMinus_ratio_lt_old
    {B0sq : ℝ} {s M : ℚ} (hd : 2 ≤ d)
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (hMu : (M:ℝ)^2 < B0sq-1+(7:ℝ)/256) :
    let E := canonicalFrame d hd
    let u := freshScalars s M
    distSq (u.pinMinus E) (u.guardSourceMinus E) /
      distSq (fold (u.pinMinus E)) (fold (u.guardSourceMinus E)) < B0sq := by
  dsimp
  obtain ⟨hfpp,hfpm,hfgp,hfgm,hfc⟩ :=
    fresh_fold_identities (d:=d) hd hB hs0 hs1 hMpos hMl
  rw [hfpm,hfgm]
  rw [(freshScalars s M).pinMinus_guardSourceMinus_distSq (canonicalFrame d hd),
      (freshScalars s M).pinMinus_guardMinus_distSq (canonicalFrame d hd)]
  have hden := fresh_pin_guard_den_pos hB hs0 hs1 hMpos hMl
  obtain ⟨hh,hh50,hh2,ht,ht1⟩ := small_center_parameters hs0 hs1
  obtain ⟨hsa,hsb⟩ := fresh_sa_sb_pos hB hs0 hs1 hMpos hMl
  obtain ⟨hca,hcb,hcbca,hd2,hrho2⟩ :=
    fresh_scalar_geometry hB hs0 hs1 hMpos hMl
  have hterm : 0 ≤ (freshScalars s M).cb*(freshScalars s M).sa*
      (freshScalars s M).h*(freshScalars s M).t := by
    have hh' : 0 < (freshScalars s M).h := by simpa using hh
    have ht' : 0 < (freshScalars s M).t := by simpa using ht
    positivity
  have hnumle :
      2 - 2*(freshScalars s M).cb*
          ((freshScalars s M).ca*(1-2*(freshScalars s M).h^2) +
            2*(freshScalars s M).sa*(freshScalars s M).h*(freshScalars s M).t)
      ≤
      2 - 2*(freshScalars s M).cb*
          ((freshScalars s M).ca*(1-2*(freshScalars s M).h^2) -
            2*(freshScalars s M).sa*(freshScalars s M).h*(freshScalars s M).t) := by
    nlinarith
  have hratio :
      (2 - 2*(freshScalars s M).cb*
          ((freshScalars s M).ca*(1-2*(freshScalars s M).h^2) +
            2*(freshScalars s M).sa*(freshScalars s M).h*(freshScalars s M).t)) /
        (2-2*(freshScalars s M).ca*(freshScalars s M).cb)
      ≤ worstPinGuardSq (freshScalars s M) := by
    unfold worstPinGuardSq
    exact (div_le_div_iff_of_pos_right hden).2 hnumle
  exact lt_of_le_of_lt hratio
    (fresh_worst_pin_guard_lt_old hB hs0 hs1 hMpos hMl hMu)

/-- All inverse ratios internal to the four-point scaffold stay below the old
record. -/
lemma fresh_scaffold_local_safe
    {B0sq : ℝ} {s M : ℚ} (hd : 2 ≤ d)
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (hMu : (M:ℝ)^2 < B0sq-1+(7:ℝ)/256) :
    FoldInverseSafe
      (scaffoldSources (canonicalFrame d hd) (freshScalars s M)) B0sq := by
  let E := canonicalFrame d hd
  let u := freshScalars s M
  obtain ⟨hfpp,hfpm,hfgp,hfgm,hfc⟩ :=
    fresh_fold_identities (d:=d) hd hB hs0 hs1 hMpos hMl
  have hppgp := fresh_pinPlus_guardSourcePlus_ratio_lt_old (d:=d) hd
    hB hs0 hs1 hMpos hMl hMu
  have hppgm := fresh_pinPlus_guardSourceMinus_ratio_lt_old (d:=d) hd
    hB hs0 hs1 hMpos hMl hMu
  have hpmpg := fresh_pinMinus_guardSourcePlus_ratio_lt_old (d:=d) hd
    hB hs0 hs1 hMpos hMl hMu
  have hpmmg := fresh_pinMinus_guardSourceMinus_ratio_lt_old (d:=d) hd
    hB hs0 hs1 hMpos hMl hMu
  dsimp only at hppgp hppgm hpmpg hpmmg
  intro p hp q hq
  simp [scaffoldSources] at hp hq
  rcases hp with rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl
  · exact le_trans (by simpa [hfpp] using self_ratio_le_hundred (u.pinPlus E) (u.pinPlus E)) hB
  · exact le_trans (by simpa [hfpp,hfpm] using self_ratio_le_hundred (u.pinPlus E) (u.pinMinus E)) hB
  · exact le_of_lt hppgp
  · exact le_of_lt hppgm
  · exact le_trans (by simpa [hfpm,hfpp] using self_ratio_le_hundred (u.pinMinus E) (u.pinPlus E)) hB
  · exact le_trans (by simpa [hfpm] using self_ratio_le_hundred (u.pinMinus E) (u.pinMinus E)) hB
  · exact le_of_lt hpmpg
  · exact le_of_lt hpmmg
  · rw [distSq_comm (u.guardSourcePlus E) (u.pinPlus E),
        distSq_comm (fold (u.guardSourcePlus E)) (fold (u.pinPlus E))]
    exact le_of_lt hppgp
  · rw [distSq_comm (u.guardSourcePlus E) (u.pinMinus E),
        distSq_comm (fold (u.guardSourcePlus E)) (fold (u.pinMinus E))]
    exact le_of_lt hpmpg
  · have h0 : (0:ℝ) ≤ B0sq := by linarith
    simpa [distSq_self] using h0
  · have href : distSq (u.guardSourcePlus E) (u.guardSourceMinus E) =
        distSq (u.guardPlus E) (u.guardMinus E) := by
      simp [ModuleScalars.guardSourcePlus, ModuleScalars.guardSourceMinus,
        distSq_reflect_reflect]
    rw [hfgp,hfgm,href]
    exact le_trans (self_ratio_le_hundred (u.guardPlus E) (u.guardMinus E)) hB
  · rw [distSq_comm (u.guardSourceMinus E) (u.pinPlus E),
        distSq_comm (fold (u.guardSourceMinus E)) (fold (u.pinPlus E))]
    exact le_of_lt hppgm
  · rw [distSq_comm (u.guardSourceMinus E) (u.pinMinus E),
        distSq_comm (fold (u.guardSourceMinus E)) (fold (u.pinMinus E))]
    exact le_of_lt hpmmg
  · have href : distSq (u.guardSourceMinus E) (u.guardSourcePlus E) =
        distSq (u.guardMinus E) (u.guardPlus E) := by
      simp [ModuleScalars.guardSourcePlus, ModuleScalars.guardSourceMinus,
        distSq_reflect_reflect]
    rw [hfgm,hfgp,href]
    exact le_trans (self_ratio_le_hundred (u.guardMinus E) (u.guardPlus E)) hB
  · have h0 : (0:ℝ) ≤ B0sq := by linarith
    simpa [distSq_self] using h0

end Ulam165

namespace Ulam165
open Sphere

variable {d : ℕ}

/-- The center has safe inverse interaction with every scaffold point at the
new record. -/
lemma fresh_scaffold_center_cross_safe
    {B0sq : ℝ} {s M : ℚ} (hd : 2 ≤ d)
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (hMu : (M:ℝ)^2 < B0sq-1+(7:ℝ)/256) :
    let E := canonicalFrame d hd
    let u := freshScalars s M
    let Bsq := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
    FoldInverseCrossSafe (scaffoldSources E u) [u.center E] Bsq := by
  dsimp
  let E := canonicalFrame d hd
  let u := freshScalars s M
  let Bsq : ℝ := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
  obtain ⟨hfpp,hfpm,hfgp,hfgm,hfc⟩ :=
    fresh_fold_identities (d:=d) hd hB hs0 hs1 hMpos hMl
  obtain ⟨hincL,hincU,hBsq100⟩ :=
    fresh_record_data hB hs0 hs1 hMpos hMl hMu
  dsimp [E,u,Bsq] at hfpp hfpm hfgp hfgm hfc hBsq100 ⊢
  intro p hp q hq
  simp [scaffoldSources] at hp
  simp only [List.mem_singleton] at hq
  subst q
  rcases hp with rfl | rfl | rfl | rfl
  · have h100 := self_ratio_le_hundred
      ((freshScalars s M).pinPlus (canonicalFrame d hd))
      ((freshScalars s M).center (canonicalFrame d hd))
    have hle : (100:ℝ) ≤
        ((2-2*(freshScalars s M).cb)+
          4*(freshScalars s M).h^2*(freshScalars s M).cb) /
          (2-2*(freshScalars s M).cb) := by linarith
    exact le_trans (by simpa [hfpp,hfc] using h100) hle
  · have h100 := self_ratio_le_hundred
      ((freshScalars s M).pinMinus (canonicalFrame d hd))
      ((freshScalars s M).center (canonicalFrame d hd))
    have hle : (100:ℝ) ≤
        ((2-2*(freshScalars s M).cb)+
          4*(freshScalars s M).h^2*(freshScalars s M).cb) /
          (2-2*(freshScalars s M).cb) := by linarith
    exact le_trans (by simpa [hfpm,hfc] using h100) hle
  · rw [distSq_comm
          ((freshScalars s M).guardSourcePlus (canonicalFrame d hd))
          ((freshScalars s M).center (canonicalFrame d hd)),
        distSq_comm
          (fold ((freshScalars s M).guardSourcePlus (canonicalFrame d hd)))
          (fold ((freshScalars s M).center (canonicalFrame d hd))),
        hfgp,hfc,
        (freshScalars s M).center_guardSourcePlus_distSq (canonicalFrame d hd),
        (freshScalars s M).center_guardPlus_distSq (canonicalFrame d hd)]
    simp only [freshScalars_cb, freshScalars_h]
    exact le_rfl
  · rw [distSq_comm
          ((freshScalars s M).guardSourceMinus (canonicalFrame d hd))
          ((freshScalars s M).center (canonicalFrame d hd)),
        distSq_comm
          (fold ((freshScalars s M).guardSourceMinus (canonicalFrame d hd)))
          (fold ((freshScalars s M).center (canonicalFrame d hd))),
        hfgm,hfc,
        (freshScalars s M).center_guardSourceMinus_distSq (canonicalFrame d hd),
        (freshScalars s M).center_guardMinus_distSq (canonicalFrame d hd)]
    simp only [freshScalars_cb, freshScalars_h]
    exact le_rfl

/-- All inverse ratios internal to the complete five-point fresh block are
bounded by the new record. -/
lemma fresh_module_local_safe
    {B0sq : ℝ} {s M : ℚ} (hd : 2 ≤ d)
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (hMu : (M:ℝ)^2 < B0sq-1+(7:ℝ)/256) :
    let E := canonicalFrame d hd
    let u := freshScalars s M
    let Bsq := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
    FoldInverseSafe (moduleSources E u) Bsq := by
  dsimp
  let E := canonicalFrame d hd
  let u := freshScalars s M
  let Bsq : ℝ := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
  have hsc0 := fresh_scaffold_local_safe (d:=d) hd hB hs0 hs1 hMpos hMl hMu
  have hcross := fresh_scaffold_center_cross_safe (d:=d) hd hB hs0 hs1 hMpos hMl hMu
  obtain ⟨hincL,hincU,hBsq100⟩ := fresh_record_data hB hs0 hs1 hMpos hMl hMu
  dsimp [E,u,Bsq] at hsc0 hcross hBsq100 ⊢
  have hB0le : B0sq ≤
      ((2-2*(freshScalars s M).cb)+
        4*(freshScalars s M).h^2*(freshScalars s M).cb) /
        (2-2*(freshScalars s M).cb) := by nlinarith
  have hsc := foldInverseSafe_weaken hsc0 hB0le
  have hc : FoldInverseSafe
      [(freshScalars s M).center (canonicalFrame d hd)]
      (((2-2*(freshScalars s M).cb)+
        4*(freshScalars s M).h^2*(freshScalars s M).cb) /
        (2-2*(freshScalars s M).cb)) := by
    intro p hp q hq
    simp only [List.mem_singleton] at hp hq
    subst p
    subst q
    have h0 : (0:ℝ) ≤
        ((2-2*(freshScalars s M).cb)+
          4*(freshScalars s M).h^2*(freshScalars s M).cb) /
          (2-2*(freshScalars s M).cb) := by linarith
    simpa [distSq_self] using h0
  simpa [moduleSources] using
    (foldInverseSafe_append_of_cross hsc hc hcross)

private lemma ne_of_distSq_pos' {x y : Sphere d} (h : 0 < distSq x y) : x ≠ y := by
  intro hxy
  subst y
  rw [distSq_self] at h
  exact (lt_irrefl 0) h

/-- The five intended fold images of a fresh module are pairwise distinct. -/
lemma fresh_module_image_nodup
    {B0sq : ℝ} {s M : ℚ} (hd : 2 ≤ d)
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2) :
    ((moduleSources (canonicalFrame d hd) (freshScalars s M)).map fold).Nodup := by
  let E := canonicalFrame d hd
  let u := freshScalars s M
  obtain ⟨hfpp,hfpm,hfgp,hfgm,hfc⟩ :=
    fresh_fold_identities (d:=d) hd hB hs0 hs1 hMpos hMl
  obtain ⟨hca,hcb,hcbca,hd2,hrho2⟩ :=
    fresh_scalar_geometry hB hs0 hs1 hMpos hMl
  obtain ⟨hsa,hsb⟩ := fresh_sa_sb_pos hB hs0 hs1 hMpos hMl
  have hden := fresh_pin_guard_den_pos hB hs0 hs1 hMpos hMl
  have hpppmD : 0 < distSq (u.pinPlus E) (u.pinMinus E) := by
    rw [u.pinPlus_pinMinus_distSq E]
    positivity
  have hgpgmD : 0 < distSq (u.guardPlus E) (u.guardMinus E) := by
    rw [u.guardPlus_guardMinus_distSq E]
    positivity
  have hpppm : u.pinPlus E ≠ u.pinMinus E := ne_of_distSq_pos' hpppmD
  have hgpgm : u.guardPlus E ≠ u.guardMinus E := ne_of_distSq_pos' hgpgmD
  have hppgp : u.pinPlus E ≠ u.guardPlus E := by
    apply ne_of_distSq_pos'
    rw [u.pinPlus_guardPlus_distSq E]
    exact hden
  have hppgm : u.pinPlus E ≠ u.guardMinus E := by
    apply ne_of_distSq_pos'
    rw [u.pinPlus_guardMinus_distSq E]
    exact hden
  have hpmgp : u.pinMinus E ≠ u.guardPlus E := by
    apply ne_of_distSq_pos'
    rw [u.pinMinus_guardPlus_distSq E]
    exact hden
  have hpmgm : u.pinMinus E ≠ u.guardMinus E := by
    apply ne_of_distSq_pos'
    rw [u.pinMinus_guardMinus_distSq E]
    exact hden
  have hcpp : u.center E ≠ u.pinPlus E := by
    apply ne_of_distSq_pos'
    rw [u.center_pinPlus_distSq E]
    exact hrho2
  have hcpm : u.center E ≠ u.pinMinus E := by
    apply ne_of_distSq_pos'
    rw [u.center_pinMinus_distSq E]
    exact hrho2
  have hcgp : u.center E ≠ u.guardPlus E := by
    apply ne_of_distSq_pos'
    rw [u.center_guardPlus_distSq E]
    exact hd2
  have hcgm : u.center E ≠ u.guardMinus E := by
    apply ne_of_distSq_pos'
    rw [u.center_guardMinus_distSq E]
    exact hd2
  have hppc : u.pinPlus E ≠ u.center E := by exact fun h => hcpp h.symm
  have hpmc : u.pinMinus E ≠ u.center E := by exact fun h => hcpm h.symm
  have hgpc : u.guardPlus E ≠ u.center E := by exact fun h => hcgp h.symm
  have hgmc : u.guardMinus E ≠ u.center E := by exact fun h => hcgm h.symm
  dsimp [E,u] at hfpp hfpm hfgp hfgm hfc hpppm hgpgm hppgp hppgm hpmgp hpmgm hppc hpmc hgpc hgmc ⊢
  simp [moduleSources, scaffoldSources, hfpp,hfpm,hfgp,hfgm,hfc,
    hpppm,hgpgm,hppgp,hppgm,hpmgp,hpmgm,hppc,hpmc,hgpc,hgmc]

/-- Only two genuinely global finite conditions remain: old--new ratios below
100 and avoidance of all old fold images. -/
structure FreshOldInteraction
    (src : List (Sphere d)) (E : EqFrame d) (u : ModuleScalars) : Prop where
  cross100 : FoldInverseCrossSafe src (moduleSources E u) 100
  image_disjoint : List.Disjoint (src.map fold) ((moduleSources E u).map fold)

/-- The universal local geometry upgrades an old-interaction package to the
full finite geometry package needed by the certificate assembler. -/
lemma freshFiniteGeometry_of_oldInteraction
    {src : List (Sphere d)} (hd : 2 ≤ d)
    {B0sq : ℝ} {s M : ℚ}
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (hMu : (M:ℝ)^2 < B0sq-1+(7:ℝ)/256)
    (holdSafe : FoldInverseSafe src B0sq)
    (holdNodup : (src.map fold).Nodup)
    (O : FreshOldInteraction src (canonicalFrame d hd) (freshScalars s M)) :
    let E := canonicalFrame d hd
    let u := freshScalars s M
    let Bsq := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
    FreshFiniteGeometry src B0sq Bsq E u := by
  dsimp
  let E := canonicalFrame d hd
  let u := freshScalars s M
  let Bsq : ℝ := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
  have hsc := fresh_scaffold_local_safe (d:=d) hd hB hs0 hs1 hMpos hMl hMu
  have hmod := fresh_module_local_safe (d:=d) hd hB hs0 hs1 hMpos hMl hMu
  have hnd := fresh_module_image_nodup (d:=d) hd hB hs0 hs1 hMpos hMl
  obtain ⟨hincL,hincU,hBsq100⟩ := fresh_record_data hB hs0 hs1 hMpos hMl hMu
  dsimp [E,u,Bsq] at hsc hmod hnd hBsq100 O ⊢
  have hcrossSc : FoldInverseCrossSafe src
      (scaffoldSources (canonicalFrame d hd) (freshScalars s M)) B0sq := by
    intro p hp q hq
    have hqmod : q ∈ moduleSources (canonicalFrame d hd) (freshScalars s M) := by
      simp [moduleSources, hq]
    exact le_trans (O.cross100 p hp q hqmod) hB
  have hcrossMod : FoldInverseCrossSafe src
      (moduleSources (canonicalFrame d hd) (freshScalars s M))
      (((2-2*(freshScalars s M).cb)+
        4*(freshScalars s M).h^2*(freshScalars s M).cb) /
        (2-2*(freshScalars s M).cb)) := by
    intro p hp q hq
    exact le_trans (O.cross100 p hp q hq) (le_of_lt hBsq100)
  exact {
    old_safe := holdSafe
    scaffold_local_safe := hsc
    module_local_safe := hmod
    old_scaffold_cross := hcrossSc
    old_module_cross := hcrossMod
    old_image_nodup := holdNodup
    module_image_nodup := hnd
    image_disjoint := O.image_disjoint
  }

/-- Reduced assembly theorem.  At this point the existence problem is exactly
`FreshOldInteraction`: a finite continuity/avoidance statement. -/
theorem freshModuleCertificate_of_oldInteraction
    {src : List (Sphere d)} (hd : 2 ≤ d)
    {i0 : Fin d} {B0sq : ℝ} {s M : ℚ}
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (hMu : (M:ℝ)^2 < B0sq-1+(7:ℝ)/256)
    (holdSafe : FoldInverseSafe src B0sq)
    (holdNodup : (src.map fold).Nodup)
    (O : FreshOldInteraction src (canonicalFrame d hd) (freshScalars s M)) :
    let E := canonicalFrame d hd
    let u := freshScalars s M
    let Bsq := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
    FreshModuleCertificate src i0 B0sq Bsq E u := by
  apply freshModuleCertificate_of_finite_geometry hd hB hs0 hs1 hMpos hMl hMu
  exact freshFiniteGeometry_of_oldInteraction hd hB hs0 hs1 hMpos hMl hMu
    holdSafe holdNodup O

end Ulam165

namespace Ulam165
open Sphere

variable {d : ℕ}

/-- An equatorial point sees a source and its fold at exactly the same chordal
distance.  This is the key reason every old--new inverse ratio tends to `1`
when a fresh module collapses to the equator. -/
lemma zeta_distSq_fold_eq (E : EqFrame d) (p : Sphere d) :
    distSq E.zeta p = distSq E.zeta (fold p) := by
  unfold distSq EqFrame.zeta fold
  simp only
  have habs : |p.1.2|^2 = p.1.2^2 := sq_abs p.1.2
  nlinarith

lemma old_zeta_inverse_ratio_one (E : EqFrame d) (p : Sphere d)
    (hz : E.zeta ≠ fold p) :
    distSq p E.zeta / distSq (fold p) E.zeta = 1 := by
  rw [distSq_comm p E.zeta, distSq_comm (fold p) E.zeta]
  rw [zeta_distSq_fold_eq E p]
  apply div_self
  apply ne_of_gt
  exact distSq_pos hz

lemma old_zeta_inverse_ratio_one_of_mem
    {src : List (Sphere d)} (E : EqFrame d)
    (hz : E.zeta ∉ src.map fold) :
    ∀ p ∈ src, distSq p E.zeta / distSq (fold p) E.zeta = 1 := by
  intro p hp
  apply old_zeta_inverse_ratio_one E p
  intro h
  apply hz
  exact List.mem_map.mpr ⟨p,hp,h.symm⟩

/-- A positive fresh module never uses the equatorial accumulation point as an
image. -/
lemma moduleZeta_not_fresh_module_image
    {B0sq : ℝ} {s M : ℚ} (hd : 2 ≤ d)
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2) :
    moduleZeta d hd ∉
      (moduleSources (canonicalFrame d hd) (freshScalars s M)).map fold := by
  let E := canonicalFrame d hd
  let u := freshScalars s M
  obtain ⟨hc,hpp,hpm,hgp,hgm⟩ :=
    fresh_northern (d:=d) hd hB hs0 hs1 hMpos hMl
  obtain ⟨hfpp,hfpm,hfgp,hfgm,hfc⟩ :=
    fresh_fold_identities (d:=d) hd hB hs0 hs1 hMpos hMl
  intro hz
  have hmap :
      (moduleSources E u).map fold =
        [u.pinPlus E, u.pinMinus E, u.guardPlus E, u.guardMinus E, u.center E] := by
    dsimp [E,u]
    simp [moduleSources, scaffoldSources, hfpp,hfpm,hfgp,hfgm,hfc]
  change moduleZeta d hd ∈ (moduleSources E u).map fold at hz
  rw [hmap] at hz
  simp at hz
  rcases hz with hz | hz | hz | hz | hz
  · have hlast := congrArg (fun x : Sphere d => x.1.2) hz
    have hz0 : (moduleZeta d hd).1.2 = 0 := by rfl
    rw [hz0] at hlast
    nlinarith
  · have hlast := congrArg (fun x : Sphere d => x.1.2) hz
    have hz0 : (moduleZeta d hd).1.2 = 0 := by rfl
    rw [hz0] at hlast
    nlinarith
  · have hlast := congrArg (fun x : Sphere d => x.1.2) hz
    have hz0 : (moduleZeta d hd).1.2 = 0 := by rfl
    rw [hz0] at hlast
    nlinarith
  · have hlast := congrArg (fun x : Sphere d => x.1.2) hz
    have hz0 : (moduleZeta d hd).1.2 = 0 := by rfl
    rw [hz0] at hlast
    nlinarith
  · have hlast := congrArg (fun x : Sphere d => x.1.2) hz
    have hz0 : (moduleZeta d hd).1.2 = 0 := by rfl
    rw [hz0] at hlast
    nlinarith

/-- The unused accumulation-point invariant survives a fresh module. -/
lemma moduleZeta_not_image_after_fresh
    {src : List (Sphere d)} {B0sq : ℝ} {s M : ℚ} (hd : 2 ≤ d)
    (hzold : moduleZeta d hd ∉ src.map fold)
    (hB : 100 ≤ B0sq)
    (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2) :
    moduleZeta d hd ∉
      ((src ++ moduleSources (canonicalFrame d hd) (freshScalars s M)).map fold) := by
  rw [List.map_append]
  intro hz
  have hz' := List.mem_append.mp hz
  rcases hz' with hz' | hz'
  · exact hzold hz'
  · exact (moduleZeta_not_fresh_module_image (d:=d) hd hB hs0 hs1 hMpos hMl) hz'

end Ulam165

/-! ==========================================================================
## Completion layer: finite old--new interaction by continuity

This section is intended to close the last finite-stage existence gap without
new mathematical hypotheses.  The real one-parameter family is used only to
choose a sufficiently small positive rational parameter.
========================================================================== -/

namespace Ulam165
open Sphere
open Set Filter

variable {d : ℕ}

/-- Proof-irrelevant extensionality for the scalar record. -/
@[ext]
theorem ModuleScalars.ext' {a b : ModuleScalars}
    (ht : a.t = b.t) (hh : a.h = b.h)
    (hca : a.ca = b.ca) (hsa : a.sa = b.sa)
    (hcb : a.cb = b.cb) (hsb : a.sb = b.sb) : a = b := by
  cases a
  cases b
  simp_all

/-- The real fresh family agrees exactly with the rational family after casts. -/
lemma freshScalarsR_cast (s M : ℚ) :
    freshScalarsR (s : ℝ) (M : ℝ) = freshScalars s M := by
  apply ModuleScalars.ext'
  · simp [freshScalarsR, freshScalars, realModuleScalars,
      rationalModuleScalars, cast_qCos]
  · simp [freshScalarsR, freshScalars, realModuleScalars,
      rationalModuleScalars, cast_qSin]
  · simp [freshScalarsR, freshScalars, realModuleScalars,
      rationalModuleScalars, cast_qCos, cast_qSin, pinScale]
  · simp [freshScalarsR, freshScalars, realModuleScalars,
      rationalModuleScalars, cast_qCos, cast_qSin, pinScale]
  · simp [freshScalarsR, freshScalars, realModuleScalars,
      rationalModuleScalars, cast_qCos, cast_qSin]
  · simp [freshScalarsR, freshScalars, realModuleScalars,
      rationalModuleScalars, cast_qSin]

/-- The five positions in a fresh module. -/
inductive FreshSlot where
  | pinPlus
  | pinMinus
  | guardPlus
  | guardMinus
  | center
  deriving DecidableEq

@[fun_prop] lemma continuous_halfCosR_global : Continuous halfCosR := by
  unfold halfCosR
  apply Continuous.div₀
  · fun_prop
  · fun_prop
  · intro x
    positivity

@[fun_prop] lemma continuous_halfSinR_global : Continuous halfSinR := by
  unfold halfSinR
  apply Continuous.div₀
  · fun_prop
  · fun_prop
  · intro x
    positivity

/-- Real source point in one of the five fresh-module slots. -/
def freshSourceR (j : FreshSlot) (E : EqFrame d) (M r : ℝ) : Sphere d :=
  let u := freshScalarsR r M
  match j with
  | .pinPlus => u.pinPlus E
  | .pinMinus => u.pinMinus E
  | .guardPlus => u.guardSourcePlus E
  | .guardMinus => u.guardSourceMinus E
  | .center => u.center E

/-- Real intended fold image in one of the five fresh-module slots. -/
def freshTargetR (j : FreshSlot) (E : EqFrame d) (M r : ℝ) : Sphere d :=
  let u := freshScalarsR r M
  match j with
  | .pinPlus => u.pinPlus E
  | .pinMinus => u.pinMinus E
  | .guardPlus => u.guardPlus E
  | .guardMinus => u.guardMinus E
  | .center => u.center E

lemma freshSourceR_zero (j : FreshSlot) (E : EqFrame d) (M : ℝ) :
    freshSourceR j E M 0 = E.zeta := by
  cases j <;>
    simp [freshSourceR, freshScalarsR_zero, pinPlus_zero, pinMinus_zero,
      guardSourcePlus_zero, guardSourceMinus_zero, center_zero]

lemma freshTargetR_zero (j : FreshSlot) (E : EqFrame d) (M : ℝ) :
    freshTargetR j E M 0 = E.zeta := by
  cases j <;>
    simp [freshTargetR, freshScalarsR_zero, pinPlus_zero, pinMinus_zero,
      guardPlus_zero, guardMinus_zero, center_zero]

lemma freshSourceR_cast (j : FreshSlot) (E : EqFrame d) (s M : ℚ) :
    freshSourceR j E (M : ℝ) (s : ℝ) =
      match j with
      | .pinPlus => (freshScalars s M).pinPlus E
      | .pinMinus => (freshScalars s M).pinMinus E
      | .guardPlus => (freshScalars s M).guardSourcePlus E
      | .guardMinus => (freshScalars s M).guardSourceMinus E
      | .center => (freshScalars s M).center E := by
  unfold freshSourceR
  rw [freshScalarsR_cast]

lemma freshTargetR_cast (j : FreshSlot) (E : EqFrame d) (s M : ℚ) :
    freshTargetR j E (M : ℝ) (s : ℝ) =
      match j with
      | .pinPlus => (freshScalars s M).pinPlus E
      | .pinMinus => (freshScalars s M).pinMinus E
      | .guardPlus => (freshScalars s M).guardPlus E
      | .guardMinus => (freshScalars s M).guardMinus E
      | .center => (freshScalars s M).center E := by
  unfold freshTargetR
  rw [freshScalarsR_cast]

/-- The rational five-source list is exactly the list of the five slots. -/
lemma moduleSources_eq_slots (E : EqFrame d) (s M : ℚ) :
    moduleSources E (freshScalars s M) =
      [ freshSourceR .pinPlus E (M:ℝ) (s:ℝ),
        freshSourceR .pinMinus E (M:ℝ) (s:ℝ),
        freshSourceR .guardPlus E (M:ℝ) (s:ℝ),
        freshSourceR .guardMinus E (M:ℝ) (s:ℝ),
        freshSourceR .center E (M:ℝ) (s:ℝ) ] := by
  simp [moduleSources, scaffoldSources, freshSourceR_cast]

/-- Continuity of squared distance from a fixed old source to a real fresh
source.  Unfolding reduces the statement to finite sums of rational functions. -/
lemma continuous_distSq_freshSourceR
    (p : Sphere d) (j : FreshSlot) (E : EqFrame d) (M : ℝ) :
    Continuous (fun r : ℝ => distSq p (freshSourceR j E M r)) := by
  cases j <;>
    simp [freshSourceR, freshScalarsR, realModuleScalars,
      ModuleScalars.center, ModuleScalars.pinPlus, ModuleScalars.pinMinus,
      ModuleScalars.guardSourcePlus, ModuleScalars.guardSourceMinus,
      ModuleScalars.guardPlus, ModuleScalars.guardMinus, Sphere.reflect,
      Sphere.distSq, div_eq_mul_inv] <;>
    fun_prop (disch := positivity)

lemma continuous_distSq_freshTargetR
    (p : Sphere d) (j : FreshSlot) (E : EqFrame d) (M : ℝ) :
    Continuous (fun r : ℝ => distSq p (freshTargetR j E M r)) := by
  cases j <;>
    simp [freshTargetR, freshScalarsR, realModuleScalars,
      ModuleScalars.center, ModuleScalars.pinPlus, ModuleScalars.pinMinus,
      ModuleScalars.guardPlus, ModuleScalars.guardMinus,
      Sphere.distSq, div_eq_mul_inv] <;>
    fun_prop (disch := positivity)

/-- Old--new inverse-ratio function for the real family.  We use the intended
fresh target, which agrees with the actual fold for every admissible positive
rational parameter. -/
def oldFreshRatioR (p : Sphere d) (j : FreshSlot)
    (E : EqFrame d) (M r : ℝ) : ℝ :=
  distSq p (freshSourceR j E M r) /
    distSq (fold p) (freshTargetR j E M r)

lemma oldFreshRatioR_zero (p : Sphere d) (j : FreshSlot)
    (E : EqFrame d) (M : ℝ) (hz : E.zeta ≠ fold p) :
    oldFreshRatioR p j E M 0 = 1 := by
  simp [oldFreshRatioR, freshSourceR_zero, freshTargetR_zero]
  rw [distSq_comm p E.zeta, distSq_comm (fold p) E.zeta]
  rw [zeta_distSq_fold_eq E p]
  exact div_self (ne_of_gt (distSq_pos hz))

lemma oldFreshDenR_zero_pos (p : Sphere d) (j : FreshSlot)
    (E : EqFrame d) (M : ℝ) (hz : E.zeta ≠ fold p) :
    0 < distSq (fold p) (freshTargetR j E M 0) := by
  rw [freshTargetR_zero]
  rw [distSq_comm]
  exact distSq_pos hz

lemma continuousAt_oldFreshRatioR (p : Sphere d) (j : FreshSlot)
    (E : EqFrame d) (M : ℝ) (hz : E.zeta ≠ fold p) :
    ContinuousAt (fun r : ℝ => oldFreshRatioR p j E M r) 0 := by
  unfold oldFreshRatioR
  apply ContinuousAt.div
  · exact (continuous_distSq_freshSourceR p j E M).continuousAt
  · exact (continuous_distSq_freshTargetR (fold p) j E M).continuousAt
  · exact ne_of_gt (oldFreshDenR_zero_pos p j E M hz)

/-- For one old point and one fresh slot, both the ratio bound and target
avoidance hold eventually near the collapsed module. -/
lemma eventually_oldFresh_good (p : Sphere d) (j : FreshSlot)
    (E : EqFrame d) (M : ℝ) (hz : E.zeta ≠ fold p) :
    ∀ᶠ r : ℝ in 𝓝 0,
      oldFreshRatioR p j E M r < 100 ∧
      0 < distSq (fold p) (freshTargetR j E M r) := by
  have hratio0 : oldFreshRatioR p j E M 0 = 1 :=
    oldFreshRatioR_zero p j E M hz
  have hratioEv : ∀ᶠ r : ℝ in 𝓝 0, oldFreshRatioR p j E M r < 100 := by
    have hnh : ∀ᶠ x : ℝ in 𝓝 (oldFreshRatioR p j E M 0), x < 100 := by
      apply gt_mem_nhds
      rw [hratio0]
      norm_num
    exact (continuousAt_oldFreshRatioR p j E M hz) hnh
  have hdenEv : ∀ᶠ r : ℝ in 𝓝 0,
      0 < distSq (fold p) (freshTargetR j E M r) := by
    have h0 := oldFreshDenR_zero_pos p j E M hz
    have hnh : ∀ᶠ x : ℝ in
        𝓝 (distSq (fold p) (freshTargetR j E M 0)), 0 < x :=
      lt_mem_nhds h0
    exact (continuous_distSq_freshTargetR (fold p) j E M).continuousAt hnh
  filter_upwards [hratioEv, hdenEv] with r hr hd
  exact ⟨hr,hd⟩

/-- All five fresh slots are simultaneously good for one fixed old point. -/
lemma eventually_old_allSlots_good (p : Sphere d) (E : EqFrame d) (M : ℝ)
    (hz : E.zeta ≠ fold p) :
    ∀ᶠ r : ℝ in 𝓝 0,
      ∀ j : FreshSlot,
        oldFreshRatioR p j E M r < 100 ∧
        0 < distSq (fold p) (freshTargetR j E M r) := by
  have hpp := eventually_oldFresh_good p .pinPlus E M hz
  have hpm := eventually_oldFresh_good p .pinMinus E M hz
  have hgp := eventually_oldFresh_good p .guardPlus E M hz
  have hgm := eventually_oldFresh_good p .guardMinus E M hz
  have hc := eventually_oldFresh_good p .center E M hz
  filter_upwards [hpp,hpm,hgp,hgm,hc] with r hpp hpm hgp hgm hc
  intro j
  cases j <;> assumption

/-- Every old point in a finite list is simultaneously compatible with all
five slots for all sufficiently small real parameters. -/
lemma eventually_allOld_allSlots_good
    (src : List (Sphere d)) (E : EqFrame d) (M : ℝ)
    (hz : E.zeta ∉ src.map fold) :
    ∀ᶠ r : ℝ in 𝓝 0,
      ∀ p ∈ src, ∀ j : FreshSlot,
        oldFreshRatioR p j E M r < 100 ∧
        0 < distSq (fold p) (freshTargetR j E M r) := by
  induction src with
  | nil => simp
  | cons p ps ih =>
      have hzp : E.zeta ≠ fold p := by
        intro h
        apply hz
        simp [h]
      have hzps : E.zeta ∉ ps.map fold := by
        intro h
        apply hz
        simp [h]
      have hp := eventually_old_allSlots_good p E M hzp
      have hps := ih hzps
      filter_upwards [hp,hps] with r hp hps
      intro q hq j
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hp j
      · exact hps q hq j

/-- A neighborhood of zero contains a small positive rational point. -/
lemma exists_pos_rat_in_nhds {P : ℝ → Prop}
    (hP : ∀ᶠ r : ℝ in 𝓝 0, P r) :
    ∃ s : ℚ, 0 < s ∧ s < 1/100 ∧ P (s : ℝ) := by
  have hset : {r : ℝ | P r} ∈ 𝓝 (0:ℝ) := hP
  rcases (Metric.mem_nhds_iff.1 hset) with ⟨ε,hε,hball⟩
  let η : ℝ := min ε (1/100 : ℝ)
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min hε (by norm_num)
  obtain ⟨s,hs0,hsη⟩ := exists_rat_btwn hη
  have hsε : (s:ℝ) < ε := lt_of_lt_of_le hsη (min_le_left _ _)
  have hs100 : (s:ℝ) < (1:ℝ)/100 :=
    lt_of_lt_of_le hsη (min_le_right _ _)
  have hsball : (s:ℝ) ∈ Metric.ball (0:ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [sub_zero, abs_of_pos hs0]
    exact hsε
  refine ⟨s, ?_, ?_, hball hsball⟩
  · exact_mod_cast hs0
  · have hs100' : (s:ℝ) < (((1:ℚ)/100 : ℚ) : ℝ) := by
      norm_num
      exact hs100
    exact_mod_cast hs100'

/-- Slot membership normal form for the five-source list. -/
lemma mem_moduleSources_slots
    (E : EqFrame d) (s M : ℚ) {q : Sphere d} :
    q ∈ moduleSources E (freshScalars s M) ↔
      q = freshSourceR .pinPlus E (M:ℝ) (s:ℝ) ∨
      q = freshSourceR .pinMinus E (M:ℝ) (s:ℝ) ∨
      q = freshSourceR .guardPlus E (M:ℝ) (s:ℝ) ∨
      q = freshSourceR .guardMinus E (M:ℝ) (s:ℝ) ∨
      q = freshSourceR .center E (M:ℝ) (s:ℝ) := by
  rw [moduleSources_eq_slots]
  simp

/-- Target corresponding to a rational source slot. -/
lemma fold_freshSourceR_cast
    {B0sq : ℝ} (hd : 2 ≤ d) (hB : 100 ≤ B0sq)
    {s M : ℚ} (hs0 : 0 < s) (hs1 : s < 1/100)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (j : FreshSlot) :
    fold (freshSourceR j (canonicalFrame d hd) (M:ℝ) (s:ℝ)) =
      freshTargetR j (canonicalFrame d hd) (M:ℝ) (s:ℝ) := by
  obtain ⟨hfpp,hfpm,hfgp,hfgm,hfc⟩ :=
    fresh_fold_identities (d:=d) hd hB hs0 hs1 hMpos hMl
  cases j <;>
    simp [freshSourceR_cast, freshTargetR_cast, hfpp,hfpm,hfgp,hfgm,hfc]

/-- The finite continuity/avoidance theorem that was the last unresolved field
of `FreshModuleCertificate`. -/
theorem exists_small_rational_oldInteraction
    {src : List (Sphere d)} (hd : 2 ≤ d)
    {B0sq : ℝ} {M : ℚ}
    (hB : 100 ≤ B0sq)
    (hMpos : 0 < M)
    (hMl : B0sq-1+(5:ℝ)/256 < (M:ℝ)^2)
    (hz : moduleZeta d hd ∉ src.map fold) :
    ∃ s : ℚ, 0 < s ∧ s < 1/100 ∧
      FreshOldInteraction src (canonicalFrame d hd) (freshScalars s M) := by
  let E := canonicalFrame d hd
  have hzE : E.zeta ∉ src.map fold := by
    simpa [E, moduleZeta, EqFrame.zeta, canonicalFrame] using hz
  have hev := eventually_allOld_allSlots_good src E (M:ℝ) hzE
  obtain ⟨s,hs0,hs1,hgood⟩ := exists_pos_rat_in_nhds hev
  refine ⟨s,hs0,hs1,?_⟩
  constructor
  · intro p hp q hq
    rw [mem_moduleSources_slots] at hq
    rcases hq with hq | hq | hq | hq | hq
    · subst q
      have h := (hgood p hp .pinPlus).1
      have hf := fold_freshSourceR_cast (d:=d) hd hB hs0 hs1 hMpos hMl FreshSlot.pinPlus
      rw [hf]
      change oldFreshRatioR p .pinPlus E (M:ℝ) (s:ℝ) ≤ 100
      exact le_of_lt h
    · subst q
      have h := (hgood p hp .pinMinus).1
      have hf := fold_freshSourceR_cast (d:=d) hd hB hs0 hs1 hMpos hMl FreshSlot.pinMinus
      rw [hf]
      change oldFreshRatioR p .pinMinus E (M:ℝ) (s:ℝ) ≤ 100
      exact le_of_lt h
    · subst q
      have h := (hgood p hp .guardPlus).1
      have hf := fold_freshSourceR_cast (d:=d) hd hB hs0 hs1 hMpos hMl FreshSlot.guardPlus
      rw [hf]
      change oldFreshRatioR p .guardPlus E (M:ℝ) (s:ℝ) ≤ 100
      exact le_of_lt h
    · subst q
      have h := (hgood p hp .guardMinus).1
      have hf := fold_freshSourceR_cast (d:=d) hd hB hs0 hs1 hMpos hMl FreshSlot.guardMinus
      rw [hf]
      change oldFreshRatioR p .guardMinus E (M:ℝ) (s:ℝ) ≤ 100
      exact le_of_lt h
    · subst q
      have h := (hgood p hp .center).1
      have hf := fold_freshSourceR_cast (d:=d) hd hB hs0 hs1 hMpos hMl FreshSlot.center
      rw [hf]
      change oldFreshRatioR p .center E (M:ℝ) (s:ℝ) ≤ 100
      exact le_of_lt h
  · intro a ha hb
    rcases List.mem_map.mp ha with ⟨p,hp,rfl⟩
    rcases List.mem_map.mp hb with ⟨q,hq,hqeq⟩
    rw [mem_moduleSources_slots] at hq
    rcases hq with hq | hq | hq | hq | hq
    · subst q
      have hdpos := (hgood p hp .pinPlus).2
      have hf := fold_freshSourceR_cast (d:=d) hd hB hs0 hs1 hMpos hMl FreshSlot.pinPlus
      have heq : freshTargetR .pinPlus E (M:ℝ) (s:ℝ) = fold p := by
        simpa [E, hf] using hqeq
      rw [heq, distSq_self] at hdpos
      linarith
    · subst q
      have hdpos := (hgood p hp .pinMinus).2
      have hf := fold_freshSourceR_cast (d:=d) hd hB hs0 hs1 hMpos hMl FreshSlot.pinMinus
      have heq : freshTargetR .pinMinus E (M:ℝ) (s:ℝ) = fold p := by
        simpa [E, hf] using hqeq
      rw [heq, distSq_self] at hdpos
      linarith
    · subst q
      have hdpos := (hgood p hp .guardPlus).2
      have hf := fold_freshSourceR_cast (d:=d) hd hB hs0 hs1 hMpos hMl FreshSlot.guardPlus
      have heq : freshTargetR .guardPlus E (M:ℝ) (s:ℝ) = fold p := by
        simpa [E, hf] using hqeq
      rw [heq, distSq_self] at hdpos
      linarith
    · subst q
      have hdpos := (hgood p hp .guardMinus).2
      have hf := fold_freshSourceR_cast (d:=d) hd hB hs0 hs1 hMpos hMl FreshSlot.guardMinus
      have heq : freshTargetR .guardMinus E (M:ℝ) (s:ℝ) = fold p := by
        simpa [E, hf] using hqeq
      rw [heq, distSq_self] at hdpos
      linarith
    · subst q
      have hdpos := (hgood p hp .center).2
      have hf := fold_freshSourceR_cast (d:=d) hd hB hs0 hs1 hMpos hMl FreshSlot.center
      have heq : freshTargetR .center E (M:ℝ) (s:ℝ) = fold p := by
        simpa [E, hf] using hqeq
      rw [heq, distSq_self] at hdpos
      linarith

/-- Unconditional one-step fresh certificate existence over any finite old
state satisfying the already established invariants. -/
theorem exists_freshModuleCertificate
    {src : List (Sphere d)} (hd : 2 ≤ d) (i0 : Fin d)
    {B0sq : ℝ}
    (hB : 100 ≤ B0sq)
    (holdSafe : FoldInverseSafe src B0sq)
    (holdNodup : (src.map fold).Nodup)
    (hz : moduleZeta d hd ∉ src.map fold) :
    ∃ (s M : ℚ) (Bsq : ℝ),
      0 < s ∧ s < 1/100 ∧ 0 < M ∧
      FreshModuleCertificate src i0 B0sq Bsq
        (canonicalFrame d hd) (freshScalars s M) := by
  obtain ⟨M,hMpos,hMl,hMu⟩ := exists_positive_record_parameter B0sq hB
  obtain ⟨s,hs0,hs1,hO⟩ :=
    exists_small_rational_oldInteraction (d:=d) hd hB hMpos hMl hz
  let u := freshScalars s M
  let Bsq : ℝ := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
  refine ⟨s,M,Bsq,hs0,hs1,hMpos,?_⟩
  dsimp [u,Bsq]
  exact freshModuleCertificate_of_oldInteraction
    (d:=d) (src:=src) hd (i0:=i0) (B0sq:=B0sq)
    hB hs0 hs1 hMpos hMl hMu holdSafe holdNodup hO

end Ulam165

/-! ==========================================================================
## Completion layer: certified infinite fresh tower

This layer packages the already-proved one-step existence theorem into a
state that can be iterated without losing any of the hypotheses required by
the next step.  It gives a genuine infinite greedy construction with exact
inverse record growing at least linearly.  Density insertion is handled in the
next layer.
========================================================================== -/

namespace Ulam165
open Sphere
open Set Filter

variable {d : ℕ}

lemma epos_injective : Function.Injective (@epos d) := by
  intro i j hij
  by_contra hne
  have hc := congrArg (fun x : Sphere d => x.1.1 i) hij
  simp [epos, hne] at hc

lemma eneg_injective : Function.Injective (@eneg d) := by
  intro i j hij
  by_contra hne
  have hc := congrArg (fun x : Sphere d => x.1.1 i) hij
  simp [eneg, hne] at hc

lemma epos_ne_eneg (i j : Fin d) : epos i ≠ eneg j := by
  intro hij
  have hc := congrArg (fun x : Sphere d => x.1.1 i) hij
  by_cases h : i = j
  · subst j
    norm_num [epos, eneg] at hc
  · simp [epos, eneg, h] at hc

lemma epos_ne_north (i : Fin d) : epos i ≠ north d := by
  intro h
  have hc := congrArg (fun x : Sphere d => x.1.2) h
  norm_num [epos, north] at hc

lemma eneg_ne_north (i : Fin d) : eneg i ≠ north d := by
  intro h
  have hc := congrArg (fun x : Sphere d => x.1.2) h
  norm_num [eneg, north] at hc

lemma epos_ne_anchorA (i i0 : Fin d) : epos i ≠ anchorA i0 := by
  intro h
  have hc := congrArg (fun x : Sphere d => x.1.2) h
  norm_num [epos, anchorA] at hc

lemma eneg_ne_anchorA (i i0 : Fin d) : eneg i ≠ anchorA i0 := by
  intro h
  have hc := congrArg (fun x : Sphere d => x.1.2) h
  norm_num [eneg, anchorA] at hc

lemma north_ne_anchorA (i0 : Fin d) : north d ≠ anchorA i0 := by
  intro h
  have hc := congrArg (fun x : Sphere d => x.1.2) h
  norm_num [north, anchorA] at hc

lemma anchor_fold_images_eq (i0 : Fin d) :
    (anchorSources d i0).map fold =
      (List.ofFn fun i : Fin d => epos i) ++
      (List.ofFn fun i : Fin d => eneg i) ++
      [north d, anchorA i0] := by
  simp [anchorSources, List.map_append, Function.comp_def, fold_epos, fold_eneg,
    fold_south, fold_anchorA]

/-- The initial anchor images are pairwise distinct. -/
lemma anchor_image_nodup (i0 : Fin d) :
    ((anchorSources d i0).map fold).Nodup := by
  rw [anchor_fold_images_eq]
  let P : List (Sphere d) := List.ofFn fun i : Fin d => epos i
  let N : List (Sphere d) := List.ofFn fun i : Fin d => eneg i
  have hP : P.Nodup := by
    dsimp [P]
    exact List.nodup_ofFn_ofInjective epos_injective
  have hN : N.Nodup := by
    dsimp [N]
    exact List.nodup_ofFn_ofInjective eneg_injective
  have hPN : P.Disjoint N := by
    intro x hx hy
    rw [List.mem_ofFn'] at hx hy
    rcases hx with ⟨i,rfl⟩
    rcases hy with ⟨j,hj⟩
    exact (epos_ne_eneg i j) hj.symm
  have hPNnd : (P ++ N).Nodup := hP.append hN hPN
  have htail : ([north d, anchorA i0] : List (Sphere d)).Nodup := by
    simp [north_ne_anchorA]
  have hcross : (P ++ N).Disjoint [north d, anchorA i0] := by
    intro x hx hy
    rw [List.mem_append] at hx
    simp at hy
    rcases hx with hx | hx
    · rw [List.mem_ofFn'] at hx
      rcases hx with ⟨i,rfl⟩
      rcases hy with h | h
      · exact (epos_ne_north i) h
      · exact (epos_ne_anchorA i i0) h
    · rw [List.mem_ofFn'] at hx
      rcases hx with ⟨i,rfl⟩
      rcases hy with h | h
      · exact (eneg_ne_north i) h
      · exact (eneg_ne_anchorA i i0) h
  exact hPNnd.append htail hcross

/-- All invariants needed to continue the construction from a finite stage. -/
structure CertifiedState (d : ℕ) (hd : 2 ≤ d) (i0 : Fin d) where
  src : List (Sphere d)
  Bsq : ℝ
  built : GreedyBuiltFrom (anchorSources d i0) src
  inverse_exact : inverseLipSq (foldGraph src) = Bsq
  safe : FoldInverseSafe src Bsq
  image_nodup : (src.map fold).Nodup
  rational : ∀ p ∈ src, RationalPoint p
  zeta_avoid : moduleZeta d hd ∉ src.map fold
  pos_mem : ∀ i : Fin d, epos i ∈ src
  neg_mem : ∀ i : Fin d, eneg i ∈ src
  south_mem : south d ∈ src
  anchorA_mem : anchorA i0 ∈ src
  B_ge : 100 ≤ Bsq

/-- The anchor configuration is a certified initial state. -/
noncomputable def initialCertifiedState (d : ℕ) (hd : 2 ≤ d) :
    CertifiedState d hd (idx0 d (le_trans (by norm_num) hd)) where
  src := anchorSources d (idx0 d (le_trans (by norm_num) hd))
  Bsq := 100
  built := GreedyBuiltFrom.base
  inverse_exact := (initial_constants (d:=d) (idx0 d (le_trans (by norm_num) hd))).2
  safe := foldInverseSafe_of_inverse_eq _ _
    (initial_constants (d:=d) (idx0 d (le_trans (by norm_num) hd))).2
  image_nodup := anchor_image_nodup (d:=d) (idx0 d (le_trans (by norm_num) hd))
  zeta_avoid := moduleZeta_not_initial_image (d:=d) hd (idx0 d (le_trans (by norm_num) hd))
  pos_mem := fun i => epos_mem_anchorSources (idx0 d (le_trans (by norm_num) hd)) i
  neg_mem := fun i => eneg_mem_anchorSources (idx0 d (le_trans (by norm_num) hd)) i
  south_mem := south_mem_anchorSources (idx0 d (le_trans (by norm_num) hd))
  anchorA_mem := anchorA_mem_anchorSources (idx0 d (le_trans (by norm_num) hd))
  rational := anchorSources_rational (d:=d) (idx0 d (le_trans (by norm_num) hd))
  B_ge := by norm_num

/-- A fresh step retains the numerical choices used to prove zeta avoidance;
this prevents loss of information when iterating the existential theorem. -/
structure FreshStepData {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CertifiedState d hd i0) where
  s : ℚ
  M : ℚ
  Bnext : ℝ
  hs0 : 0 < s
  hs1 : s < 1/100
  hMpos : 0 < M
  hMl : S.Bsq - 1 + (5:ℝ)/256 < (M:ℝ)^2
  hMu : (M:ℝ)^2 < S.Bsq - 1 + (7:ℝ)/256
  cert : FreshModuleCertificate S.src i0 S.Bsq Bnext
    (canonicalFrame d hd) (freshScalars s M)

/-- Every certified finite state admits another complete five-point fresh
module. -/
theorem exists_freshStepData {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CertifiedState d hd i0) : ∃ _T : FreshStepData S, True := by
  obtain ⟨M,hMpos,hMl,hMu⟩ := exists_positive_record_parameter S.Bsq S.B_ge
  obtain ⟨s,hs0,hs1,hO⟩ :=
    exists_small_rational_oldInteraction (d:=d) hd S.B_ge hMpos hMl S.zeta_avoid
  let u := freshScalars s M
  let Bnext : ℝ := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
  have hC : FreshModuleCertificate S.src i0 S.Bsq Bnext
      (canonicalFrame d hd) u := by
    dsimp [u,Bnext]
    exact freshModuleCertificate_of_oldInteraction
      (d:=d) (src:=S.src) hd (i0:=i0) (B0sq:=S.Bsq)
      S.B_ge hs0 hs1 hMpos hMl hMu S.safe S.image_nodup hO
  refine ⟨{
    s := s
    M := M
    Bnext := Bnext
    hs0 := hs0
    hs1 := hs1
    hMpos := hMpos
    hMl := hMl
    hMu := hMu
    cert := hC
  }, trivial⟩

noncomputable def chooseFreshStep {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CertifiedState d hd i0) : FreshStepData S :=
  Classical.choose (exists_freshStepData S)

namespace FreshStepData

variable {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
  {S : CertifiedState d hd i0}

/-- The certified state obtained after applying the chosen five-point block. -/
noncomputable def nextState (T : FreshStepData S) : CertifiedState d hd i0 := by
  let E := canonicalFrame d hd
  let u := freshScalars T.s T.M
  let src' := S.src ++ moduleSources E u
  have happ := T.cert.apply_fresh_module S.built S.pos_mem S.neg_mem
    S.south_mem S.anchorA_mem S.inverse_exact
  refine {
    src := src'
    Bsq := T.Bnext
    built := ?_
    inverse_exact := ?_
    safe := ?_
    image_nodup := ?_
    rational := ?_
    zeta_avoid := ?_
    pos_mem := ?_
    neg_mem := ?_
    south_mem := ?_
    anchorA_mem := ?_
    B_ge := ?_
  }
  · exact happ.1
  · exact happ.2
  · exact T.cert.full_safe
  · exact T.cert.image_nodup
  · intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact S.rational p hp
    · exact T.cert.moduleSources_rational p hp
  · exact moduleZeta_not_image_after_fresh (d:=d) hd S.zeta_avoid S.B_ge
      T.hs0 T.hs1 T.hMpos T.hMl
  · intro i
    exact List.mem_append_left _ (S.pos_mem i)
  · intro i
    exact List.mem_append_left _ (S.neg_mem i)
  · exact List.mem_append_left _ S.south_mem
  · exact List.mem_append_left _ S.anchorA_mem
  · exact T.cert.Bsq_ge

lemma next_B_growth (T : FreshStepData S) :
    (1:ℝ)/64 < T.nextState.Bsq - S.Bsq := by
  exact T.cert.record_inc_low

lemma next_src_eq (T : FreshStepData S) :
    T.nextState.src = S.src ++
      moduleSources (canonicalFrame d hd) (freshScalars T.s T.M) := rfl

lemma next_length (T : FreshStepData S) :
    T.nextState.src.length = S.src.length + 5 := by
  rw [next_src_eq, List.length_append]
  simp [moduleSources, scaffoldSources]

end FreshStepData

/-- Infinite iteration of certified fresh modules. -/
noncomputable def freshTower (d : ℕ) (hd : 2 ≤ d) :
    ℕ → CertifiedState d hd (idx0 d (le_trans (by norm_num) hd))
  | 0 => initialCertifiedState d hd
  | n+1 => (chooseFreshStep (freshTower d hd n)).nextState

lemma freshTower_succ (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    freshTower d hd (n+1) =
      (chooseFreshStep (freshTower d hd n)).nextState := rfl

/-- The exact squared inverse record grows at least by 1/64 per module. -/
theorem freshTower_record_lower (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (100:ℝ) + (n:ℝ)/64 ≤ (freshTower d hd n).Bsq := by
  induction n with
  | zero =>
      simp [freshTower, initialCertifiedState]
  | succ n ih =>
      rw [freshTower_succ]
      have hg := (chooseFreshStep (freshTower d hd n)).next_B_growth
      have hn : ((n+1:ℕ):ℝ) = (n:ℝ) + 1 := by norm_num
      rw [hn]
      nlinarith

/-- Consequently the exact inverse constants along the tower are unbounded. -/
theorem freshTower_inverse_exact (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    inverseLipSq (foldGraph (freshTower d hd n).src) =
      (freshTower d hd n).Bsq :=
  (freshTower d hd n).inverse_exact

theorem freshTower_inverse_lower (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (100:ℝ) + (n:ℝ)/64 ≤
      inverseLipSq (foldGraph (freshTower d hd n).src) := by
  rw [freshTower_inverse_exact]
  exact freshTower_record_lower d hd n

/-- Every finite fresh-tower stage is itself a valid unique-greedy extension
of the initial anchor configuration. -/
theorem freshTower_greedy (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    GreedyBuiltFrom (anchorSources d (idx0 d (le_trans (by norm_num) hd))) (freshTower d hd n).src :=
  (freshTower d hd n).built

/-- Forward Lipschitz constant stays exactly one at every tower stage. -/
theorem freshTower_forward_one (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    forwardLipSq (foldGraph (freshTower d hd n).src) = 1 := by
  exact forwardLipSq_foldGraph_eq_one _ (idx0 d (le_trans (by norm_num) hd))
    ((freshTower d hd n).pos_mem (idx0 d (le_trans (by norm_num) hd)))
    ((freshTower d hd n).neg_mem (idx0 d (le_trans (by norm_num) hd)))

end Ulam165

/-! ==========================================================================
## Completion layer: protected density-point insertion

A pending point `x` can be protected while the inverse record is raised:
each fresh module is chosen using the finite old list `src ++ [x]` in the
continuity theorem.  Thus its fold image is never stolen by the module and all
new cross inverse ratios involving `x` are at most 100.  Once the record is
large enough to dominate the finite old cross ratios of `x`, the point can be
inserted as one more unique greedy fold step.
========================================================================== -/

namespace Ulam165
open Sphere
open Set Filter

variable {d : ℕ}

/-- Global certified finite state.  Rationality is retained as a first-class
invariant so the direct-limit source is a dense sequence of rational points. -/
structure CoreState (d : ℕ) (hd : 2 ≤ d) (i0 : Fin d) where
  src : List (Sphere d)
  Bsq : ℝ
  built : GreedyBuiltFrom (anchorSources d i0) src
  inverse_exact : inverseLipSq (foldGraph src) = Bsq
  safe : FoldInverseSafe src Bsq
  image_nodup : (src.map fold).Nodup
  rational : ∀ p ∈ src, RationalPoint p
  zeta_avoid : moduleZeta d hd ∉ src.map fold
  pos_mem : ∀ i : Fin d, epos i ∈ src
  neg_mem : ∀ i : Fin d, eneg i ∈ src
  south_mem : south d ∈ src
  anchorA_mem : anchorA i0 ∈ src
  B_ge : 100 ≤ Bsq

noncomputable def CertifiedState.toCore {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CertifiedState d hd i0) : CoreState d hd i0 where
  src := S.src
  Bsq := S.Bsq
  built := S.built
  inverse_exact := S.inverse_exact
  safe := S.safe
  image_nodup := S.image_nodup
  rational := S.rational
  zeta_avoid := S.zeta_avoid
  pos_mem := S.pos_mem
  neg_mem := S.neg_mem
  south_mem := S.south_mem
  anchorA_mem := S.anchorA_mem
  B_ge := S.B_ge

noncomputable def initialCoreState (d : ℕ) (hd : 2 ≤ d) :
    CoreState d hd (idx0 d (le_trans (by norm_num) hd)) := (initialCertifiedState d hd).toCore

/-- Restriction of old/new interaction from a larger finite old list. -/
lemma FreshOldInteraction.mono_left
    {src big : List (Sphere d)} {E : EqFrame d} {u : ModuleScalars}
    (H : FreshOldInteraction big E u)
    (hsub : ∀ p ∈ src, p ∈ big) : FreshOldInteraction src E u := by
  constructor
  · intro p hp q hq
    exact H.cross100 p (hsub p hp) q hq
  · intro a ha hb
    rcases List.mem_map.mp ha with ⟨p,hp,rfl⟩
    exact H.image_disjoint
      (List.mem_map.mpr ⟨p,hsub p hp,rfl⟩) hb

/-- A point is pending for insertion with all its current old cross ratios
bounded by `C`; `C ≥ 100` is chosen so that protected fresh modules preserve
this same bound. -/
structure PendingState {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) where
  x : Sphere d
  x_rational : RationalPoint x
  C : ℝ
  C_ge : 100 ≤ C
  fold_fresh : fold x ∉ S.src.map fold
  zeta_ne : fold x ≠ moduleZeta d hd
  cross_bound : ∀ p ∈ S.src,
    distSq x p / distSq (fold x) (fold p) ≤ C

/-- The finite maximum of the current inverse cross ratios of a proposed
point. -/
def targetCrossBound {d : ℕ} (src : List (Sphere d)) (x : Sphere d) : ℝ :=
  listMax (src.map fun p => distSq x p / distSq (fold x) (fold p))

lemma targetCrossBound_nonneg {d : ℕ} (src : List (Sphere d)) (x : Sphere d) :
    0 ≤ targetCrossBound src x := listMax_nonneg _

lemma target_ratio_le_bound {d : ℕ} {src : List (Sphere d)} {x p : Sphere d}
    (hp : p ∈ src) :
    distSq x p / distSq (fold x) (fold p) ≤ targetCrossBound src x := by
  unfold targetCrossBound
  apply le_listMax_of_mem
  exact List.mem_map.mpr ⟨p,hp,rfl⟩

/-- Any fold-fresh point away from zeta defines a pending target with a finite
bound. -/
noncomputable def pendingOfPoint {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) (x : Sphere d)
    (hxrat : RationalPoint x)
    (hfresh : fold x ∉ S.src.map fold)
    (hzeta : fold x ≠ moduleZeta d hd) : PendingState S where
  x := x
  x_rational := hxrat
  C := max 100 (targetCrossBound S.src x)
  C_ge := le_max_left _ _
  fold_fresh := hfresh
  zeta_ne := hzeta
  cross_bound := by
    intro p hp
    exact le_trans (target_ratio_le_bound hp) (le_max_right _ _)

/-- A protected fresh step retains the interaction certificate for the
augmented old list `src ++ [x]`. -/
structure ProtectedFreshStepData {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    {S : CoreState d hd i0} (P : PendingState S) where
  s : ℚ
  M : ℚ
  Bnext : ℝ
  hs0 : 0 < s
  hs1 : s < 1/100
  hMpos : 0 < M
  hMl : S.Bsq - 1 + (5:ℝ)/256 < (M:ℝ)^2
  hMu : (M:ℝ)^2 < S.Bsq - 1 + (7:ℝ)/256
  interaction_aug : FreshOldInteraction (S.src ++ [P.x])
    (canonicalFrame d hd) (freshScalars s M)
  cert : FreshModuleCertificate S.src i0 S.Bsq Bnext
    (canonicalFrame d hd) (freshScalars s M)

/-- Existence of a fresh module that simultaneously protects one pending
point. -/
theorem exists_protectedFreshStepData
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    {S : CoreState d hd i0} (P : PendingState S) :
    ∃ _T : ProtectedFreshStepData P, True := by
  obtain ⟨M,hMpos,hMl,hMu⟩ := exists_positive_record_parameter S.Bsq S.B_ge
  have hzaug : moduleZeta d hd ∉ (S.src ++ [P.x]).map fold := by
    rw [List.map_append]
    simp only [List.map_singleton, List.mem_append, List.mem_singleton]
    intro h
    rcases h with h | h
    · exact S.zeta_avoid h
    · exact P.zeta_ne h.symm
  obtain ⟨s,hs0,hs1,hOaug⟩ :=
    exists_small_rational_oldInteraction (d:=d) hd S.B_ge hMpos hMl hzaug
  have hO : FreshOldInteraction S.src (canonicalFrame d hd) (freshScalars s M) :=
    hOaug.mono_left (fun p hp => List.mem_append_left [P.x] hp)
  let u := freshScalars s M
  let Bnext : ℝ := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
  have hC : FreshModuleCertificate S.src i0 S.Bsq Bnext
      (canonicalFrame d hd) u := by
    dsimp [u,Bnext]
    exact freshModuleCertificate_of_oldInteraction
      (d:=d) (src:=S.src) hd (i0:=i0) (B0sq:=S.Bsq)
      S.B_ge hs0 hs1 hMpos hMl hMu S.safe S.image_nodup hO
  refine ⟨{
    s := s
    M := M
    Bnext := Bnext
    hs0 := hs0
    hs1 := hs1
    hMpos := hMpos
    hMl := hMl
    hMu := hMu
    interaction_aug := hOaug
    cert := hC
  }, trivial⟩

noncomputable def chooseProtectedFreshStep
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    {S : CoreState d hd i0} (P : PendingState S) : ProtectedFreshStepData P :=
  Classical.choose (exists_protectedFreshStepData P)

namespace ProtectedFreshStepData

variable {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
  {S : CoreState d hd i0} {P : PendingState S}

/-- Core state after the protected fresh module. -/
noncomputable def nextCore (T : ProtectedFreshStepData P) : CoreState d hd i0 := by
  let E := canonicalFrame d hd
  let u := freshScalars T.s T.M
  let src' := S.src ++ moduleSources E u
  have happ := T.cert.apply_fresh_module S.built S.pos_mem S.neg_mem
    S.south_mem S.anchorA_mem S.inverse_exact
  refine {
    src := src'
    Bsq := T.Bnext
    built := happ.1
    inverse_exact := happ.2
    safe := T.cert.full_safe
    image_nodup := T.cert.image_nodup
    rational := by
      intro p hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · exact S.rational p hp
      · exact T.cert.moduleSources_rational p hp
    zeta_avoid := moduleZeta_not_image_after_fresh (d:=d) hd S.zeta_avoid S.B_ge
      T.hs0 T.hs1 T.hMpos T.hMl
    pos_mem := fun i => List.mem_append_left _ (S.pos_mem i)
    neg_mem := fun i => List.mem_append_left _ (S.neg_mem i)
    south_mem := List.mem_append_left _ S.south_mem
    anchorA_mem := List.mem_append_left _ S.anchorA_mem
    B_ge := T.cert.Bsq_ge
  }

/-- The pending point remains pending with the same finite bound after the
protected module. -/
noncomputable def nextPending (T : ProtectedFreshStepData P) :
    PendingState T.nextCore := by
  let E := canonicalFrame d hd
  let u := freshScalars T.s T.M
  refine {
    x := P.x
    x_rational := P.x_rational
    C := P.C
    C_ge := P.C_ge
    fold_fresh := ?_
    zeta_ne := P.zeta_ne
    cross_bound := ?_
  }
  · intro hx
    change fold P.x ∈ (S.src ++ moduleSources E u).map fold at hx
    rw [List.map_append] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact P.fold_fresh hx
    · have hxold : fold P.x ∈ (S.src ++ [P.x]).map fold := by
        simp
      exact T.interaction_aug.image_disjoint hxold hx
  · intro q hq
    change q ∈ S.src ++ moduleSources E u at hq
    rw [List.mem_append] at hq
    rcases hq with hq | hq
    · exact P.cross_bound q hq
    · have h100 := T.interaction_aug.cross100 P.x (by simp) q hq
      exact le_trans h100 P.C_ge


lemma nextCore_src_eq (T : ProtectedFreshStepData P) :
    T.nextCore.src = S.src ++
      moduleSources (canonicalFrame d hd) (freshScalars T.s T.M) := rfl

lemma nextCore_length (T : ProtectedFreshStepData P) :
    T.nextCore.src.length = S.src.length + 5 := by
  rw [nextCore_src_eq, List.length_append]
  simp [moduleSources, scaffoldSources]

lemma B_growth (T : ProtectedFreshStepData P) :
    (1:ℝ)/64 < T.nextCore.Bsq - S.Bsq := T.cert.record_inc_low

end ProtectedFreshStepData

/-- Repeated protected fresh growth.  The pending point and its bound are
carried in the dependent state itself. -/
noncomputable def protectedTower
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    {S : CoreState d hd i0} (P : PendingState S) :
    (n : ℕ) → Sigma fun S' : CoreState d hd i0 => PendingState S'
  | 0 => ⟨S,P⟩
  | n+1 =>
      let Q := protectedTower P n
      let T := chooseProtectedFreshStep Q.2
      ⟨T.nextCore, T.nextPending⟩

theorem protectedTower_pending_C
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    {S : CoreState d hd i0} (P : PendingState S) (n : ℕ) :
    (protectedTower P n).2.C = P.C := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [protectedTower]
      let Q := protectedTower P n
      let T := chooseProtectedFreshStep Q.2
      change T.nextPending.C = P.C
      change Q.2.C = P.C at ih
      exact ih

theorem protectedTower_pending_x
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    {S : CoreState d hd i0} (P : PendingState S) (n : ℕ) :
    (protectedTower P n).2.x = P.x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [protectedTower]
      let Q := protectedTower P n
      let T := chooseProtectedFreshStep Q.2
      change T.nextPending.x = P.x
      change Q.2.x = P.x at ih
      exact ih

lemma protectedTower_zero
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    {S : CoreState d hd i0} (P : PendingState S) :
    protectedTower P 0 = ⟨S,P⟩ := rfl

/-- Exact source-length growth in the protected tower. -/
theorem protectedTower_length
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    {S : CoreState d hd i0} (P : PendingState S) (n : ℕ) :
    (protectedTower P n).1.src.length = S.src.length + 5*n := by
  induction n with
  | zero => simp [protectedTower]
  | succ n ih =>
      simp only [protectedTower]
      let Q := protectedTower P n
      let T := chooseProtectedFreshStep Q.2
      have hlen : T.nextCore.src.length = Q.1.src.length + 5 := T.nextCore_length
      have hQ : Q.1.src.length = S.src.length + 5*n := by simpa [Q] using ih
      change T.nextCore.src.length = S.src.length + 5 * (n+1)
      omega

/-- Linear record growth for the protected tower. -/
theorem protectedTower_record_lower
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    {S : CoreState d hd i0} (P : PendingState S) (n : ℕ) :
    S.Bsq + (n:ℝ)/64 ≤ (protectedTower P n).1.Bsq := by
  induction n with
  | zero =>
      simp [protectedTower]
  | succ n ih =>
      simp only [protectedTower]
      let Q := protectedTower P n
      let T := chooseProtectedFreshStep Q.2
      have hg : (1:ℝ)/64 < T.nextCore.Bsq - Q.1.Bsq := T.B_growth
      have hQ : S.Bsq + (n:ℝ)/64 ≤ Q.1.Bsq := by simpa [Q] using ih
      have hn : (((n+1:ℕ):ℕ):ℝ) = (n:ℝ) + 1 := by norm_num
      rw [hn]
      nlinarith

/-- After finitely many protected modules the exact record dominates the
pending target bound. -/
theorem exists_protectedTower_ready
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    {S : CoreState d hd i0} (P : PendingState S) :
    ∃ n : ℕ, P.C ≤ (protectedTower P n).1.Bsq := by
  obtain ⟨n,hn⟩ := exists_nat_gt (64 * (P.C - S.Bsq) : ℝ)
  refine ⟨n, ?_⟩
  have hl := protectedTower_record_lower P n
  nlinarith

/-- Append a ready pending point as one more exact unique greedy fold step. -/
noncomputable def insertReadyPending
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    {S : CoreState d hd i0} (P : PendingState S)
    (hready : P.C ≤ S.Bsq) : CoreState d hd i0 := by
  have hxnew : P.x ∉ S.src := by
    intro hx
    exact P.fold_fresh (List.mem_map.mpr ⟨P.x,hx,rfl⟩)
  have hcross : ∀ p ∈ S.src,
      distSq P.x p / distSq (fold P.x) (fold p) ≤ S.Bsq := by
    intro p hp
    exact le_trans (P.cross_bound p hp) hready
  have hgreedy := fold_extension_unique_greedy S.src i0 P.x S.Bsq
    S.pos_mem S.neg_mem S.south_mem S.anchorA_mem S.inverse_exact S.B_ge
    hxnew P.fold_fresh hcross
  have hinv : inverseLipSq (foldGraph (S.src ++ [P.x])) = S.Bsq :=
    inverseLipSq_fold_append_eq S.src P.x S.Bsq S.inverse_exact
      (by linarith [S.B_ge]) hxnew hcross
  have himg : ((S.src ++ [P.x]).map fold).Nodup := by
    rw [List.map_append]
    exact S.image_nodup.append (by simp) (by
      intro a ha hb
      simp only [List.map_singleton, List.mem_singleton] at hb
      rw [hb] at ha
      exact P.fold_fresh ha)
  refine {
    src := S.src ++ [P.x]
    Bsq := S.Bsq
    built := GreedyBuiltFrom.step S.built hgreedy
    inverse_exact := hinv
    safe := foldInverseSafe_of_inverse_eq _ _ hinv
    image_nodup := himg
    rational := by
      intro p hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · exact S.rational p hp
      · simp only [List.mem_singleton] at hp
        subst p
        exact P.x_rational
    zeta_avoid := ?_
    pos_mem := fun i => List.mem_append_left _ (S.pos_mem i)
    neg_mem := fun i => List.mem_append_left _ (S.neg_mem i)
    south_mem := List.mem_append_left _ S.south_mem
    anchorA_mem := List.mem_append_left _ S.anchorA_mem
    B_ge := S.B_ge
  }
  rw [List.map_append]
  simp only [List.map_singleton, List.mem_append, List.mem_singleton]
  intro h
  rcases h with h | h
  · exact S.zeta_avoid h
  · exact P.zeta_ne h.symm

/-- Starting from any fold-fresh point away from zeta, finitely many protected
modules followed by that point produce a new certified state containing it. -/
theorem exists_core_extension_containing
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) (x : Sphere d)
    (hxrat : RationalPoint x)
    (hfresh : fold x ∉ S.src.map fold)
    (hzeta : fold x ≠ moduleZeta d hd) :
    ∃ S' : CoreState d hd i0,
      x ∈ S'.src ∧
      S.src.length < S'.src.length ∧
      S.Bsq ≤ S'.Bsq := by
  let P := pendingOfPoint S x hxrat hfresh hzeta
  obtain ⟨n,hn⟩ := exists_protectedTower_ready P
  let Q := protectedTower P n
  have hCQ : Q.2.C = P.C := by
    simpa [Q] using protectedTower_pending_C P n
  have hxQ : Q.2.x = P.x := by
    simpa [Q] using protectedTower_pending_x P n
  have hnQ : Q.2.C ≤ Q.1.Bsq := by
    rw [hCQ]
    simpa [Q] using hn
  let S' := insertReadyPending Q.2 hnQ
  refine ⟨S', ?_, ?_, ?_⟩
  · change x ∈ Q.1.src ++ [Q.2.x]
    rw [List.mem_append, List.mem_singleton]
    right
    have hPx : P.x = x := by rfl
    exact (hxQ.trans hPx).symm
  · have hlenTower : Q.1.src.length = S.src.length + 5*n := by
      simpa [Q] using protectedTower_length P n
    simp [S', insertReadyPending]
    omega
  · have hrec := protectedTower_record_lower P n
    have : S.Bsq ≤ Q.1.Bsq := by
      have hn0 : 0 ≤ (n:ℝ)/64 := by positivity
      nlinarith
    simpa [S', insertReadyPending] using this

end Ulam165

/-! ==========================================================================
## Completion layer: local dense insertion by finite avoidance

For every current finite core state and every requested sphere point `y`, we
construct a point `x` arbitrarily close to `y` whose fold image is new and is
not the module accumulation point.  The construction is explicit.  If the
head of `y` is nonzero we radially scale the entire head by a scalar `r<1`
chosen outside a finite forbidden list.  If the head vanishes (so `y` is a
pole), we insert a small first head coordinate.  In both cases the last
coordinate is restored by the square root with the sign of the requested
point.
========================================================================== -/

namespace Ulam165
open Sphere
open Set Filter
open scoped BigOperators Topology

variable {d : ℕ}

/-- Choose a rational point in a real interval while avoiding a finite list of
forbidden real values. -/
lemma exists_rat_btwn_avoid_list (F : List ℝ) {a b : ℝ} (hab : a < b) :
    ∃ q : ℚ, a < (q:ℝ) ∧ (q:ℝ) < b ∧ (q:ℝ) ∉ F := by
  revert a b
  induction F with
  | nil =>
      intro a b hab
      obtain ⟨q,haq,hqb⟩ := exists_rat_btwn hab
      exact ⟨q,haq,hqb,by simp⟩
  | cons c F ih =>
      intro a b hab
      by_cases hca : c ≤ a
      · obtain ⟨q,haq,hqb,hqF⟩ := ih hab
        refine ⟨q,haq,hqb,?_⟩
        simp only [List.mem_cons]
        intro h
        rcases h with hqc | hqF'
        · subst c
          linarith
        · exact hqF hqF'
      · by_cases hbc : b ≤ c
        · obtain ⟨q,haq,hqb,hqF⟩ := ih hab
          refine ⟨q,haq,hqb,?_⟩
          simp only [List.mem_cons]
          intro h
          rcases h with hqc | hqF'
          · subst c
            linarith
          · exact hqF hqF'
        · have hac : a < c := lt_of_not_ge hca
          have hcb : c < b := lt_of_not_ge hbc
          obtain ⟨q,haq,hqc,hqF⟩ := ih hac
          refine ⟨q,haq,lt_trans hqc hcb,?_⟩
          simp only [List.mem_cons]
          intro h
          rcases h with hqc' | hqF'
          · exact (ne_of_lt hqc) hqc'
          · exact hqF hqF'

/-- Squared norm of the equatorial/head coordinates of a sphere point. -/
def headEnergy (x : Sphere d) : ℝ := ∑ i, x.1.1 i ^ 2

lemma headEnergy_nonneg (x : Sphere d) : 0 ≤ headEnergy x := by
  unfold headEnergy
  positivity

lemma headEnergy_add_last_sq (x : Sphere d) :
    headEnergy x + x.1.2^2 = 1 := by
  exact normSq_val x

lemma headEnergy_le_one (x : Sphere d) : headEnergy x ≤ 1 := by
  have h := headEnergy_add_last_sq x
  nlinarith [sq_nonneg x.1.2]

lemma head_coord_eq_zero_of_energy_zero {x : Sphere d}
    (hE : headEnergy x = 0) (i : Fin d) : x.1.1 i = 0 := by
  have hi : x.1.1 i ^ 2 ≤ headEnergy x := by
    unfold headEnergy
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x.1.1 j)) (Finset.mem_univ i)
  rw [hE] at hi
  nlinarith [sq_nonneg (x.1.1 i)]

lemma exists_nonzero_head_of_energy_pos {x : Sphere d}
    (hE : 0 < headEnergy x) : ∃ i : Fin d, x.1.1 i ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hz : headEnergy x = 0 := by
    unfold headEnergy
    simp [h]
  linarith

/-- Radially scale the head of a non-polar sphere point and restore the last
coordinate with the original sign.  It is defined for every `0 ≤ r ≤ 1`. -/
def radialPerturb (y : Sphere d) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Sphere d := by
  let A := headEnergy y
  have hA0 : 0 ≤ A := headEnergy_nonneg y
  have hA1 : A ≤ 1 := headEnergy_le_one y
  have hr2 : r^2 ≤ 1 := by nlinarith [sq_nonneg r, sq_nonneg (1-r)]
  have hrad : 0 ≤ 1 - r^2*A := by
    have hm : r^2*A ≤ 1*A := mul_le_mul_of_nonneg_right hr2 hA0
    nlinarith
  let L : ℝ := if 0 ≤ y.1.2 then Real.sqrt (1-r^2*A)
    else -Real.sqrt (1-r^2*A)
  refine ⟨((fun i => r*y.1.1 i), L), ?_⟩
  unfold normSq
  have hhead : (∑ i, (r*y.1.1 i)^2) = r^2*A := by
    calc
      (∑ i, (r*y.1.1 i)^2) = ∑ i, r^2 * (y.1.1 i)^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = r^2 * (∑ i, (y.1.1 i)^2) := by
        rw [Finset.mul_sum]
      _ = r^2*A := by rfl
  have hL : L^2 = 1-r^2*A := by
    dsimp [L]
    split_ifs <;> nlinarith [Real.sq_sqrt hrad]
  rw [hhead,hL]
  ring

@[simp] lemma radialPerturb_head (y : Sphere d) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (i : Fin d) :
    (radialPerturb y r hr0 hr1).1.1 i = r*y.1.1 i := rfl

/-- Quantitative radial-perturbation estimate. -/
lemma radialPerturb_distSq_le (y : Sphere d) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    distSq (radialPerturb y r hr0 hr1) y ≤
      (1-r)^2 + (1-r^2) := by
  let A := headEnergy y
  have hA0 : 0 ≤ A := headEnergy_nonneg y
  have hA1 : A ≤ 1 := headEnergy_le_one y
  have hy : A + y.1.2^2 = 1 := headEnergy_add_last_sq y
  have hr2 : r^2 ≤ 1 := by nlinarith [sq_nonneg r, sq_nonneg (1-r)]
  have hrr0 : 0 ≤ 1-r^2 := by linarith
  have hrad : 0 ≤ 1-r^2*A := by
    have hm := mul_le_mul_of_nonneg_right hr2 hA0
    have hm' : r^2*A ≤ A := by simpa using hm
    linarith
  let V := Real.sqrt (1-r^2*A)
  have hV0 : 0 ≤ V := Real.sqrt_nonneg _
  have hV2 : V^2 = 1-r^2*A := by
    dsimp [V]
    exact Real.sq_sqrt hrad
  have hbase : y.1.2^2 ≤ 1-r^2*A := by
    nlinarith [mul_nonneg hA0 hrr0]
  have habs : |y.1.2| ≤ V := by
    have hs := Real.sqrt_le_sqrt hbase
    simpa [V, Real.sqrt_sq_eq_abs] using hs
  have hhead :
      (∑ i, ((radialPerturb y r hr0 hr1).1.1 i - y.1.1 i)^2) =
        (1-r)^2*A := by
    calc
      (∑ i, ((radialPerturb y r hr0 hr1).1.1 i - y.1.1 i)^2) =
          ∑ i, ((r-1)*y.1.1 i)^2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [radialPerturb_head]
            ring
      _ = ∑ i, (1-r)^2 * (y.1.1 i)^2 := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (1-r)^2 * (∑ i, (y.1.1 i)^2) := by
            rw [Finset.mul_sum]
      _ = (1-r)^2*A := by rfl
  have hlast :
      ((radialPerturb y r hr0 hr1).1.2 - y.1.2)^2 ≤ A*(1-r^2) := by
    by_cases hy0 : 0 ≤ y.1.2
    · have habs' : y.1.2 ≤ V := by simpa [abs_of_nonneg hy0] using habs
      have hlastval : (radialPerturb y r hr0 hr1).1.2 = V := by
        simp [radialPerturb, hy0, A, V]
      rw [hlastval]
      nlinarith
    · have hyneg : y.1.2 < 0 := lt_of_not_ge hy0
      have habs' : -y.1.2 ≤ V := by simpa [abs_of_neg hyneg] using habs
      have hlastval : (radialPerturb y r hr0 hr1).1.2 = -V := by
        simp [radialPerturb, hy0, A, V]
      rw [hlastval]
      nlinarith
  have hheadB : (1-r)^2*A ≤ (1-r)^2 := by
    have hm := mul_le_mul_of_nonneg_left hA1 (sq_nonneg (1-r))
    simpa using hm
  have hlastB : A*(1-r^2) ≤ 1-r^2 := by
    have hm := mul_le_mul_of_nonneg_right hA1 hrr0
    simpa using hm
  unfold distSq
  rw [hhead]
  nlinarith

/-- Pole perturbation: insert a small coordinate at `idx0` and restore the last
coordinate with its original sign. -/
def polePerturb (hd : 2 ≤ d) (y : Sphere d) (_hE : headEnergy y = 0)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Sphere d := by
  let i0 : Fin d := idx0 d (le_trans (by norm_num) hd)
  have hrad : 0 ≤ 1-t^2 := by nlinarith [sq_nonneg t, sq_nonneg (1-t)]
  let L : ℝ := if 0 ≤ y.1.2 then Real.sqrt (1-t^2) else -Real.sqrt (1-t^2)
  refine ⟨((fun j => if j=i0 then t else 0), L), ?_⟩
  unfold normSq
  have hhead : (∑ j : Fin d, (if j=i0 then t else 0)^2) = t^2 := by
    simp
  have hL : L^2 = 1-t^2 := by
    dsimp [L]
    split_ifs <;> nlinarith [Real.sq_sqrt hrad]
  rw [hhead,hL]
  ring

@[simp] lemma polePerturb_head_idx0 (hd : 2 ≤ d) (y : Sphere d)
    (hE : headEnergy y = 0) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (polePerturb hd y hE t ht0 ht1).1.1 (idx0 d (le_trans (by norm_num) hd)) = t := by
  simp [polePerturb]

/-- Quantitative estimate at a pole. -/
lemma polePerturb_distSq_le (hd : 2 ≤ d) (y : Sphere d)
    (hE : headEnergy y = 0) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    distSq (polePerturb hd y hE t ht0 ht1) y ≤ 2*t^2 := by
  let i0 : Fin d := idx0 d (le_trans (by norm_num) hd)
  have hlastsq : y.1.2^2 = 1 := by
    have h := headEnergy_add_last_sq y
    rw [hE] at h
    linarith
  have hrad : 0 ≤ 1-t^2 := by nlinarith [sq_nonneg t, sq_nonneg (1-t)]
  let V := Real.sqrt (1-t^2)
  have hV0 : 0 ≤ V := Real.sqrt_nonneg _
  have hV2 : V^2 = 1-t^2 := by
    dsimp [V]
    exact Real.sq_sqrt hrad
  have hheadzero : ∀ j : Fin d, y.1.1 j = 0 :=
    fun j => head_coord_eq_zero_of_energy_zero hE j
  have hhead :
      (∑ j, ((polePerturb hd y hE t ht0 ht1).1.1 j - y.1.1 j)^2) = t^2 := by
    simp [polePerturb, hheadzero]
  have hlast :
      ((polePerturb hd y hE t ht0 ht1).1.2-y.1.2)^2 ≤ t^2 := by
    by_cases hy0 : 0 ≤ y.1.2
    · have hyone : y.1.2 = 1 := by nlinarith
      have hV1 : V ≤ 1 := by nlinarith
      have hval : (polePerturb hd y hE t ht0 ht1).1.2 = V := by
        simp [polePerturb, hy0, V]
      rw [hval,hyone]
      nlinarith
    · have hyneg : y.1.2 < 0 := lt_of_not_ge hy0
      have hymone : y.1.2 = -1 := by nlinarith
      have hV1 : V ≤ 1 := by nlinarith
      have hval : (polePerturb hd y hE t ht0 ht1).1.2 = -V := by
        simp [polePerturb, hy0, V]
      rw [hval,hymone]
      nlinarith
  unfold distSq
  rw [hhead]
  linarith

/-- Forbidden radial scale values detected in one nonzero head coordinate. -/
def radialBadScalars {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) (y : Sphere d) (i : Fin d) : List ℝ :=
  S.src.map (fun p => (fold p).1.1 i / y.1.1 i) ++
    [(moduleZeta d hd).1.1 i / y.1.1 i]

/-- Forbidden first-head values in the pole perturbation. -/
def poleBadScalars {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) : List ℝ :=
  let j0 : Fin d := idx0 d (le_trans (by norm_num) hd)
  S.src.map (fun p => (fold p).1.1 j0) ++ [(moduleZeta d hd).1.1 j0]

/-- A radial scale outside `radialBadScalars` produces a new fold image. -/
lemma radialPerturb_fold_fresh
    {hd : 2 ≤ d} {i0 : Fin d} (S : CoreState d hd i0)
    (y : Sphere d) (i : Fin d) (hyi : y.1.1 i ≠ 0)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (havoid : r ∉ radialBadScalars S y i) :
    fold (radialPerturb y r hr0 hr1) ∉ S.src.map fold := by
  intro hmem
  rcases List.mem_map.mp hmem with ⟨p,hp,heq⟩
  have hc := congrArg (fun z : Sphere d => z.1.1 i) heq
  simp only [fold_head, radialPerturb_head] at hc
  have hrbad : r = (fold p).1.1 i / y.1.1 i := by
    field_simp [hyi]
    exact hc.symm
  apply havoid
  unfold radialBadScalars
  rw [List.mem_append]
  left
  exact List.mem_map.mpr ⟨p,hp,hrbad.symm⟩

lemma radialPerturb_ne_zeta
    {hd : 2 ≤ d} {i0 : Fin d} (S : CoreState d hd i0)
    (y : Sphere d) (i : Fin d) (hyi : y.1.1 i ≠ 0)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (havoid : r ∉ radialBadScalars S y i) :
    fold (radialPerturb y r hr0 hr1) ≠ moduleZeta d hd := by
  intro heq
  have hc := congrArg (fun z : Sphere d => z.1.1 i) heq
  simp only [fold_head, radialPerturb_head] at hc
  have hrbad : r = (moduleZeta d hd).1.1 i / y.1.1 i := by
    field_simp [hyi]
    exact hc
  apply havoid
  unfold radialBadScalars
  rw [List.mem_append]
  right
  simp [hrbad]

lemma polePerturb_fold_fresh
    {hd : 2 ≤ d} {i0 : Fin d} (S : CoreState d hd i0)
    (y : Sphere d) (hE : headEnergy y = 0)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (havoid : t ∉ poleBadScalars S) :
    fold (polePerturb hd y hE t ht0 ht1) ∉ S.src.map fold := by
  intro hmem
  rcases List.mem_map.mp hmem with ⟨p,hp,heq⟩
  let j0 : Fin d := idx0 d (le_trans (by norm_num) hd)
  have hc := congrArg (fun z : Sphere d => z.1.1 j0) heq
  have htval : t = (fold p).1.1 j0 := by
    simpa [j0] using hc.symm
  apply havoid
  unfold poleBadScalars
  rw [List.mem_append]
  left
  exact List.mem_map.mpr ⟨p,hp,htval.symm⟩

lemma polePerturb_ne_zeta
    {hd : 2 ≤ d} {i0 : Fin d} (S : CoreState d hd i0)
    (y : Sphere d) (hE : headEnergy y = 0)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (havoid : t ∉ poleBadScalars S) :
    fold (polePerturb hd y hE t ht0 ht1) ≠ moduleZeta d hd := by
  intro heq
  let j0 : Fin d := idx0 d (le_trans (by norm_num) hd)
  have hc := congrArg (fun z : Sphere d => z.1.1 j0) heq
  have htval : t = (moduleZeta d hd).1.1 j0 := by
    simpa [j0] using hc
  apply havoid
  unfold poleBadScalars
  rw [List.mem_append]
  right
  exact List.mem_singleton.mpr htval

/-- Local density lemma needed by the global construction: every requested
point has an arbitrarily close point whose fold image is fresh and avoids the
fixed module accumulation point. -/
theorem exists_near_foldFresh
    {hd : 2 ≤ d} {i0 : Fin d} (S : CoreState d hd i0)
    (y : Sphere d) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : Sphere d,
      distSq x y < ε ∧
      fold x ∉ S.src.map fold ∧
      fold x ≠ moduleZeta d hd := by
  by_cases hE0 : headEnergy y = 0
  · let δ : ℝ := min (1/2) (ε/4)
    have hδ0 : 0 < δ := by
      dsimp [δ]
      exact lt_min (by norm_num) (by positivity)
    have hδ1 : δ ≤ 1/2 := min_le_left _ _
    have hδε : δ ≤ ε/4 := min_le_right _ _
    obtain ⟨q,hq0,hqδ,havoid⟩ :=
      exists_rat_btwn_avoid_list (poleBadScalars S) hδ0
    let t : ℝ := (q:ℝ)
    have ht0 : 0 ≤ t := le_of_lt hq0
    have ht1 : t ≤ 1 := by linarith
    let x := polePerturb hd y hE0 t ht0 ht1
    refine ⟨x,?_,?_,?_⟩
    · have hdle := polePerturb_distSq_le hd y hE0 t ht0 ht1
      have htlt1 : t < 1 := by linarith
      have ht2lt : t^2 < t := by
        calc
          t^2 = t*t := by ring
          _ < t*1 := mul_lt_mul_of_pos_left htlt1 hq0
          _ = t := by ring
      have : 2*t^2 < ε := by nlinarith
      exact lt_of_le_of_lt hdle this
    · exact polePerturb_fold_fresh S y hE0 t ht0 ht1 havoid
    · exact polePerturb_ne_zeta S y hE0 t ht0 ht1 havoid
  · have hEpos : 0 < headEnergy y :=
      lt_of_le_of_ne (headEnergy_nonneg y) (Ne.symm hE0)
    obtain ⟨i,hyi⟩ := exists_nonzero_head_of_energy_pos hEpos
    let δ : ℝ := min (1/2) (ε/4)
    have hδ0 : 0 < δ := by
      dsimp [δ]
      exact lt_min (by norm_num) (by positivity)
    have hδhalf : δ ≤ 1/2 := min_le_left _ _
    have hδε : δ ≤ ε/4 := min_le_right _ _
    have hab : 1-δ < 1 := by linarith
    obtain ⟨q,hql,hqu,havoid⟩ :=
      exists_rat_btwn_avoid_list (radialBadScalars S y i) hab
    let r : ℝ := (q:ℝ)
    have hr0 : 0 ≤ r := by linarith
    have hr1 : r ≤ 1 := le_of_lt hqu
    let x := radialPerturb y r hr0 hr1
    refine ⟨x,?_,?_,?_⟩
    · have hdle := radialPerturb_distSq_le y r hr0 hr1
      let z := 1-r
      have hz0 : 0 < z := by dsimp [z]; linarith
      have hzδ : z < δ := by dsimp [z]; linarith
      have hz1 : z < 1 := by dsimp [z]; linarith
      have hfirst : z^2 < δ := by
        calc
          z^2 = z*z := by ring
          _ < δ*z := mul_lt_mul_of_pos_right hzδ hz0
          _ < δ*1 := mul_lt_mul_of_pos_left hz1 hδ0
          _ = δ := by ring
      have hrp : 0 < 1+r := by linarith
      have hrp2 : 1+r < 2 := by linarith
      have hsecond : 1-r^2 < 2*δ := by
        calc
          1-r^2 = z*(1+r) := by dsimp [z]; ring
          _ < δ*(1+r) := mul_lt_mul_of_pos_right hzδ hrp
          _ < δ*2 := mul_lt_mul_of_pos_left hrp2 hδ0
          _ = 2*δ := by ring
      have hsum : (1-r)^2 + (1-r^2) < ε := by
        have hzdef : z = 1-r := rfl
        rw [← hzdef]
        nlinarith
      exact lt_of_le_of_lt hdle hsum
    · exact radialPerturb_fold_fresh S y i hyi r hr0 hr1 havoid
    · exact radialPerturb_ne_zeta S y i hyi r hr0 hr1 havoid

/-! --------------------------------------------------------------------------
### Rational stereographic density

The local perturbation lemma above gives an open nonempty set of admissible
points.  We now prove that rational points meet every such set.  This is done
with the classical rational parametrization of the sphere.
---------------------------------------------------------------------------- -/

/-- Coordinatewise inclusion of a rational vector into a real vector. -/
def ratVecCast {d : ℕ} : (Fin d → ℚ) → (Fin d → ℝ) :=
  Pi.map (fun _ : Fin d => (Rat.cast : ℚ → ℝ))

/-- Rational vectors are dense in the finite real coordinate space. -/
theorem ratVecCast_denseRange (d : ℕ) :
    DenseRange (@ratVecCast d) := by
  exact DenseRange.piMap (fun _ : Fin d => Rat.denseRange_cast)

/-- Squared norm of a stereographic parameter. -/
def stereoEnergy {d : ℕ} (u : Fin d → ℝ) : ℝ := ∑ i, (u i)^2

lemma stereoEnergy_nonneg {d : ℕ} (u : Fin d → ℝ) : 0 ≤ stereoEnergy u := by
  unfold stereoEnergy
  positivity

lemma stereoDen_pos {d : ℕ} (u : Fin d → ℝ) : 0 < 1 + stereoEnergy u := by
  have := stereoEnergy_nonneg u
  linarith

/-- Explicit stereographic parametrization from the south chart. -/
def realStereo {d : ℕ} (u : Fin d → ℝ) : Sphere d := by
  let R : ℝ := stereoEnergy u
  let D : ℝ := 1 + R
  have hDpos : 0 < D := by
    dsimp [D,R]
    exact stereoDen_pos u
  have hD : D ≠ 0 := ne_of_gt hDpos
  refine ⟨(fun i => 2*u i/D, (R-1)/D), ?_⟩
  unfold normSq
  have hsum : (∑ i, (2 * u i / D)^2) = 4*R/D^2 := by
    calc
      (∑ i, (2 * u i / D)^2) = ∑ i, (4 * (u i)^2) / D^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [hD]
        ring
      _ = (∑ i, 4 * (u i)^2) / D^2 := by
        rw [Finset.sum_div]
      _ = 4 * (∑ i, (u i)^2) / D^2 := by
        rw [Finset.mul_sum]
      _ = 4*R/D^2 := by rfl
  rw [hsum]
  have hDR : D = 1+R := rfl
  field_simp [hD]
  rw [hDR]
  ring

@[simp] lemma realStereo_head {d : ℕ} (u : Fin d → ℝ) (i : Fin d) :
    (realStereo u).1.1 i = 2*u i/(1+stereoEnergy u) := rfl

@[simp] lemma realStereo_last {d : ℕ} (u : Fin d → ℝ) :
    (realStereo u).1.2 = (stereoEnergy u-1)/(1+stereoEnergy u) := rfl

@[fun_prop] lemma continuous_stereoEnergy {d : ℕ} :
    Continuous (@stereoEnergy d) := by
  unfold stereoEnergy
  fun_prop

lemma continuous_realStereo {d : ℕ} :
    Continuous (@realStereo d) := by
  have hD : Continuous (fun u : Fin d → ℝ => 1 + stereoEnergy u) :=
    continuous_const.add continuous_stereoEnergy
  have hD0 : ∀ u : Fin d → ℝ, 1 + stereoEnergy u ≠ 0 :=
    fun u => ne_of_gt (stereoDen_pos u)
  have hhead : Continuous
      (fun u : Fin d → ℝ => fun i => 2 * u i / (1 + stereoEnergy u)) := by
    apply continuous_pi
    intro i
    exact (continuous_const.mul (continuous_apply i)).div₀ hD hD0
  have hlast : Continuous
      (fun u : Fin d → ℝ => (stereoEnergy u - 1) / (1 + stereoEnergy u)) := by
    exact (continuous_stereoEnergy.sub continuous_const).div₀ hD hD0
  apply Continuous.subtype_mk
  exact continuous_prodMk.mpr ⟨hhead, hlast⟩

/-- Inverse chart coordinates away from the north pole. -/
def stereoInv {d : ℕ} (x : Sphere d) : Fin d → ℝ :=
  fun i => x.1.1 i / (1-x.1.2)

lemma eq_north_of_last_eq_one {d : ℕ} {x : Sphere d} (hx : x.1.2 = 1) :
    x = north d := by
  have hs : (∑ i, (x.1.1 i)^2) = 0 := by
    have hn := normSq_val x
    rw [hx] at hn
    nlinarith
  have hh : ∀ i, x.1.1 i = 0 := by
    intro i
    have hi : (x.1.1 i)^2 ≤ ∑ j, (x.1.1 j)^2 := by
      exact Finset.single_le_sum (fun j _ => sq_nonneg (x.1.1 j)) (Finset.mem_univ i)
    have hsq : (x.1.1 i)^2 = 0 := by nlinarith [hs]
    nlinarith
  apply Sphere.ext
  · funext i
    simp [north,hh i]
  · simp [north,hx]

lemma one_sub_last_ne_zero_of_ne_north {d : ℕ} {x : Sphere d}
    (hx : x ≠ north d) : 1-x.1.2 ≠ 0 := by
  intro h
  have hx1 : x.1.2 = 1 := by linarith
  exact hx (eq_north_of_last_eq_one hx1)

lemma stereoEnergy_inv {d : ℕ} {x : Sphere d} (hx : x ≠ north d) :
    stereoEnergy (stereoInv x) = (1+x.1.2)/(1-x.1.2) := by
  let z := x.1.2
  have hden : 1-z ≠ 0 := by
    simpa [z] using one_sub_last_ne_zero_of_ne_north hx
  have hsphere := normSq_val x
  have hhead : (∑ i, (x.1.1 i)^2) = (1-z)*(1+z) := by
    dsimp [z] at hsphere ⊢
    nlinarith
  unfold stereoEnergy stereoInv
  have hsum : (∑ i, (x.1.1 i / (1-z))^2) =
      (∑ i, (x.1.1 i)^2) / (1-z)^2 := by
    calc
      (∑ i, (x.1.1 i / (1-z))^2) =
          ∑ i, (x.1.1 i)^2 / (1-z)^2 := by
            apply Finset.sum_congr rfl
            intro i hi
            field_simp [hden]
      _ = (∑ i, (x.1.1 i)^2) / (1-z)^2 := by
            rw [Finset.sum_div]
  rw [hsum,hhead]
  dsimp [z] at hden ⊢
  field_simp [hden]

lemma realStereo_stereoInv {d : ℕ} {x : Sphere d} (hx : x ≠ north d) :
    realStereo (stereoInv x) = x := by
  let z := x.1.2
  have hden : 1-z ≠ 0 := by
    simpa [z] using one_sub_last_ne_zero_of_ne_north hx
  have hE := stereoEnergy_inv hx
  apply Sphere.ext
  · funext i
    simp only [realStereo_head]
    rw [hE]
    unfold stereoInv
    dsimp [z] at hden ⊢
    field_simp [hden]
    ring
  · simp only [realStereo_last]
    rw [hE]
    dsimp [z] at hden ⊢
    field_simp [hden]
    ring

lemma stereoEnergy_ratVecCast {d : ℕ} (q : Fin d → ℚ) :
    stereoEnergy (ratVecCast q) = ((∑ i, (q i)^2 : ℚ) : ℝ) := by
  unfold stereoEnergy ratVecCast
  simp only [Pi.map_apply]
  rw [Rat.cast_sum]
  simp only [Rat.cast_pow]

/-- Every rational stereographic parameter gives a rational sphere point. -/
lemma rational_realStereo_ratVecCast {d : ℕ} (q : Fin d → ℚ) :
    RationalPoint (realStereo (ratVecCast q)) := by
  let Rq : ℚ := ∑ i, (q i)^2
  have hE : stereoEnergy (ratVecCast q) = (Rq:ℝ) := by
    simpa [Rq] using stereoEnergy_ratVecCast q
  constructor
  · intro i
    refine ⟨2*q i/(1+Rq), ?_⟩
    simp only [realStereo_head]
    rw [hE]
    norm_num [ratVecCast, Pi.map_apply]
  · refine ⟨(Rq-1)/(1+Rq), ?_⟩
    simp only [realStereo_last]
    rw [hE]
    norm_num [ratVecCast, Pi.map_apply]

@[fun_prop] lemma continuous_distSq_left {d : ℕ} (a : Sphere d) :
    Continuous (fun x : Sphere d => distSq x a) := by
  unfold distSq
  fun_prop

/-- The fold map is continuous. -/
@[fun_prop] lemma continuous_fold {d : ℕ} : Continuous (@fold d) := by
  unfold fold
  apply Continuous.subtype_mk
  fun_prop

lemma isOpen_fold_ne {d : ℕ} (a : Sphere d) :
    IsOpen {x : Sphere d | fold x ≠ a} := by
  have hc : Continuous (fun x : Sphere d => distSq (fold x) a) :=
    (continuous_distSq_left a).comp continuous_fold
  have heq : {x : Sphere d | fold x ≠ a} =
      {x : Sphere d | 0 < distSq (fold x) a} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      exact distSq_pos h
    · intro h hp
      subst hp
      rw [distSq_self] at h
      exact (lt_irrefl 0) h
  rw [heq]
  exact isOpen_lt continuous_const hc

lemma isOpen_fold_not_mem {d : ℕ} (L : List (Sphere d)) :
    IsOpen {x : Sphere d | fold x ∉ L} := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have ha := isOpen_fold_ne (d:=d) a
      simpa [List.mem_cons, not_or, Set.ofPred_and] using ha.inter ih

/-- Squared chordal balls are open in the inherited Euclidean topology. -/
lemma isOpen_distSq_lt (y : Sphere d) (ε : ℝ) :
    IsOpen {x : Sphere d | distSq x y < ε} := by
  have hc : Continuous (fun x : Sphere d => distSq x y) := by
    unfold distSq
    fun_prop
  exact isOpen_lt hc continuous_const

/-- The admissible local set used for rational density insertion is open. -/
lemma isOpen_densityAdmissible
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) (y : Sphere d) (ε : ℝ) :
    IsOpen {x : Sphere d |
      distSq x y < ε ∧
      fold x ∉ S.src.map fold ∧
      fold x ≠ moduleZeta d hd} := by
  have hdist := isOpen_distSq_lt y ε
  have hold := isOpen_fold_not_mem (S.src.map fold)
  have hz := isOpen_fold_ne (moduleZeta d hd)
  simpa [Set.ofPred_and] using hdist.inter (hold.inter hz)

/-- Rational strengthening of `exists_near_foldFresh`. -/
theorem exists_near_rational_foldFresh
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d} (S : CoreState d hd i0)
    (y : Sphere d) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : Sphere d,
      RationalPoint x ∧
      distSq x y < ε ∧
      fold x ∉ S.src.map fold ∧
      fold x ≠ moduleZeta d hd := by
  obtain ⟨x0,hnear,hfresh,hzeta⟩ := exists_near_foldFresh S y hε
  let U : Set (Sphere d) := {x |
    distSq x y < ε ∧
    fold x ∉ S.src.map fold ∧
    fold x ≠ moduleZeta d hd}
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_densityAdmissible S y ε
  have hx0U : x0 ∈ U := by
    exact ⟨hnear,hfresh,hzeta⟩
  by_cases hxn : x0 = north d
  · subst x0
    refine ⟨north d, rational_north, ?_⟩
    exact hx0U
  · let u0 : Fin d → ℝ := stereoInv x0
    have hst : realStereo u0 = x0 := by
      dsimp [u0]
      exact realStereo_stereoInv hxn
    let V : Set (Fin d → ℝ) := realStereo ⁻¹' U
    have hVopen : IsOpen V := hUopen.preimage continuous_realStereo
    have hu0V : u0 ∈ V := by
      change realStereo u0 ∈ U
      rw [hst]
      exact hx0U
    have hVne : V.Nonempty := ⟨u0,hu0V⟩
    obtain ⟨q,hqV⟩ := (ratVecCast_denseRange d).exists_mem_open hVopen hVne
    refine ⟨realStereo (ratVecCast q), rational_realStereo_ratVecCast q, ?_⟩
    exact hqV

end Ulam165

/-! ==========================================================================
## Completion layer: dense phase recursion and direct-limit source sequence
========================================================================== -/

namespace Ulam165
open Sphere
open Set Filter
open scoped BigOperators Topology

variable {d : ℕ}

/-- Explicit append-extension relation used instead of an abstract list-prefix
API, so the direct-limit bookkeeping remains transparent. -/
def ListExtends {α : Type*} (a b : List α) : Prop := ∃ t, b = a ++ t

lemma ListExtends.refl {α : Type*} (a : List α) : ListExtends a a := by
  exact ⟨[],by simp⟩

lemma ListExtends.trans {α : Type*} {a b c : List α}
    (hab : ListExtends a b) (hbc : ListExtends b c) : ListExtends a c := by
  rcases hab with ⟨u,rfl⟩
  rcases hbc with ⟨v,rfl⟩
  exact ⟨u++v,by simp [List.append_assoc]⟩

lemma ListExtends.length_le {α : Type*} {a b : List α}
    (h : ListExtends a b) : a.length ≤ b.length := by
  rcases h with ⟨u,rfl⟩
  simp

/-- Every protected tower stage is obtained by appending a finite block to the
original source. -/
theorem protectedTower_extends
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    {S : CoreState d hd i0} (P : PendingState S) (n : ℕ) :
    ListExtends S.src (protectedTower P n).1.src := by
  induction n with
  | zero => exact ListExtends.refl _
  | succ n ih =>
      simp only [protectedTower]
      let Q := protectedTower P n
      let T := chooseProtectedFreshStep Q.2
      rcases ih with ⟨u,hu⟩
      refine ⟨u ++ moduleSources (canonicalFrame d hd) (freshScalars T.s T.M), ?_⟩
      change T.nextCore.src = S.src ++
        (u ++ moduleSources (canonicalFrame d hd) (freshScalars T.s T.M))
      rw [T.nextCore_src_eq, hu]
      simp [List.append_assoc]

/-- Strengthened density-point extension: the new state is literally the old
source followed by a nonempty finite block, and the requested point belongs to
that new block. -/
theorem exists_core_extension_block
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) (x : Sphere d)
    (hxrat : RationalPoint x)
    (hfresh : fold x ∉ S.src.map fold)
    (hzeta : fold x ≠ moduleZeta d hd) :
    ∃ (S' : CoreState d hd i0) (block : List (Sphere d)),
      block ≠ [] ∧
      S'.src = S.src ++ block ∧
      x ∈ block ∧
      S.Bsq ≤ S'.Bsq := by
  let P := pendingOfPoint S x hxrat hfresh hzeta
  obtain ⟨n,hn⟩ := exists_protectedTower_ready P
  let Q := protectedTower P n
  have hCQ : Q.2.C = P.C := by
    simpa [Q] using protectedTower_pending_C P n
  have hxQ : Q.2.x = P.x := by
    simpa [Q] using protectedTower_pending_x P n
  have hnQ : Q.2.C ≤ Q.1.Bsq := by
    rw [hCQ]
    simpa [Q] using hn
  let S' := insertReadyPending Q.2 hnQ
  have hPx : P.x = x := by
    rfl
  rcases protectedTower_extends P n with ⟨u,hu⟩
  refine ⟨S',u++[x],?_,?_,?_,?_⟩
  · simp
  · change (insertReadyPending Q.2 hnQ).src = S.src ++ (u++[x])
    change Q.1.src ++ [Q.2.x] = S.src ++ (u++[x])
    rw [hxQ, hPx, hu]
    simp [List.append_assoc]
  · simp
  · have hrec := protectedTower_record_lower P n
    change S.Bsq ≤ Q.1.Bsq
    have hn0 : 0 ≤ (n:ℝ)/64 := by positivity
    nlinarith

/-- One completed density phase. -/
structure DensityStepData {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) (y : Sphere d) (ε : ℝ) where
  x : Sphere d
  x_rational : RationalPoint x
  near : distSq x y < ε
  next : CoreState d hd i0
  block : List (Sphere d)
  block_nonempty : block ≠ []
  next_src : next.src = S.src ++ block
  x_mem_block : x ∈ block
  B_mono : S.Bsq ≤ next.Bsq

/-- Every positive-precision request admits a completed density phase. -/
theorem exists_densityStepData
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) (y : Sphere d) {ε : ℝ} (hε : 0 < ε) :
    ∃ _D : DensityStepData S y ε, True := by
  obtain ⟨x,hxrat,hnear,hfresh,hzeta⟩ :=
    exists_near_rational_foldFresh S y hε
  obtain ⟨S',block,hbn,hsrc,hx,hB⟩ :=
    exists_core_extension_block S x hxrat hfresh hzeta
  exact ⟨{
    x := x
    x_rational := hxrat
    near := hnear
    next := S'
    block := block
    block_nonempty := hbn
    next_src := hsrc
    x_mem_block := hx
    B_mono := hB
  }, trivial⟩

noncomputable def chooseDensityStep
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) (y : Sphere d) (ε : ℝ) (hε : 0 < ε) :
    DensityStepData S y ε :=
  Classical.choose (exists_densityStepData S y hε)

/-- The sphere is nonempty in every dimension. -/
instance sphereNonempty (d : ℕ) : Nonempty (Sphere d) := ⟨north d⟩

/-- A dense request is repeated with all precisions using the natural pairing
function. -/
noncomputable def densityRequest (d : ℕ) (n : ℕ) : Sphere d :=
  TopologicalSpace.denseSeq (Sphere d) (Nat.unpair n).1

/-- Precision assigned to the second component of the pairing schedule. -/
def densityPrecision (n : ℕ) : ℝ :=
  1 / (((Nat.unpair n).2 + 1 : ℕ) : ℝ)

lemma densityPrecision_pos (n : ℕ) : 0 < densityPrecision n := by
  unfold densityPrecision
  positivity

/-- The mathlib dense request sequence is dense also in the explicit squared
chordal sense used in this development. -/
lemma denseRequest_chord_approx (d : ℕ) (y : Sphere d) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, distSq (TopologicalSpace.denseSeq (Sphere d) k) y < ε := by
  let U : Set (Sphere d) := {x | distSq x y < ε}
  have hUopen : IsOpen U := isOpen_distSq_lt y ε
  have hUne : U.Nonempty := by
    refine ⟨y,?_⟩
    simp [U,distSq_self,hε]
  obtain ⟨k,hk⟩ :=
    (TopologicalSpace.denseRange_denseSeq (Sphere d)).exists_mem_open hUopen hUne
  exact ⟨k,hk⟩

/-- Quantitative chordal density of the global source sequence. -/
def ChordDense {d : ℕ} (x : ℕ → Sphere d) : Prop :=
  ∀ y : Sphere d, ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, distSq (x n) y < ε

/-- Coarse squared triangle inequality for the explicit Euclidean chordal
distance. -/
lemma distSq_triangle_two (x y z : Sphere d) :
    distSq x z ≤ 2*distSq x y + 2*distSq y z := by
  have hsum :
      (∑ i, (x.1.1 i-z.1.1 i)^2) ≤
        ∑ i, (2*(x.1.1 i-y.1.1 i)^2 + 2*(y.1.1 i-z.1.1 i)^2) := by
    apply Finset.sum_le_sum
    intro i hi
    nlinarith [sq_nonneg ((x.1.1 i-y.1.1 i)-(y.1.1 i-z.1.1 i))]
  have hlast : (x.1.2-z.1.2)^2 ≤
      2*(x.1.2-y.1.2)^2 + 2*(y.1.2-z.1.2)^2 := by
    nlinarith [sq_nonneg ((x.1.2-y.1.2)-(y.1.2-z.1.2))]
  unfold distSq
  rw [Finset.sum_add_distrib] at hsum
  have hxsum : (∑ i, 2*(x.1.1 i-y.1.1 i)^2) =
      2*(∑ i, (x.1.1 i-y.1.1 i)^2) := by
    rw [Finset.mul_sum]
  have hysum : (∑ i, 2*(y.1.1 i-z.1.1 i)^2) =
      2*(∑ i, (y.1.1 i-z.1.1 i)^2) := by
    rw [Finset.mul_sum]
  rw [hxsum,hysum] at hsum
  nlinarith



end Ulam165

/-! ==========================================================================
## Completion layer: density phases with forced inverse-record growth

Each completed density phase is followed by one ordinary fresh module.  Thus
we retain the density point inserted by the protected construction and obtain
a strict record increase `> 1/64` at every phase.
========================================================================== -/

namespace Ulam165
open Sphere
open Set Filter
open scoped BigOperators Topology

variable {d : ℕ}

/-- One ordinary fresh-module step for a core state. -/
structure CoreFreshStepData {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) where
  s : ℚ
  M : ℚ
  Bnext : ℝ
  hs0 : 0 < s
  hs1 : s < 1/100
  hMpos : 0 < M
  hMl : S.Bsq - 1 + (5:ℝ)/256 < (M:ℝ)^2
  cert : FreshModuleCertificate S.src i0 S.Bsq Bnext
    (canonicalFrame d hd) (freshScalars s M)

theorem exists_coreFreshStepData
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) : ∃ _T : CoreFreshStepData S, True := by
  obtain ⟨M,hMpos,hMl,hMu⟩ := exists_positive_record_parameter S.Bsq S.B_ge
  obtain ⟨s,hs0,hs1,hO⟩ :=
    exists_small_rational_oldInteraction (d:=d) hd S.B_ge hMpos hMl S.zeta_avoid
  let u := freshScalars s M
  let Bnext : ℝ := ((2-2*u.cb)+4*u.h^2*u.cb)/(2-2*u.cb)
  have hC : FreshModuleCertificate S.src i0 S.Bsq Bnext
      (canonicalFrame d hd) u := by
    dsimp [u,Bnext]
    exact freshModuleCertificate_of_oldInteraction
      (d:=d) (src:=S.src) hd (i0:=i0) (B0sq:=S.Bsq)
      S.B_ge hs0 hs1 hMpos hMl hMu S.safe S.image_nodup hO
  exact ⟨{
    s := s
    M := M
    Bnext := Bnext
    hs0 := hs0
    hs1 := hs1
    hMpos := hMpos
    hMl := hMl
    cert := hC
  }, trivial⟩

noncomputable def chooseCoreFreshStep
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) : CoreFreshStepData S :=
  Classical.choose (exists_coreFreshStepData S)

namespace CoreFreshStepData

variable {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
  {S : CoreState d hd i0}

noncomputable def nextCore (T : CoreFreshStepData S) : CoreState d hd i0 := by
  let E := canonicalFrame d hd
  let u := freshScalars T.s T.M
  have happ := T.cert.apply_fresh_module S.built S.pos_mem S.neg_mem
    S.south_mem S.anchorA_mem S.inverse_exact
  refine {
    src := S.src ++ moduleSources E u
    Bsq := T.Bnext
    built := happ.1
    inverse_exact := happ.2
    safe := T.cert.full_safe
    image_nodup := T.cert.image_nodup
    rational := by
      intro p hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · exact S.rational p hp
      · exact T.cert.moduleSources_rational p hp
    zeta_avoid := moduleZeta_not_image_after_fresh (d:=d) hd S.zeta_avoid S.B_ge
      T.hs0 T.hs1 T.hMpos T.hMl
    pos_mem := fun i => List.mem_append_left _ (S.pos_mem i)
    neg_mem := fun i => List.mem_append_left _ (S.neg_mem i)
    south_mem := List.mem_append_left _ S.south_mem
    anchorA_mem := List.mem_append_left _ S.anchorA_mem
    B_ge := T.cert.Bsq_ge
  }

lemma nextCore_src_eq (T : CoreFreshStepData S) :
    T.nextCore.src = S.src ++
      moduleSources (canonicalFrame d hd) (freshScalars T.s T.M) := rfl

lemma nextCore_growth (T : CoreFreshStepData S) :
    (1:ℝ)/64 < T.nextCore.Bsq - S.Bsq := T.cert.record_inc_low

end CoreFreshStepData

/-- A density step followed by one forced fresh module. -/
structure StrongDensityStepData {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) (y : Sphere d) (ε : ℝ) where
  first : DensityStepData S y ε
  fresh : CoreFreshStepData first.next

namespace StrongDensityStepData

variable {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
  {S : CoreState d hd i0} {y : Sphere d} {ε : ℝ}

noncomputable def next (D : StrongDensityStepData S y ε) : CoreState d hd i0 :=
  D.fresh.nextCore

noncomputable def block (D : StrongDensityStepData S y ε) : List (Sphere d) :=
  D.first.block ++
    moduleSources (canonicalFrame d hd) (freshScalars D.fresh.s D.fresh.M)

lemma next_src (D : StrongDensityStepData S y ε) :
    D.next.src = S.src ++ D.block := by
  rw [next, D.fresh.nextCore_src_eq, D.first.next_src]
  simp [block,List.append_assoc]

lemma block_nonempty (D : StrongDensityStepData S y ε) : D.block ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp [block, moduleSources, scaffoldSources] at hl

lemma chosen_mem_block (D : StrongDensityStepData S y ε) :
    D.first.x ∈ D.block := by
  unfold block
  exact List.mem_append_left _ D.first.x_mem_block

lemma chosen_near (D : StrongDensityStepData S y ε) :
    distSq D.first.x y < ε := D.first.near

lemma B_growth (D : StrongDensityStepData S y ε) :
    (1:ℝ)/64 < D.next.Bsq - S.Bsq := by
  have hf := D.fresh.nextCore_growth
  have hm := D.first.B_mono
  unfold next at hf ⊢
  nlinarith

end StrongDensityStepData

 theorem exists_strongDensityStepData
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) (y : Sphere d) {ε : ℝ} (hε : 0 < ε) :
    ∃ _D : StrongDensityStepData S y ε, True := by
  let A := chooseDensityStep S y ε hε
  let F := chooseCoreFreshStep A.next
  exact ⟨{first := A, fresh := F}, trivial⟩

noncomputable def chooseStrongDensityStep
    {d : ℕ} {hd : 2 ≤ d} {i0 : Fin d}
    (S : CoreState d hd i0) (y : Sphere d) (ε : ℝ) (hε : 0 < ε) :
    StrongDensityStepData S y ε :=
  Classical.choose (exists_strongDensityStepData S y hε)

/-- Final phase-state chain used by the main theorem. -/
noncomputable def finalState (d : ℕ) (hd : 2 ≤ d) :
    ℕ → CoreState d hd (idx0 d (le_trans (by norm_num) hd))
  | 0 => initialCoreState d hd
  | n+1 =>
      (chooseStrongDensityStep (finalState d hd n)
        (densityRequest d n) (densityPrecision n) (densityPrecision_pos n)).next

noncomputable def finalBlock (d : ℕ) (hd : 2 ≤ d) (n : ℕ) : List (Sphere d) :=
  (chooseStrongDensityStep (finalState d hd n)
    (densityRequest d n) (densityPrecision n) (densityPrecision_pos n)).block

noncomputable def finalChosenPoint (d : ℕ) (hd : 2 ≤ d) (n : ℕ) : Sphere d :=
  (chooseStrongDensityStep (finalState d hd n)
    (densityRequest d n) (densityPrecision n) (densityPrecision_pos n)).first.x

lemma finalState_succ_src (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (finalState d hd (n+1)).src = (finalState d hd n).src ++ finalBlock d hd n := by
  simp [finalState,finalBlock]
  exact (chooseStrongDensityStep (finalState d hd n)
    (densityRequest d n) (densityPrecision n) (densityPrecision_pos n)).next_src

lemma finalBlock_nonempty (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    finalBlock d hd n ≠ [] :=
  (chooseStrongDensityStep (finalState d hd n)
    (densityRequest d n) (densityPrecision n) (densityPrecision_pos n)).block_nonempty

lemma finalChosenPoint_mem_block (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    finalChosenPoint d hd n ∈ finalBlock d hd n :=
  (chooseStrongDensityStep (finalState d hd n)
    (densityRequest d n) (densityPrecision n) (densityPrecision_pos n)).chosen_mem_block

lemma finalChosenPoint_near (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    distSq (finalChosenPoint d hd n) (densityRequest d n) < densityPrecision n :=
  (chooseStrongDensityStep (finalState d hd n)
    (densityRequest d n) (densityPrecision n) (densityPrecision_pos n)).chosen_near

lemma finalState_growth (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (1:ℝ)/64 < (finalState d hd (n+1)).Bsq - (finalState d hd n).Bsq :=
  (chooseStrongDensityStep (finalState d hd n)
    (densityRequest d n) (densityPrecision n) (densityPrecision_pos n)).B_growth

/-- Quantitative record divergence at the final density phases. -/
theorem finalState_record_lower (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (100:ℝ) + (n:ℝ)/64 ≤ (finalState d hd n).Bsq := by
  induction n with
  | zero => simp [finalState,initialCoreState,CertifiedState.toCore,initialCertifiedState]
  | succ n ih =>
      have hg := finalState_growth d hd n
      have hn : (((n+1:ℕ):ℕ):ℝ) = (n:ℝ)+1 := by norm_num
      rw [hn]
      nlinarith

/-- Strict quantitative growth in the next final phase.  This is the form
used in the final Ulam statement: after the `(n+1)`-st strong phase the
squared inverse record is already strictly larger than `100 + n/64`. -/
theorem finalState_record_strict (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (100:ℝ) + (n:ℝ)/64 < (finalState d hd (n+1)).Bsq := by
  have hlow := finalState_record_lower d hd n
  have hg := finalState_growth d hd n
  nlinarith

/-- Final states have strictly increasing source length. -/
theorem finalState_length_lower (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (anchorSources d (idx0 d (le_trans (by norm_num) hd))).length + n ≤ (finalState d hd n).src.length := by
  induction n with
  | zero => simp [finalState,initialCoreState,CertifiedState.toCore,initialCertifiedState]
  | succ n ih =>
      rw [finalState_succ_src,List.length_append]
      have hb : 1 ≤ (finalBlock d hd n).length := by
        cases hblk : finalBlock d hd n with
        | nil =>
            exact False.elim (finalBlock_nonempty d hd n hblk)
        | cons a l => simp
      omega

lemma finalState_index_bound (d : ℕ) (hd : 2 ≤ d) (m : ℕ) :
    m < (finalState d hd (m+1)).src.length := by
  have h := finalState_length_lower d hd (m+1)
  omega

lemma finalState_extends_succ (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    ListExtends (finalState d hd n).src (finalState d hd (n+1)).src :=
  ⟨finalBlock d hd n, finalState_succ_src d hd n⟩

theorem finalState_extends_of_le (d : ℕ) (hd : 2 ≤ d)
    {m n : ℕ} (hmn : m ≤ n) :
    ListExtends (finalState d hd m).src (finalState d hd n).src := by
  induction n, hmn using Nat.le_induction with
  | base => exact ListExtends.refl _
  | succ n hmn ih => exact ih.trans (finalState_extends_succ d hd n)

lemma getD_finalState_stable (d : ℕ) (hd : 2 ≤ d)
    {m n i : ℕ} (hmn : m ≤ n) (hi : i < (finalState d hd m).src.length) :
    (finalState d hd n).src.getD i (north d) =
      (finalState d hd m).src.getD i (north d) := by
  rcases finalState_extends_of_le d hd hmn with ⟨u,hu⟩
  rw [hu]
  exact List.getD_append _ _ _ _ hi

/-- The actual source sequence for the final theorem. -/
noncomputable def finalSource (d : ℕ) (hd : 2 ≤ d) (m : ℕ) : Sphere d :=
  (finalState d hd (m+1)).src.getD m (north d)

lemma finalSource_eq_state_getD (d : ℕ) (hd : 2 ≤ d)
    (N m : ℕ) (hm : m < (finalState d hd N).src.length) :
    finalSource d hd m = (finalState d hd N).src.getD m (north d) := by
  unfold finalSource
  rcases le_total N (m+1) with hN | hN
  · exact getD_finalState_stable d hd hN hm
  · have hmb : m < (finalState d hd (m+1)).src.length :=
      finalState_index_bound d hd m
    exact (getD_finalState_stable d hd hN hmb).symm

/-- Every finite final state is exactly the corresponding prefix of the direct
limit sequence. -/
def finalPrefix (d : ℕ) (hd : 2 ≤ d) (n : ℕ) : List (Sphere d) :=
  List.ofFn (fun i : Fin n => finalSource d hd i.1)

lemma finalPrefix_length (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (finalPrefix d hd n).length = n := by simp [finalPrefix]

 theorem finalPrefix_at_state (d : ℕ) (hd : 2 ≤ d) (N : ℕ) :
    finalPrefix d hd (finalState d hd N).src.length = (finalState d hd N).src := by
  apply List.ext_getElem
  · simp [finalPrefix]
  · intro i h1 h2
    simp [finalPrefix]
    have hEq := finalSource_eq_state_getD d hd N i h2
    rw [hEq]
    rw [List.getD_eq_getElem _ _ h2]

/-- Image-Nodup implies source-Nodup. -/
lemma source_nodup_of_fold_image_nodup {src : List (Sphere d)}
    (h : (src.map fold).Nodup) : src.Nodup := by
  induction src with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.nodup_cons] at h ⊢
      constructor
      · intro ha
        exact h.1 (List.mem_map.mpr ⟨a,ha,rfl⟩)
      · exact ih h.2

/-- Every point of the final direct-limit source has rational coordinates. -/
theorem finalSource_rational (d : ℕ) (hd : 2 ≤ d) :
    ∀ m : ℕ, RationalPoint (finalSource d hd m) := by
  intro m
  let S := finalState d hd (m+1)
  have hm : m < S.src.length := by
    simpa [S] using finalState_index_bound d hd m
  have heq := finalSource_eq_state_getD d hd (m+1) m hm
  rw [heq, List.getD_eq_getElem _ _ hm]
  exact S.rational _ (by simp)

/-- The final direct-limit source is pairwise distinct. -/
theorem finalSource_pairwise (d : ℕ) (hd : 2 ≤ d) :
    Pairwise (fun m n => finalSource d hd m ≠ finalSource d hd n) := by
  intro m n hmn
  let K := max m n
  let N := K + 1
  have hKN : K < (finalState d hd N).src.length := by
    simpa [N] using finalState_index_bound d hd K
  have hmN : m < (finalState d hd N).src.length :=
    lt_of_le_of_lt (Nat.le_max_left _ _) hKN
  have hnN : n < (finalState d hd N).src.length :=
    lt_of_le_of_lt (Nat.le_max_right _ _) hKN
  have hmEq := finalSource_eq_state_getD d hd N m hmN
  have hnEq := finalSource_eq_state_getD d hd N n hnN
  rw [hmEq,hnEq]
  rw [List.getD_eq_getElem _ _ hmN, List.getD_eq_getElem _ _ hnN]
  have hnodup := source_nodup_of_fold_image_nodup (finalState d hd N).image_nodup
  intro h
  have heq : m = n := (hnodup.getElem_inj_iff).mp h
  exact hmn heq

/-- Every element of a final state occurs in the final direct-limit sequence. -/
theorem mem_finalState_range_finalSource
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ) {x : Sphere d}
    (hx : x ∈ (finalState d hd N).src) :
    ∃ m : ℕ, finalSource d hd m = x := by
  rw [List.mem_iff_get] at hx
  rcases hx with ⟨i,hi⟩
  let m := i.1
  have hm : m < (finalState d hd N).src.length := i.2
  refine ⟨m,?_⟩
  rw [finalSource_eq_state_getD d hd N m hm]
  rw [List.getD_eq_get _ _ i]
  exact hi

lemma finalChosenPoint_in_range (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    ∃ m : ℕ, finalSource d hd m = finalChosenPoint d hd n := by
  have hx : finalChosenPoint d hd n ∈ (finalState d hd (n+1)).src := by
    rw [finalState_succ_src]
    exact List.mem_append_right _ (finalChosenPoint_mem_block d hd n)
  exact mem_finalState_range_finalSource d hd (n+1) hx

/-- Density of the final source. -/
theorem finalSource_chordDense (d : ℕ) (hd : 2 ≤ d) :
    ChordDense (finalSource d hd) := by
  intro y ε hε
  obtain ⟨k,hky⟩ := denseRequest_chord_approx d y (show 0 < ε/4 by positivity)
  obtain ⟨j,hj⟩ := exists_nat_gt (4/ε : ℝ)
  let n := Nat.pair k j
  have hunpair : Nat.unpair n = (k,j) := by simp [n]
  have hprec : densityPrecision n < ε/4 := by
    unfold densityPrecision
    rw [hunpair]
    dsimp
    have hj0 : (4/ε:ℝ) < (j:ℝ) := hj
    have hjr : (4/ε:ℝ) < ((j+1:ℕ):ℝ) := by
      norm_num
      linarith
    have hpos : 0 < ((j+1:ℕ):ℝ) := by positivity
    rw [div_lt_iff₀ hpos]
    have hm := mul_lt_mul_of_pos_left hjr hε
    field_simp at hm ⊢
    nlinarith
  have hreq : densityRequest d n = TopologicalSpace.denseSeq (Sphere d) k := by
    simp [densityRequest,hunpair]
  have hnear := finalChosenPoint_near d hd n
  rw [hreq] at hnear
  obtain ⟨m,hm⟩ := finalChosenPoint_in_range d hd n
  refine ⟨m,?_⟩
  rw [hm]
  have htri := distSq_triangle_two (finalChosenPoint d hd n)
    (TopologicalSpace.denseSeq (Sphere d) k) y
  nlinarith


/-- Exact greedy and Lipschitz data at every cofinal final phase. -/
theorem finalState_greedy (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    GreedyBuiltFrom (anchorSources d (idx0 d (le_trans (by norm_num) hd)))
      (finalPrefix d hd (finalState d hd n).src.length) := by
  rw [finalPrefix_at_state]
  exact (finalState d hd n).built

theorem finalState_forward_one (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    forwardLipSq (foldGraph
      (finalPrefix d hd (finalState d hd n).src.length)) = 1 := by
  rw [finalPrefix_at_state]
  exact forwardLipSq_foldGraph_eq_one _ (idx0 d (le_trans (by norm_num) hd))
    ((finalState d hd n).pos_mem (idx0 d (le_trans (by norm_num) hd)))
    ((finalState d hd n).neg_mem (idx0 d (le_trans (by norm_num) hd)))

theorem finalState_inverse_exact (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    inverseLipSq (foldGraph
      (finalPrefix d hd (finalState d hd n).src.length)) =
      (finalState d hd n).Bsq := by
  rw [finalPrefix_at_state]
  exact (finalState d hd n).inverse_exact

/-- Quantitative inverse divergence along a cofinal subsequence of finite
prefixes. -/
theorem finalSource_inverse_diverges (d : ℕ) (hd : 2 ≤ d) :
    ∀ k : ℕ, ∃ N : ℕ,
      (100:ℝ) + (k:ℝ)/64 <
        inverseLipSq (foldGraph (finalPrefix d hd N)) := by
  intro k
  let N := (finalState d hd (k+1)).src.length
  refine ⟨N,?_⟩
  rw [show finalPrefix d hd N = (finalState d hd (k+1)).src by
    simpa [N] using finalPrefix_at_state d hd (k+1)]
  rw [(finalState d hd (k+1)).inverse_exact]
  exact finalState_record_strict d hd k

/-- The phase lengths are cofinal, so the greedy certificates cover arbitrarily
long prefixes of the final sequence. -/
theorem finalStageLengths_unbounded (d : ℕ) (hd : 2 ≤ d) :
    ∀ m : ℕ, ∃ n : ℕ, m ≤ (finalState d hd n).src.length := by
  intro m
  refine ⟨m,?_⟩
  have h := finalState_length_lower d hd m
  omega

/-- Every source index lies inside a finite prefix whose *entire* extension
from the anchor block is certified by `GreedyBuiltFrom`.  Since the latter is
inductive by single-point `UniqueGreedyStep`s, this is the direct formal
coverage statement that every point of the infinite source occurs in a
uniquely-greedy certified construction. -/
theorem finalSource_every_index_certified (d : ℕ) (hd : 2 ≤ d) :
    ∀ m : ℕ, ∃ n : ℕ,
      m < (finalState d hd n).src.length ∧
      GreedyBuiltFrom
        (anchorSources d (idx0 d (le_trans (by norm_num) hd)))
        (finalPrefix d hd (finalState d hd n).src.length) := by
  intro m
  refine ⟨m+1, ?_, finalState_greedy d hd (m+1)⟩
  have h := finalState_length_lower d hd (m+1)
  omega

/-- Final packaged counterexample statement.  `cofinal_greedy` says that
arbitrarily long prefixes are certified by the inductive `GreedyBuiltFrom`
relation; since each such proof records every intervening unique greedy step,
this is the direct-limit formulation of an infinite greedy construction. -/
structure UlamCounterexample (d : ℕ) (hd : 2 ≤ d) where
  source : ℕ → Sphere d
  source_rational : ∀ n, RationalPoint (source n)
  pairwise : Pairwise (fun m n => source m ≠ source n)
  dense : ChordDense source
  stageLength : ℕ → ℕ
  stage_unbounded : ∀ m, ∃ n, m ≤ stageLength n
  cofinal_greedy : ∀ n,
    GreedyBuiltFrom
      (anchorSources d (idx0 d (le_trans (by norm_num) hd)))
      (List.ofFn fun i : Fin (stageLength n) => source i.1)
  every_index_certified : ∀ m, ∃ n,
    m < stageLength n ∧
    GreedyBuiltFrom
      (anchorSources d (idx0 d (le_trans (by norm_num) hd)))
      (List.ofFn fun i : Fin (stageLength n) => source i.1)
  forward_one : ∀ n,
    forwardLipSq (foldGraph
      (List.ofFn fun i : Fin (stageLength n) => source i.1)) = 1
  inverse_growth : ∀ k : ℕ, ∃ n : ℕ,
    (100:ℝ) + (k:ℝ)/64 <
      inverseLipSq (foldGraph
        (List.ofFn fun i : Fin (stageLength n) => source i.1))

/-- Ulam 165 on every sphere dimension `d ≥ 2`: a pairwise distinct dense
rational infinite source sequence admits a unique greedy fold construction with forward
Lipschitz constant one while inverse Lipschitz constants diverge. -/
noncomputable def ulam165_counterexample (d : ℕ) (hd : 2 ≤ d) :
    UlamCounterexample d hd := by
  refine {
    source := finalSource d hd
    source_rational := finalSource_rational d hd
    pairwise := finalSource_pairwise d hd
    dense := finalSource_chordDense d hd
    stageLength := fun n => (finalState d hd n).src.length
    stage_unbounded := finalStageLengths_unbounded d hd
    cofinal_greedy := ?_
    every_index_certified := ?_
    forward_one := ?_
    inverse_growth := ?_
  }
  · intro n
    simpa [finalPrefix] using finalState_greedy d hd n
  · intro m
    rcases finalSource_every_index_certified d hd m with ⟨n,hm,hg⟩
    refine ⟨n,hm,?_⟩
    simpa [finalPrefix] using hg
  · intro n
    simpa [finalPrefix] using finalState_forward_one d hd n
  · intro k
    refine ⟨k+1,?_⟩
    simpa [finalPrefix] using
      (show (100:ℝ)+(k:ℝ)/64 <
        inverseLipSq (foldGraph
          (finalPrefix d hd (finalState d hd (k+1)).src.length)) by
        rw [finalState_inverse_exact]
        exact finalState_record_strict d hd k)

theorem exists_ulam165_counterexample (d : ℕ) (hd : 2 ≤ d) :
    Nonempty (UlamCounterexample d hd) :=
  ⟨ulam165_counterexample d hd⟩

#print axioms exists_ulam165_counterexample

end Ulam165
