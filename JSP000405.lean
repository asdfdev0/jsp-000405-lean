import Mathlib

namespace JSP000405

abbrev Point := ℝ × ℝ

structure Circle where
  u : ℝ
  v : ℝ
  w : ℝ

/-- Monic affine equation for a proper Euclidean circle:
`x^2 + y^2 + u*x + v*y + w = 0`. -/
def OnCircle (C : Circle) (p : Point) : Prop :=
  p.1 ^ 2 + p.2 ^ 2 + C.u * p.1 + C.v * p.2 + C.w = 0

/-- The explicit `n`-point configuration on the x-axis. -/
def axisConfig (n : ℕ) : Fin n → Point :=
  fun i => ((i.1 : ℝ), 0)

/-- An indexed configuration is all concyclic if one circle contains every point. -/
def AllConcyclic {n : ℕ} (P : Fin n → Point) : Prop :=
  ∃ C : Circle, ∀ i : Fin n, OnCircle C (P i)

/-- A circle is determined by a configuration if it contains three distinct indexed points. -/
def DeterminedCircle {n : ℕ} (P : Fin n → Point) (C : Circle) : Prop :=
  ∃ i j k : Fin n,
    i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    OnCircle C (P i) ∧ OnCircle C (P j) ∧ OnCircle C (P k)

/-- Number of distinct circles determined by a configuration. -/
noncomputable def circleCount {n : ℕ} (P : Fin n → Point) : ℕ :=
  Set.ncard {C : Circle | DeterminedCircle P C}

lemma axisConfig_injective (n : ℕ) : Function.Injective (axisConfig n) := by
  intro i j hij
  apply Fin.ext
  have hfirst : (i.1 : ℝ) = (j.1 : ℝ) := by
    simpa [axisConfig] using congrArg Prod.fst hij
  exact_mod_cast hfirst

lemma three_axis_points_not_concyclic
    {n : ℕ} (C : Circle) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : OnCircle C (axisConfig n i))
    (hj : OnCircle C (axisConfig n j))
    (hk : OnCircle C (axisConfig n k)) : False := by
  have hijNat : i.1 ≠ j.1 := by
    intro h
    exact hij (Fin.ext h)
  have hikNat : i.1 ≠ k.1 := by
    intro h
    exact hik (Fin.ext h)
  have hjkNat : j.1 ≠ k.1 := by
    intro h
    exact hjk (Fin.ext h)
  have hijv : (i.1 : ℝ) ≠ (j.1 : ℝ) := by exact_mod_cast hijNat
  have hikv : (i.1 : ℝ) ≠ (k.1 : ℝ) := by exact_mod_cast hikNat
  have hjkv : (j.1 : ℝ) ≠ (k.1 : ℝ) := by exact_mod_cast hjkNat
  have hi' : (i.1 : ℝ) ^ 2 + C.u * (i.1 : ℝ) + C.w = 0 := by
    simpa [OnCircle, axisConfig] using hi
  have hj' : (j.1 : ℝ) ^ 2 + C.u * (j.1 : ℝ) + C.w = 0 := by
    simpa [OnCircle, axisConfig] using hj
  have hk' : (k.1 : ℝ) ^ 2 + C.u * (k.1 : ℝ) + C.w = 0 := by
    simpa [OnCircle, axisConfig] using hk
  have hab : ((i.1 : ℝ) - (j.1 : ℝ)) * ((i.1 : ℝ) + (j.1 : ℝ) + C.u) = 0 := by
    nlinarith
  have hac : ((i.1 : ℝ) - (k.1 : ℝ)) * ((i.1 : ℝ) + (k.1 : ℝ) + C.u) = 0 := by
    nlinarith
  have hs1 : (i.1 : ℝ) + (j.1 : ℝ) + C.u = 0 :=
    (mul_eq_zero.mp hab).resolve_left (sub_ne_zero.mpr hijv)
  have hs2 : (i.1 : ℝ) + (k.1 : ℝ) + C.u = 0 :=
    (mul_eq_zero.mp hac).resolve_left (sub_ne_zero.mpr hikv)
  have : (j.1 : ℝ) = (k.1 : ℝ) := by linarith
  exact hjkv this

lemma axisConfig_no_determined_circle (n : ℕ) (C : Circle) :
    ¬ DeterminedCircle (axisConfig n) C := by
  rintro ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩
  exact three_axis_points_not_concyclic C i j k hij hik hjk hi hj hk

lemma axisConfig_circleCount_zero (n : ℕ) : circleCount (axisConfig n) = 0 := by
  have hset : {C : Circle | DeterminedCircle (axisConfig n) C} = ∅ := by
    ext C
    simp [axisConfig_no_determined_circle n C]
  simp [circleCount, hset]

lemma axisConfig_not_all_concyclic {n : ℕ} (hn : 3 ≤ n) :
    ¬ AllConcyclic (axisConfig n) := by
  rintro ⟨C, hC⟩
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let k : Fin n := ⟨2, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    norm_num [i, j] at this
  have hik : i ≠ k := by
    intro h
    have := congrArg Fin.val h
    norm_num [i, k] at this
  have hjk : j ≠ k := by
    intro h
    have := congrArg Fin.val h
    norm_num [j, k] at this
  exact three_axis_points_not_concyclic C i j k hij hik hjk (hC i) (hC j) (hC k)

/-- Literal solution of the published JSP-000405 wording.

For every `n ≥ 3`, there is an injectively indexed planar `n`-point set which is
not all concyclic and determines zero circles: take `n` distinct points on a line.
Thus the literal minimum number of determined circles is `0`.
-/
theorem jsp_000405_literal (n : ℕ) (hn : 3 ≤ n) :
    ∃ P : Fin n → Point,
      Function.Injective P ∧
      ¬ AllConcyclic P ∧
      circleCount P = 0 := by
  refine ⟨axisConfig n, axisConfig_injective n, axisConfig_not_all_concyclic hn, ?_⟩
  exact axisConfig_circleCount_zero n

#print axioms jsp_000405_literal

end JSP000405
