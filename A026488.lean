import Mathlib.Tactic

/-! Kimberling's OEIS A026488. Internal indices start at zero. -/
namespace Kimberling488

/-- At the index under consideration, substitute the trial value `x`. -/
def trial (a : ℕ → ℕ) (n x i : ℕ) : ℕ := if i < n then a i else x

/-- Natural-number equality uses `u*v = x+w` to represent integer subtraction. -/
def Admissible (a : ℕ → ℕ) (n x : ℕ) : Prop := ∀ i j k : ℕ,
  i ≤ j → j ≤ k → k ≤ n → trial a n x i * trial a n x j ≠ x + trial a n x k

/-- `a 0` is OEIS term 1. Each later term is the least eligible trial. -/
def Greedy (a : ℕ → ℕ) : Prop := a 0 = 1 ∧ ∀ n : ℕ,
  IsLeast {x : ℕ | a n < x ∧ Admissible a (n+1) x} (a (n+1))

def formula : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | n+2 => 3*n+4

private abbrev Good (v : ℕ) := v = 3 ∨ v % 3 = 1

private theorem inc : StrictMono formula := by
  apply strictMono_nat_of_lt_succ
  intro n
  match n with
  | 0 | 1 => decide
  | n+2 => simp [formula]

private theorem good_term (n : ℕ) : Good (formula n) := by
  match n with
  | 0 | 1 => simp [Good, formula]
  | n+2 => unfold Good; right; simp [formula, Nat.add_mod]

private theorem good_range {v : ℕ} (h : Good v) : ∃ k, formula k = v := by
  rcases h with h|h
  · exact ⟨1,h.symm⟩
  · by_cases hv : v = 1
    · exact ⟨0,hv.symm⟩
    · exact ⟨(v-4)/3+2, by simp [formula]; omega⟩

/-- Every ordered triple of sequence values avoids a positive allowed output ≥ its last input. -/
private theorem good_avoids {a b c x : ℕ} (ha : Good a) (hb : Good b) (hc : Good c)
    (hx : Good x) (hab : a ≤ b) (hbc : b ≤ c) (hcx : c ≤ x) : a*b ≠ x+c := by
  intro e
  by_cases small : x ≤ 6
  · interval_cases x <;> interval_cases c <;> interval_cases b <;> interval_cases a <;> norm_num [Good] at *
  · have big : 6 < x := by omega
    have xm : x%3=1 := by rcases hx with h|h <;> omega
    by_cases cc : c = 3
    · subst c; interval_cases b <;> interval_cases a <;> simp_all [Good]
    · have cm : c%3=1 := by rcases hc with h|h <;> omega
      have m := congrArg (fun t : ℕ => t%3) e
      simp only [Nat.mul_mod a b 3, Nat.add_mod x c 3, xm, cm] at m
      rcases ha with h|h <;> rcases hb with hh|hh <;> simp_all

/-- Prefix available to a trial includes the trial itself. -/
private abbrev Available (x v : ℕ) := (Good v ∧ v < x) ∨ v = x

private theorem skipped {x : ℕ} (hx : 1 < x) (h : ¬ Good x) :
    ∃ a b c : ℕ, Available x a ∧ Available x b ∧ Available x c ∧
      a ≤ b ∧ b ≤ c ∧ a*b=x+c := by
  by_cases hs : x < 18
  · interval_cases x <;> first
    | exact False.elim (h (by decide))
    | (refine ⟨2,2,2,?_⟩; decide)
    | (refine ⟨3,3,4,?_⟩; decide)
    | (refine ⟨3,3,3,?_⟩; decide)
    | (refine ⟨3,4,4,?_⟩; decide)
    | (refine ⟨4,4,7,?_⟩; decide)
    | (refine ⟨3,7,10,?_⟩; decide)
    | (refine ⟨4,4,4,?_⟩; decide)
    | (refine ⟨3,7,7,?_⟩; decide)
    | (refine ⟨4,7,13,?_⟩; decide)
    | (refine ⟨3,10,13,?_⟩; decide)
  · unfold Good at h
    by_cases h0 : x%3=0
    · let q := 3*((x+5)/9)+1
      let r := 4*q-x
      refine ⟨4,q,r,Or.inl ⟨Or.inr rfl,by omega⟩,Or.inl ⟨Or.inr ?_,?_⟩,Or.inl ⟨Or.inr ?_,?_⟩,?_,?_,?_⟩ <;> dsimp [q,r] <;> omega
    · let q := 3*((x+5)/6)+1
      let r := 3*q-x
      refine ⟨3,q,r,Or.inl ⟨Or.inl rfl,by omega⟩,Or.inl ⟨Or.inr ?_,?_⟩,Or.inl ⟨Or.inr ?_,?_⟩,?_,?_,?_⟩ <;> dsimp [q,r] <;> omega

private theorem trial_strict {n x i j : ℕ} (hx : formula n < x)
    (hij : i < j) (hj : j ≤ n+1) :
    trial formula (n+1) x i < trial formula (n+1) x j := by
  have hi : i < n+1 := by omega
  simp only [trial, ite_eq_left hi]
  split_ifs with h
  · exact inc hij
  · exact lt_of_le_of_lt (inc.monotone (by omega)) hx

private theorem trial_has {n x v : ℕ} (hx : x ≤ formula (n+1)) (hv : Available x v) :
    ∃ i, i ≤ n+1 ∧ trial formula (n+1) x i = v := by
  rcases hv with ⟨hg,hlt⟩|rfl
  · obtain ⟨i,hi⟩ := good_range hg
    have : i < n+1 := inc.lt_iff_lt.mp (by omega)
    exact ⟨i,by omega,by simp [trial,this,hi]⟩
  · exact ⟨n+1,le_rfl,by simp [trial]⟩

/-- The proposed formula satisfies the least-choice recurrence. -/
theorem formula_is_greedy : Greedy formula := by
  refine ⟨rfl,?_⟩
  intro n
  constructor
  · refine ⟨inc (by omega),?_⟩
    intro i j k hij hjk hkn
    have he (l : ℕ) (hl : l ≤ n+1) :
        trial formula (n+1) (formula (n+1)) l = formula l := by
      rcases lt_or_eq_of_le hl with ht|rfl <;> simp_all [trial]
    rw [he i (by omega),he j (by omega),he k hkn]
    exact good_avoids (good_term _) (good_term _) (good_term _) (good_term _)
      (inc.monotone hij) (inc.monotone hjk) (inc.monotone hkn)
  · intro x ⟨hx,had⟩
    by_contra! bad
    have hx1 : 1 < x := lt_of_le_of_lt (inc.monotone (Nat.zero_le n) : formula 0 ≤ _) hx
    have noGood : ¬ Good x := by
      intro hg
      obtain ⟨m,rfl⟩ := good_range hg
      have h1 := inc.lt_iff_lt.mp hx
      have h2 := inc.lt_iff_lt.mp bad
      omega
    obtain ⟨a,b,c,ha,hb,hc,hab,hbc,e⟩ := skipped hx1 noGood
    obtain ⟨i,hi,ei⟩ := trial_has bad.le ha
    obtain ⟨j,hj,ej⟩ := trial_has bad.le hb
    obtain ⟨k,hk,ek⟩ := trial_has bad.le hc
    have hij : i ≤ j := by
      by_contra! h
      have := trial_strict hx h hi
      omega
    have hjk : j ≤ k := by
      by_contra! h
      have := trial_strict hx h hj
      omega
    exact had i j k hij hjk hk (by simpa [ei,ej,ek] using e)

private theorem greedy_unique {s t : ℕ → ℕ} (hs : Greedy s) (ht : Greedy t) : s=t := by
  funext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => exact hs.1.trans ht.1.symm
    | succ n =>
      have prev := ih n (by omega)
      have same (x i : ℕ) : trial s (n+1) x i = trial t (n+1) x i := by
        unfold trial; split_ifs with h
        · exact ih _ h
        · rfl
      have adm (x : ℕ) : Admissible s (n+1) x ↔ Admissible t (n+1) x := by
        unfold Admissible
        simp only [same]
      have set_eq : {x : ℕ | s n < x ∧ Admissible s (n+1) x}
            = {x : ℕ | t n < x ∧ Admissible t (n+1) x} := by
        ext x; simp only [Set.mem_ofPred_eq,prev,adm]
      exact ((set_eq ▸ hs.2 n) : IsLeast {x : ℕ | t n < x ∧ Admissible t (n+1) x} _).unique (ht.2 n)

/-- Existence and uniqueness for the source recurrence, with the conjectured formula. -/
theorem A026488 : Greedy formula ∧ ∀ s : ℕ → ℕ, Greedy s → s = formula :=
  ⟨formula_is_greedy,fun _ h => greedy_unique h formula_is_greedy⟩

/-- Exact range of the source sequence. -/
theorem range_A026488 {s : ℕ → ℕ} (hs : Greedy s) (x : ℕ) :
    (∃ i, s i = x) ↔ x=3 ∨ x%3=1 := by
  rw [A026488.2 s hs]
  exact ⟨fun ⟨i,hi⟩ => hi ▸ good_term i, good_range⟩

#print axioms A026488
#print axioms range_A026488
end Kimberling488
