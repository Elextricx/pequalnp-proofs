import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3059

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

-- Evaluation of wire i in a circuit on n inputs.
def wv {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem wv_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    wv C x i.val = x i := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix C.gates (List.ofFn x)
  rw [wv, ht, List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem wv_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ)
    (hi : n + C.gates.length ≤ i) : wv C x i = false := by
  rw [wv, List.getD_eq_default _ _ (by rw [length_wiresFrom, List.length_ofFn]; omega)]

theorem wv_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    wv C x (n + j) = g.op.eval (g.inputs.map fun a => if a < n + j then wv C x a else false) := by
  obtain ⟨hjl, heq⟩ := List.getElem?_eq_some_iff.1 hj
  have hsp : C.gates = C.gates.take j ++ g :: C.gates.drop (j + 1) := by
    rw [← heq, ← List.drop_eq_getElem_cons hjl, List.take_append_drop]
  let pre := C.gates.take j
  let post := C.gates.drop (j + 1)
  have hplen : pre.length = j := by simp [pre, hjl.le]
  let w0 := wiresFrom pre (List.ofFn x)
  have hw0len : w0.length = n + j := by
    simp [w0, length_wiresFrom, List.length_ofFn, hplen]
  have hw : wiresFrom C.gates (List.ofFn x) =
      wiresFrom post (w0 ++ [g.op.eval (g.inputs.map fun a => w0.getD a false)]) := by
    conv_lhs => rw [hsp]
    rw [wiresFrom_append]
    rfl
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix post (w0 ++ [g.op.eval (g.inputs.map fun a => w0.getD a false)])
  have hval : wv C x (n + j) = g.op.eval (g.inputs.map fun a => w0.getD a false) := by
    rw [wv, hw, ht, List.getD_append _ _ _ _ (by rw [List.length_append, hw0len]; simp)]
    rw [← hw0len, getD_snoc_eq]
  rw [hval]
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases ha : a < n + j
  · simp only [ha, ite_true]
    rw [wv, hw, ht, List.getD_append _ _ _ _ (by rw [List.length_append, hw0len]; omega)]
    rw [List.getD_append _ _ _ _ (by rw [hw0len]; omega)]
  · simp only [ha, ite_false]
    rw [List.getD_eq_default _ _ (by rw [hw0len]; omega)]

-- Deleting a dead gate preserves evaluation and decreases size by 1.
def shiftIdx (k w : ℕ) : ℕ := if w < k then w else w - 1

def shiftGate (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftIdx k)⟩

theorem shiftGate_ok (k : ℕ) (g : Gate) (h : Ok g) : Ok (shiftGate k g) := by
  exact ⟨h.1, by simpa [shiftGate] using h.2⟩

theorem wiresFrom_delete_dead {n : ℕ} (pre post : List Gate) (g : Gate) (x : List Bool)
    (hx : x.length = n) (hdead : ∀ g' ∈ post, n + pre.length ∉ g'.inputs) :
    let wFull := wiresFrom (pre ++ g :: post) x
    let wDel := wiresFrom (pre ++ post.map (shiftGate (n + pre.length))) x
    ∀ i : ℕ, i ≠ n + pre.length →
      wDel.getD (shiftIdx (n + pre.length) i) false = wFull.getD i false := by
  induction post using List.reverseRecOn with
  | nil =>
    intro wFull wDel i hi
    have hpre : (wiresFrom pre x).length = n + pre.length := by rw [length_wiresFrom, hx]
    have hf : wFull = wiresFrom pre x ++ [g.op.eval (g.inputs.map fun a => (wiresFrom pre x).getD a false)] := by
      simp [wFull, wiresFrom_append, wiresFrom]
    have hd : wDel = wiresFrom pre x := by simp [wDel]
    rw [hf, hd]
    by_cases hlt : i < n + pre.length
    · simp only [shiftIdx, hlt, ite_true]
      rw [List.getD_append _ _ _ _ (by rw [hpre]; omega)]
    · have hgt : n + pre.length < i := by omega
      simp only [shiftIdx, hlt, ite_false]
      rw [List.getD_eq_default _ _ (by rw [hpre]; omega)]
      rw [List.getD_eq_default _ _ (by rw [List.length_append, hpre]; simp; omega)]
  | append_singleton post h ih =>
    have hdead' : ∀ g' ∈ post, n + pre.length ∉ g'.inputs :=
      fun g' hg' => hdead g' (List.mem_append_left _ hg')
    have hhdead : n + pre.length ∉ h.inputs := hdead h (by simp)
    have ih' := ih hdead'
    intro wFull wDel i hi
    have hlenF : (wiresFrom (pre ++ g :: post) x).length = n + pre.length + 1 + post.length := by
      rw [length_wiresFrom, hx, List.length_append, List.length_cons]; omega
    have hlenD : (wiresFrom (pre ++ post.map (shiftGate (n + pre.length))) x).length =
        n + pre.length + post.length := by
      rw [length_wiresFrom, hx, List.length_append, List.length_map]; omega
    have hf : wFull = wiresFrom (pre ++ g :: post) x ++
        [h.op.eval (h.inputs.map fun a => (wiresFrom (pre ++ g :: post) x).getD a false)] := by
      simp [wFull, List.append_assoc, wiresFrom_append, wiresFrom]
    have hd : wDel = wiresFrom (pre ++ post.map (shiftGate (n + pre.length))) x ++
        [(shiftGate (n + pre.length) h).op.eval
          ((shiftGate (n + pre.length) h).inputs.map fun a =>
            (wiresFrom (pre ++ post.map (shiftGate (n + pre.length))) x).getD a false)] := by
      simp [wDel, List.append_assoc, wiresFrom_append, wiresFrom]
    have hstep : (shiftGate (n + pre.length) h).op.eval
        ((shiftGate (n + pre.length) h).inputs.map fun a =>
          (wiresFrom (pre ++ post.map (shiftGate (n + pre.length))) x).getD a false) =
        h.op.eval (h.inputs.map fun a => (wiresFrom (pre ++ g :: post) x).getD a false) := by
      simp only [shiftGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih' a (fun heq => hhdead (heq ▸ ha))
    rw [hf, hd, hstep]
    by_cases hlast : i = n + pre.length + 1 + post.length
    · subst hlast
      have hnotlt : ¬ (n + pre.length + 1 + post.length < n + pre.length) := by omega
      have hshift : shiftIdx (n + pre.length) (n + pre.length + 1 + post.length) =
          n + pre.length + post.length := by simp [shiftIdx, hnotlt]
      rw [hshift, ← hlenD, getD_snoc_eq, ← hlenF, getD_snoc_eq]
    · have hneD : shiftIdx (n + pre.length) i ≠ n + pre.length + post.length := by
        unfold shiftIdx; split_ifs <;> omega
      rw [getD_snoc_ne _ _ _ _ (by rw [hlenD]; exact hneD)]
      rw [getD_snoc_ne _ _ _ _ (by rw [hlenF]; exact hlast)]
      exact ih' i hi

-- Replacing gate j by an equivalent Stat s (valid at n+j) decreases size by 1.
theorem replace_gate_elim {n : ℕ} (C : Circuit) (hfan : FanInTwo C) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) (s : Stat) (hsv : s.Valid (n + j))
    (hsval : ∀ x : Fin n → Bool,
      s.val (wiresFrom (C.gates.take j) (List.ofFn x)) = wv C x (n + j))
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨hjl, heq⟩ := List.getElem?_eq_some_iff.1 hj
  let pre := C.gates.take j
  let post := C.gates.drop (j + 1)
  have hsp : C.gates = pre ++ g :: post := by
    rw [← heq, ← List.drop_eq_getElem_cons hjl, List.take_append_drop]
  have hplen : pre.length = j := by simp [pre, hjl.le]
  let acc0 : List Stat × List Gate := ((List.range (n + j)).map Sum.inr ++ [s], pre)
  let acc := elim n post acc0
  have hok_pre : ∀ g' ∈ pre, Ok g' := fun g' hg' => hfan g' (List.mem_of_mem_take hg')
  have hok_post : ∀ g' ∈ post, Ok g' := fun g' hg' => hfan g' (List.mem_of_mem_drop hg')
  have hinv : ∀ x : Fin n → Bool, Inv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := by
    intro x
    have hsp' : wiresFrom C.gates (List.ofFn x) = wiresFrom post (wiresFrom (pre ++ [g]) (List.ofFn x)) := by
      conv_lhs => rw [hsp]
      rw [show pre ++ g :: post = (pre ++ [g]) ++ post by simp, wiresFrom_append]
    rw [hsp']
    apply inv_elim n (List.ofFn x) List.length_ofFn post _ acc0 hok_post
    have hwlen : (wiresFrom (pre ++ [g]) (List.ofFn x)).length = n + j + 1 := by
      rw [length_wiresFrom, List.length_ofFn, List.length_append, hplen]; simp; omega
    refine ⟨by simp [acc0, hwlen], ?_⟩
    intro i
    have hpre_len : (wiresFrom pre (List.ofFn x)).length = n + j := by
      rw [length_wiresFrom, List.length_ofFn, hplen]
    by_cases hi : i < n + j
    · have hget : acc0.1.getD i (Sum.inl false) = Sum.inr i := by
        show ((List.range (n + j)).map Sum.inr ++ [s]).getD i (Sum.inl false) = Sum.inr i
        rw [List.getD_append _ _ _ _ (by simp; omega)]
        rw [List.getD_eq_getElem _ _ (by simp; omega)]
        simp [hi]
      rw [hget]
      refine ⟨by simpa [acc0, Stat.Valid, hplen] using hi, ?_⟩
      simp only [acc0, Stat.val]
      rw [wiresFrom_append]
      obtain ⟨t, ht, _⟩ := wiresFrom_prefix [g] (wiresFrom pre (List.ofFn x))
      rw [ht, List.getD_append _ _ _ _ (by rw [hpre_len]; omega)]
    · by_cases hi2 : i = n + j
      · subst hi2
        have hget : acc0.1.getD (n + j) (Sum.inl false) = s := by
          show ((List.range (n + j)).map (Sum.inr : ℕ → Stat) ++ [s]).getD (n + j) (Sum.inl false) = s
          have hrl : ((List.range (n + j)).map (Sum.inr : ℕ → Stat)).length = n + j := by simp
          have hsn := getD_snoc_eq ((List.range (n + j)).map (Sum.inr : ℕ → Stat)) s (Sum.inl false)
          rwa [hrl] at hsn
        rw [hget]
        refine ⟨by simpa [acc0, hplen] using hsv, ?_⟩
        have hEqW : (wiresFrom (pre ++ [g]) (List.ofFn x)).getD (n + j) false = wv C x (n + j) := by
          rw [wv, show wiresFrom C.gates (List.ofFn x) =
              wiresFrom post (wiresFrom (pre ++ [g]) (List.ofFn x)) by
                conv_lhs => rw [hsp]; rw [show pre ++ g :: post = (pre ++ [g]) ++ post by simp, wiresFrom_append]]
          obtain ⟨t, ht, _⟩ := wiresFrom_prefix post (wiresFrom (pre ++ [g]) (List.ofFn x))
          rw [ht, List.getD_append _ _ _ _ (by rw [hwlen]; omega)]
        rw [hEqW]
        exact hsval x
      · have hget : acc0.1.getD i (Sum.inl false) = Sum.inl false := by
          rw [List.getD_eq_default _ _ (by simp [acc0]; omega)]
        rw [hget]
        refine ⟨trivial, ?_⟩
        rw [List.getD_eq_default _ _ (by rw [hwlen]; omega)]
        rfl
  have hlen_acc : acc.2.length ≤ pre.length + post.length := by
    have hpost_nok : ∀ g' ∈ post.map normGate, NOk g' := by
      intro g' hg'
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg'
      exact normGate_nok g0 (hok_post g0 hg0)
    have hstep_le : ∀ (gs : List Gate) (a : List Stat × List Gate),
        (elim n gs a).2.length ≤ a.2.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro a; simp [elim]
      | cons g' gs' ih =>
        intro a
        rw [elim_cons]
        have h1 := ih (elimStep n a g')
        have h2 : (elimStep n a g').2.length ≤ a.2.length + 1 := by
          simp only [elimStep, List.length_append]
          have := toList_length_le (simplify g'.op (n + a.2.length)
            (g'.inputs.map fun i => a.1.getD i (Sum.inl false))).1
          omega
        simp only [List.length_cons]
        omega
    exact hstep_le post acc0
  have hsz : acc.2.length + 1 ≤ C.size := by
    have hcl : C.gates.length = pre.length + 1 + post.length := by
      conv_lhs => rw [hsp]
      simp; omega
    change acc.2.length + 1 ≤ C.gates.length
    omega
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inr k =>
    refine ⟨⟨acc.2, k⟩, elim_ok n post acc0 hok_pre, hsz, ?_⟩
    intro x
    have hval := ((hinv x).2 C.output).2
    rw [ho] at hval
    exact hval
  | inl b =>
    obtain ⟨x, y, hxy⟩ := hnc
    have hx := ((hinv x).2 C.output).2
    have hy := ((hinv y).2 C.output).2
    rw [ho] at hx hy
    exact absurd (hx.symm.trans hy) hxy

-- Fixing input p to b using elim.
def initFix (n : ℕ) (p : Fin n) (b : Bool) : List Stat :=
  (List.range n).map fun i => if i = p.val then Sum.inl b else Sum.inr i

theorem inv_initFix {n : ℕ} (p : Fin n) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Function.update y p b)) (initFix n p b, []) := by
  refine ⟨by simp [initFix], ?_⟩
  intro i
  by_cases hi : i < n
  · have hget : (initFix n p b).getD i (Sum.inl false) =
        if i = p.val then Sum.inl b else Sum.inr i := by
      rw [List.getD_eq_getElem _ _ (by simp [initFix, hi])]
      simp [initFix, hi]
    rw [hget]
    by_cases hp : i = p.val
    · subst hp
      simp only [ite_true, Stat.Valid, Stat.val, true_and]
      rw [List.getD_eq_getElem _ _ (by simp [hi])]
      simp [Fin.eta]
    · simp only [hp, ite_false, Stat.Valid, Stat.val, wiresFrom, List.foldl_nil]
      refine ⟨by omega, ?_⟩
      rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getD_eq_getElem _ _ (by simp [hi])]
      simp [Function.update_of_ne (show (⟨i, hi⟩ : Fin n) ≠ p from fun h => hp (congrArg Fin.val h))]
  · rw [List.getD_eq_default _ _ (by simp [initFix]; omega)]
    rw [List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

-- Definitions on functions for gate elimination.
def Dep {n : ℕ} (f : (Fin n → Bool) → Bool) (p : Fin n) : Prop :=
  ∃ x : Fin n → Bool, f (Function.update x p (!x p)) ≠ f x

def RestrNC {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ p : Fin n, Dep f p → ∀ b : Bool, ∃ x y : Fin n → Bool,
    f (Function.update x p b) ≠ f (Function.update y p b)

def NoFunnel {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ p q : Fin n, p ≠ q → Dep f p → Dep f q →
    ¬ ∃ a b : Bool, ∀ x : Fin n → Bool,
      f (Function.update (Function.update x p (!a)) q b) =
        f (Function.update (Function.update x p a) q (!b)) ∧
      f (Function.update (Function.update x p a) q (!b)) =
        f (Function.update (Function.update x p (!a)) q (!b))

theorem exists_least_circuit {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ C : Circuit, FanInTwo C ∧ (∀ g ∈ C.gates, NOk g) ∧ C.size ≤ s ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) ∧
      (∀ D : Circuit, FanInTwo D → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x) →
        C.size ≤ D.size) := by
  classical
  let P : ℕ → Prop := fun m => ∃ C : Circuit, FanInTwo C ∧ C.size = m ∧
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x
  have hP : ∃ m, P m := by
    obtain ⟨C, hfan, hsz, hfun⟩ := h
    exact ⟨C.size, C, hfan, rfl, hfun⟩
  let m := Nat.find hP
  have hm_le : m ≤ s := by
    obtain ⟨C, hfan, hsz, hfun⟩ := h
    exact le_trans (Nat.find_min' hP ⟨C, hfan, rfl, hfun⟩) hsz
  obtain ⟨C, hfan, hsz, hfun⟩ := Nat.find_spec hP
  let C' : Circuit := ⟨C.gates.map normGate, C.output⟩
  have hnok : ∀ g ∈ C'.gates, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hfan g0 hg0)
  have hfan' : FanInTwo C' := fun g hg => (hnok g hg).1
  have hsz' : C'.size = m := by
    show (C.gates.map normGate).length = m
    rw [List.length_map]; exact hsz
  have hfun' : ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = f x := by
    intro x
    have : C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
      show (wiresFrom (C.gates.map normGate) (List.ofFn x)).getD C.output false =
        (wiresFrom C.gates (List.ofFn x)).getD C.output false
      rw [wiresFrom_norm]
    rw [this, hfun x]
  refine ⟨C', hfan', hnok, by omega, hfun', ?_⟩
  intro D hDfan hDfun
  rw [hsz']
  exact Nat.find_min' hP ⟨D, hDfan, rfl, hDfun⟩

-- One sensitive variable elimination (fixes p := b, drops at least 1 gate if nonconstant).
theorem elim_one_var {n : ℕ} (f : (Fin n → Bool) → Bool) (p : Fin n) (b : Bool) (s : ℕ)
    (hC : HasCircuitSize n f s)
    (hdep : Dep f p)
    (hnc : ∃ x y : Fin n → Bool, f (Function.update x p b) ≠ f (Function.update y p b)) :
    HasCircuitSize n (fun x => f (Function.update x p b)) (s - 1) := by
  obtain ⟨C, hfan, hnok, hsz, hfun, _⟩ := exists_least_circuit f s hC
  have hread : ∃ j : ℕ, ∃ g : Gate, C.gates[j]? = some g ∧ p.val ∈ g.inputs := by
    by_contra hno
    push Not at hno
    -- If no gate reads p.val, then either C.output = p.val (violates hnc) or C does not depend on p (violates hdep).
    have hsame : ∀ x : Fin n → Bool, ∀ w : ℕ, w ≠ p.val →
        wv C (Function.update x p (!x p)) w = wv C x w := by
      intro x w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        by_cases hlt : w < n
        · have h1 := wv_input C (Function.update x p (!x p)) ⟨w, hlt⟩
          have h2 := wv_input C x ⟨w, hlt⟩
          rw [h1, h2]
          exact Function.update_of_ne (show (⟨w, hlt⟩ : Fin n) ≠ p from fun e => hw (congrArg Fin.val e)) _ _
        · by_cases hgl : w < n + C.gates.length
          · let j := w - n
            have hj : j < C.gates.length := by omega
            have hget : C.gates[j]? = some (C.gates[j]) := List.getElem?_eq_getElem hj
            have hwj : w = n + j := by omega
            rw [hwj, wv_gate C _ j _ hget, wv_gate C _ j _ hget]
            congr 1
            apply List.map_congr_left
            intro a ha
            by_cases hal : a < n + j
            · simp only [hal, ite_true]
              exact ih a (by omega) (fun e => hno j (C.gates[j]) hget (e ▸ ha))
            · simp only [hal, ite_false]
          · rw [wv_beyond C _ w (by omega), wv_beyond C _ w (by omega)]
    by_cases ho : C.output = p.val
    · obtain ⟨x, y, hxy⟩ := hnc
      have hx : f (Function.update x p b) = b := by
        rw [← hfun, show C.eval (List.ofFn (Function.update x p b)) = wv C (Function.update x p b) p.val by
          simp [Circuit.eval, wv, ho, Circuit.wires, wiresFrom], wv_input, Function.update_self]
      have hy : f (Function.update y p b) = b := by
        rw [← hfun, show C.eval (List.ofFn (Function.update y p b)) = wv C (Function.update y p b) p.val by
          simp [Circuit.eval, wv, ho, Circuit.wires, wiresFrom], wv_input, Function.update_self]
      exact hxy (hx.trans hy.symm)
    · obtain ⟨x, hx⟩ := hdep
      have heq := hsame x C.output ho
      have h1 : f (Function.update x p (!x p)) = wv C (Function.update x p (!x p)) C.output := (hfun _).symm
      have h2 : f x = wv C x C.output := (hfun _).symm
      exact hx (h1.trans (heq.trans h2.symm))
  obtain ⟨j, g, hj, hpin⟩ := hread
  let acc := elim n C.gates (initFix n p b, [])
  have hcnt := elim_count n (initFix n p b, []) C.gates hnok {j} (by
    intro q hq
    rw [Finset.mem_singleton] at hq
    subst hq
    refine ⟨g, hj, p.val, hpin, by simp [initFix]; exact Nat.lt_of_lt_of_le p.isLt (Nat.le_add_right _ _), b, ?_⟩
    rw [elim_getD n p.val (Sum.inl false) C.gates (initFix n p b, []) (by simp [initFix, p.isLt])]
    rw [List.getD_eq_getElem _ _ (by simp [initFix, p.isLt])]
    simp [initFix, p.isLt])
  have hsz_acc : acc.2.length ≤ s - 1 := by
    have : acc.2.length + 1 ≤ C.gates.length := by simpa [acc] using hcnt
    have : C.gates.length ≤ s := hsz
    omega
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn (Function.update y p b))) acc :=
    fun y => inv_elim n (List.ofFn y) List.length_ofFn C.gates _ _ hfan (inv_initFix p b y)
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inr k =>
    refine ⟨⟨acc.2, k⟩, elim_ok n C.gates _ (by simp), hsz_acc, ?_⟩
    intro y
    have hv := ((hinv y).2 C.output).2
    rw [ho] at hv
    exact hv.trans (hfun _)
  | inl c =>
    obtain ⟨x, y, hxy⟩ := hnc
    have hx := (((hinv x).2 C.output).2).trans (hfun _)
    have hy := (((hinv y).2 C.output).2).trans (hfun _)
    rw [ho] at hx hy
    exact absurd (hx.symm.trans hy) hxy

-- Structural properties of a least normalized circuit for a non-constant function.
theorem least_no_dead {n : ℕ} (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hfan : FanInTwo C) (hfun : ∀ x, C.eval (List.ofFn x) = f x)
    (hmin : ∀ D, FanInTwo D → (∀ x, D.eval (List.ofFn x) = f x) → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length) (hne : n + j ≠ C.output) :
    ∃ k : ℕ, ∃ g : Gate, j < k ∧ C.gates[k]? = some g ∧ n + j ∈ g.inputs := by
  by_contra hno
  push Not at hno
  let pre := C.gates.take j
  let g := C.gates[j]
  let post := C.gates.drop (j + 1)
  have hsp : C.gates = pre ++ g :: post := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hplen : pre.length = j := by simp [pre, hj.le]
  have hdead : ∀ g' ∈ post, n + pre.length ∉ g'.inputs := by
    intro g' hg'
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hg'
    have hk : j + 1 + m < C.gates.length := by
      simp [post] at hm; omega
    have hget : C.gates[j + 1 + m]? = some post[m] := by
      rw [List.getElem?_eq_getElem hk]
      simp [post]
    rw [hplen]
    exact hno (j + 1 + m) post[m] (by omega) hget
  let D : Circuit := ⟨pre ++ post.map (shiftGate (n + pre.length)), shiftIdx (n + pre.length) C.output⟩
  have hDfan : FanInTwo D := by
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact hfan g' (List.mem_of_mem_take h1)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
      exact shiftGate_ok _ g0 (hfan g0 (List.mem_of_mem_drop hg0))
  have hDfun : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x := by
    intro x
    have hw := wiresFrom_delete_dead pre post g (List.ofFn x) List.length_ofFn hdead C.output (by rw [hplen]; exact hne.symm)
    rw [← hfun x]
    show (wiresFrom D.gates (List.ofFn x)).getD D.output false = (wiresFrom C.gates (List.ofFn x)).getD C.output false
    conv_rhs => rw [hsp]
    exact hw
  have hle := hmin D hDfan hDfun
  have hDsz : D.size + 1 = C.size := by
    show (pre ++ post.map (shiftGate (n + pre.length))).length + 1 = C.gates.length
    rw [List.length_append, List.length_map, hplen]
    simp [post]; omega
  omega

theorem least_no_const {n : ℕ} (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hfan : FanInTwo C) (hfun : ∀ x, C.eval (List.ofFn x) = f x)
    (hmin : ∀ D, FanInTwo D → (∀ x, D.eval (List.ofFn x) = f x) → C.size ≤ D.size)
    (hnc : ∃ x y, f x ≠ f y) (j : ℕ) (hj : j < C.gates.length) (c : Bool)
    (hc : ∀ x : Fin n → Bool, wv C x (n + j) = c) : False := by
  have hnc' : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
    obtain ⟨x, y, hxy⟩ := hnc; exact ⟨x, y, by rwa [hfun, hfun]⟩
  obtain ⟨D, hDfan, hDsz, hDfun⟩ := replace_gate_elim C hfan j (C.gates[j])
    (List.getElem?_eq_getElem hj) (Sum.inl c) trivial (fun x => (hc x).symm) hnc'
  have := hmin D hDfan (fun x => (hDfun x).trans (hfun x))
  omega

theorem least_no_copy {n : ℕ} (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hfan : FanInTwo C) (hfun : ∀ x, C.eval (List.ofFn x) = f x)
    (hmin : ∀ D, FanInTwo D → (∀ x, D.eval (List.ofFn x) = f x) → C.size ≤ D.size)
    (hnc : ∃ x y, f x ≠ f y) (j : ℕ) (hj : j < C.gates.length) (a : ℕ) (ha : a < n + j)
    (heq : ∀ x : Fin n → Bool, wv C x (n + j) = wv C x a) : False := by
  have hnc' : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
    obtain ⟨x, y, hxy⟩ := hnc; exact ⟨x, y, by rwa [hfun, hfun]⟩
  have hval : ∀ x : Fin n → Bool,
      Stat.val (wiresFrom (C.gates.take j) (List.ofFn x)) (Sum.inr a) = wv C x (n + j) := by
    intro x
    rw [heq x]
    show (wiresFrom (C.gates.take j) (List.ofFn x)).getD a false =
      (wiresFrom C.gates (List.ofFn x)).getD a false
    have hsp : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    conv_rhs => rw [hsp, wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix (C.gates.drop j) (wiresFrom (C.gates.take j) (List.ofFn x))
    rw [ht, List.getD_append _ _ _ _ (by rw [length_wiresFrom, List.length_ofFn, List.length_take]; omega)]
  obtain ⟨D, hDfan, hDsz, hDfun⟩ := replace_gate_elim C hfan j (C.gates[j])
    (List.getElem?_eq_getElem hj) (Sum.inr a) ha hval hnc'
  have := hmin D hDfan (fun x => (hDfun x).trans (hfun x))
  omega

theorem least_gate_shape {n : ℕ} (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hfan : FanInTwo C) (hnok : ∀ g ∈ C.gates, NOk g) (hfun : ∀ x, C.eval (List.ofFn x) = f x)
    (hmin : ∀ D, FanInTwo D → (∀ x, D.eval (List.ofFn x) = f x) → C.size ≤ D.size)
    (hnc : ∃ x y, f x ≠ f y) (j : ℕ) (g : Gate) (hj : C.gates[j]? = some g) :
    (g.op = GateOp.not ∧ ∃ a, g.inputs = [a] ∧ a < n + j) ∨
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j) := by
  have hjl : j < C.gates.length := (List.getElem?_eq_some_iff.1 hj).1
  have hgok := hnok g (List.mem_iff_getElem?.2 ⟨j, hj⟩)
  rcases hgok.1.1 with hop | hop | hop
  · right
    refine ⟨Or.inl hop, ?_⟩
    have hlen : g.inputs.length ≤ 2 := hgok.1.2
    rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exfalso; apply least_no_const f C hfan hfun hmin hnc j hjl true
      intro x; rw [wv_gate C x j g hj, hop, hins]; rfl
    · exfalso
      by_cases ha : a < n + j
      · apply least_no_copy f C hfan hfun hmin hnc j hjl a ha
        intro x; rw [wv_gate C x j g hj, hop, hins]; simp [ha, GateOp.eval]
      · apply least_no_const f C hfan hfun hmin hnc j hjl false
        intro x; rw [wv_gate C x j g hj, hop, hins]; simp [ha, GateOp.eval]
    · by_cases ha : a < n + j
      · by_cases hb : b < n + j
        · by_cases hab : a = b
          · subst hab; exfalso
            apply least_no_copy f C hfan hfun hmin hnc j hjl a ha
            intro x; rw [wv_gate C x j g hj, hop, hins]; simp [ha, GateOp.eval]
          · exact ⟨a, b, rfl, hab, ha, hb⟩
        · exfalso; apply least_no_const f C hfan hfun hmin hnc j hjl false
          intro x; rw [wv_gate C x j g hj, hop, hins]; simp [hb, GateOp.eval]
      · exfalso; apply least_no_const f C hfan hfun hmin hnc j hjl false
        intro x; rw [wv_gate C x j g hj, hop, hins]; simp [ha, GateOp.eval]
    · simp [hins] at hlen
  · right
    refine ⟨Or.inr hop, ?_⟩
    have hlen : g.inputs.length ≤ 2 := hgok.1.2
    rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exfalso; apply least_no_const f C hfan hfun hmin hnc j hjl false
      intro x; rw [wv_gate C x j g hj, hop, hins]; rfl
    · exfalso
      by_cases ha : a < n + j
      · apply least_no_copy f C hfan hfun hmin hnc j hjl a ha
        intro x; rw [wv_gate C x j g hj, hop, hins]; simp [ha, GateOp.eval]
      · apply least_no_const f C hfan hfun hmin hnc j hjl false
        intro x; rw [wv_gate C x j g hj, hop, hins]; simp [ha, GateOp.eval]
    · by_cases ha : a < n + j
      · by_cases hb : b < n + j
        · by_cases hab : a = b
          · subst hab; exfalso
            apply least_no_copy f C hfan hfun hmin hnc j hjl a ha
            intro x; rw [wv_gate C x j g hj, hop, hins]; simp [ha, GateOp.eval]
          · exact ⟨a, b, rfl, hab, ha, hb⟩
        · exfalso; apply least_no_copy f C hfan hfun hmin hnc j hjl a ha
          intro x; rw [wv_gate C x j g hj, hop, hins]; simp [ha, hb, GateOp.eval]
      · exfalso
        by_cases hb : b < n + j
        · apply least_no_copy f C hfan hfun hmin hnc j hjl b hb
          intro x; rw [wv_gate C x j g hj, hop, hins]; simp [ha, hb, GateOp.eval]
        · apply least_no_const f C hfan hfun hmin hnc j hjl false
          intro x; rw [wv_gate C x j g hj, hop, hins]; simp [ha, hb, GateOp.eval]
    · simp [hins] at hlen
  · left
    refine ⟨hop, ?_⟩
    have hlen : g.inputs.length ≤ 1 := hgok.2 hop
    rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
    · exfalso; apply least_no_const f C hfan hfun hmin hnc j hjl true
      intro x; rw [wv_gate C x j g hj, hop, hins]; rfl
    · by_cases ha : a < n + j
      · exact ⟨a, rfl, ha⟩
      · exfalso; apply least_no_const f C hfan hfun hmin hnc j hjl true
        intro x; rw [wv_gate C x j g hj, hop, hins]; simp [ha, GateOp.eval]
    · simp [hins] at hlen

theorem least_no_not_not {n : ℕ} (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hfan : FanInTwo C) (hnok : ∀ g ∈ C.gates, NOk g) (hfun : ∀ x, C.eval (List.ofFn x) = f x)
    (hmin : ∀ D, FanInTwo D → (∀ x, D.eval (List.ofFn x) = f x) → C.size ≤ D.size)
    (hnc : ∃ x y, f x ≠ f y) (i j a : ℕ) (hi : C.gates[i]? = some ⟨GateOp.not, [a]⟩)
    (hj : C.gates[j]? = some ⟨GateOp.not, [n + i]⟩) : False := by
  have hil : i < C.gates.length := (List.getElem?_eq_some_iff.1 hi).1
  have hjl : j < C.gates.length := (List.getElem?_eq_some_iff.1 hj).1
  have ha : a < n + i := by
    rcases least_gate_shape f C hfan hnok hfun hmin hnc i _ hi with ⟨_, a', ha', hlt⟩ | ⟨h, _⟩
    · simp at ha'; subst ha'; exact hlt
    · rcases h with h | h <;> cases h
  have hij : n + i < n + j := by
    rcases least_gate_shape f C hfan hnok hfun hmin hnc j _ hj with ⟨_, a', ha', hlt⟩ | ⟨h, _⟩
    · simp at ha'; subst ha'; exact hlt
    · rcases h with h | h <;> cases h
  apply least_no_copy f C hfan hfun hmin hnc j hjl a (by omega)
  intro x
  rw [wv_gate C x j _ hj]
  simp only [List.map_cons, List.map_nil, hij, ite_true]
  rw [wv_gate C x i _ hi]
  simp [ha, GateOp.eval]

theorem least_no_tri {n : ℕ} (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hfan : FanInTwo C) (hnok : ∀ g ∈ C.gates, NOk g) (hfun : ∀ x, C.eval (List.ofFn x) = f x)
    (hmin : ∀ D, FanInTwo D → (∀ x, D.eval (List.ofFn x) = f x) → C.size ≤ D.size)
    (hnc : ∃ x y, f x ≠ f y) (i j a : ℕ) (gi gj : Gate)
    (hi : C.gates[i]? = some gi) (hj : C.gates[j]? = some gj)
    (ha : a ∈ gi.inputs) (haj : a ∈ gj.inputs) (hij : n + i ∈ gj.inputs) : False := by
  have hil : i < C.gates.length := (List.getElem?_eq_some_iff.1 hi).1
  have hjl : j < C.gates.length := (List.getElem?_eq_some_iff.1 hj).1
  have hsi := least_gate_shape f C hfan hnok hfun hmin hnc i gi hi
  have hsj := least_gate_shape f C hfan hnok hfun hmin hnc j gj hj
  have ha_lt : a < n + i := by
    rcases hsi with ⟨_, a', ha', hlt⟩ | ⟨_, a', b', hab', _, halt, hblt⟩
    · rw [ha'] at ha; simp at ha; subst ha; exact hlt
    · rw [hab'] at ha; simp at ha; rcases ha with rfl | rfl <;> assumption
  rcases hsj with ⟨hopj, u, hu, _⟩ | ⟨hopj, u, v, huv, hne, hult, hvlt⟩
  · rw [hu] at haj hij; simp at haj hij; omega
  · have hni_lt : n + i < n + j := by
      rw [huv] at hij; simp at hij; rcases hij with rfl | rfl <;> omega
    have hpairs : (u = a ∧ v = n + i) ∨ (u = n + i ∧ v = a) := by
      rw [huv] at haj hij; simp at haj hij
      rcases haj with rfl | rfl <;> rcases hij with h1 | h1
      · omega
      · exact Or.inl ⟨rfl, h1.symm⟩
      · exact Or.inr ⟨h1.symm, rfl⟩
      · omega
    have hgj_val : ∀ x : Fin n → Bool, wv C x (n + j) =
        match gj.op with
        | GateOp.and => wv C x a && wv C x (n + i)
        | _ => wv C x a || wv C x (n + i) := by
      intro x
      have halt_j : a < n + j := by omega
      rw [wv_gate C x j gj hj, huv]
      rcases hopj with h | h <;> rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [h, halt_j, hni_lt, GateOp.eval, Bool.and_comm, Bool.or_comm]
    rcases hsi with ⟨hopi, a', ha', hlt'⟩ | ⟨hopi, a', b', hab', _, halt', hblt'⟩
    · rw [ha'] at ha; simp at ha; subst ha
      have hgi_val : ∀ x : Fin n → Bool, wv C x (n + i) = !wv C x a := by
        intro x; rw [wv_gate C x i gi hi, hopi, ha']; simp [hlt', GateOp.eval]
      rcases hopj with h | h
      · apply least_no_const f C hfan hfun hmin hnc j hjl false
        intro x; rw [hgj_val x, h, hgi_val x]; simp
      · apply least_no_const f C hfan hfun hmin hnc j hjl true
        intro x; rw [hgj_val x, h, hgi_val x]; simp
    · have hw : ∃ w < n + i, ∀ x : Fin n → Bool, wv C x (n + i) =
          match gi.op with
          | GateOp.and => wv C x a && wv C x w
          | _ => wv C x a || wv C x w := by
        rw [hab'] at ha; simp at ha
        rcases ha with rfl | rfl
        · refine ⟨b', hblt', fun x => ?_⟩
          rw [wv_gate C x i gi hi, hab']
          rcases hopi with h | h <;> simp [h, halt', hblt', GateOp.eval]
        · refine ⟨a', halt', fun x => ?_⟩
          rw [wv_gate C x i gi hi, hab']
          rcases hopi with h | h <;> simp [h, halt', hblt', GateOp.eval, Bool.and_comm, Bool.or_comm]
      obtain ⟨w, hwlt, hgi_val⟩ := hw
      rcases hopi with hi' | hi' <;> rcases hopj with hj' | hj'
      · apply least_no_copy f C hfan hfun hmin hnc j hjl (n + i) hni_lt
        intro x; rw [hgj_val x, hj', hgi_val x, hi']; cases wv C x a <;> cases wv C x w <;> rfl
      · apply least_no_copy f C hfan hfun hmin hnc j hjl a (by omega)
        intro x; rw [hgj_val x, hj', hgi_val x, hi']; cases wv C x a <;> cases wv C x w <;> rfl
      · apply least_no_copy f C hfan hfun hmin hnc j hjl a (by omega)
        intro x; rw [hgj_val x, hj', hgi_val x, hi']; cases wv C x a <;> cases wv C x w <;> rfl
      · apply least_no_copy f C hfan hfun hmin hnc j hjl (n + i) hni_lt
        intro x; rw [hgj_val x, hj', hgi_val x, hi']; cases wv C x a <;> cases wv C x w <;> rfl

-- In a least circuit, any input read by at least one gate must be sensitive.
theorem least_read_dep {n : ℕ} (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hfan : FanInTwo C) (hnok : ∀ g ∈ C.gates, NOk g) (hfun : ∀ x, C.eval (List.ofFn x) = f x)
    (hmin : ∀ D, FanInTwo D → (∀ x, D.eval (List.ofFn x) = f x) → C.size ≤ D.size)
    (hnc : ∃ x y, f x ≠ f y) (p : Fin n) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) (hp : p.val ∈ g.inputs) : Dep f p := by
  by_contra hnd
  have hsame : ∀ x : Fin n → Bool, f (Function.update x p false) = f x := by
    intro x
    cases hx : x p
    · rw [show Function.update x p false = x by
        funext i
        by_cases h : i = p
        · subst h; simp [hx]
        · exact Function.update_of_ne h _ _]
    · have := not_exists.mp hnd x
      rw [hx] at this
      exact not_ne_iff.mp this
  let acc := elim n C.gates (initFix n p false, [])
  have hcnt := elim_count n (initFix n p false, []) C.gates hnok {j} (by
    intro q hq; rw [Finset.mem_singleton] at hq; subst hq
    refine ⟨g, hj, p.val, hp, by simp [initFix]; exact Nat.lt_of_lt_of_le p.isLt (Nat.le_add_right _ _), false, ?_⟩
    rw [elim_getD n p.val (Sum.inl false) C.gates (initFix n p false, []) (by simp [initFix, p.isLt])]
    rw [List.getD_eq_getElem _ _ (by simp [initFix, p.isLt])]
    simp [initFix, p.isLt])
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn (Function.update y p false))) acc :=
    fun y => inv_elim n (List.ofFn y) List.length_ofFn C.gates _ _ hfan (inv_initFix p false y)
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inr k =>
    have hDfun : ∀ y : Fin n → Bool, Circuit.eval ⟨acc.2, k⟩ (List.ofFn y) = f y := by
      intro y
      have hv := ((hinv y).2 C.output).2
      rw [ho] at hv
      exact hv.trans ((hfun _).trans (hsame y))
    have hle := hmin ⟨acc.2, k⟩ (elim_ok n C.gates _ (by simp)) hDfun
    change C.gates.length ≤ acc.2.length at hle
    change acc.2.length + ({j} : Finset ℕ).card ≤ ([] : List Gate).length + C.gates.length at hcnt
    simp only [List.length_nil, Nat.zero_add, Finset.card_singleton] at hcnt
    omega
  | inl c =>
    obtain ⟨x, y, hxy⟩ := hnc
    have hx := (((hinv x).2 C.output).2).trans ((hfun _).trans (hsame x))
    have hy := (((hinv y).2 C.output).2).trans ((hfun _).trans (hsame y))
    rw [ho] at hx hy
    exact hxy (hx.symm.trans hy)

-- Helper: if a gate's status under initFix p b is constant, then it cannot be output (by RestrNC) so it has a later reader.
theorem least_const_reader {n : ℕ} (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hfan : FanInTwo C) (hfun : ∀ x, C.eval (List.ofFn x) = f x)
    (hmin : ∀ D, FanInTwo D → (∀ x, D.eval (List.ofFn x) = f x) → C.size ≤ D.size)
    (hrnc : RestrNC f) (p : Fin n) (hdep : Dep f p) (b : Bool) (j : ℕ)
    (hj : j < C.gates.length) (c : Bool)
    (hc : (elim n C.gates (initFix n p b, [])).1.getD (n + j) (Sum.inl false) = Sum.inl c) :
    ∃ r : ℕ, ∃ gr : Gate, j < r ∧ C.gates[r]? = some gr ∧ n + j ∈ gr.inputs := by
  have hne : n + j ≠ C.output := by
    intro heq
    obtain ⟨x, y, hxy⟩ := hrnc p hdep b
    have hinv : ∀ z : Fin n → Bool, Inv n (List.ofFn z) (wiresFrom C.gates (List.ofFn (Function.update z p b)))
        (elim n C.gates (initFix n p b, [])) :=
      fun z => inv_elim n (List.ofFn z) List.length_ofFn C.gates _ _ hfan (inv_initFix p b z)
    have hx := (((hinv x).2 C.output).2).trans (hfun _)
    have hy := (((hinv y).2 C.output).2).trans (hfun _)
    rw [← heq, hc] at hx hy
    exact hxy (hx.symm.trans hy)
  exact least_no_dead f C hfan hfun hmin j hj hne

-- Helper: compute the status of gate j in elim n gs acc0 directly from its inputs.
theorem elim_gate_stat (n : ℕ) (gs : List Gate) (acc0 : List Stat × List Gate) (hl : acc0.1.length = n)
    (j : ℕ) (g : Gate) (hj : gs[j]? = some g) (hins : ∀ a ∈ g.inputs, a < n + j) :
    let acc := elim n gs acc0
    acc.1.getD (n + j) (Sum.inl false) =
      (simplify g.op (n + (elim n (gs.take j) acc0).2.length)
        (g.inputs.map fun a => acc.1.getD a (Sum.inl false))).2 := by
  obtain ⟨hjl, heq⟩ := List.getElem?_eq_some_iff.1 hj
  have hsp : gs = gs.take j ++ g :: gs.drop (j + 1) := by
    rw [← heq, ← List.drop_eq_getElem_cons hjl, List.take_append_drop]
  have hplen : (gs.take j).length = j := by simp [hjl.le]
  intro acc
  have h1 : acc.1.getD (n + j) (Sum.inl false) =
      (elimStep n (elim n (gs.take j) acc0) g).1.getD (n + j) (Sum.inl false) := by
    dsimp only [acc]; conv_lhs => rw [hsp]
    exact elim_split_getD n (gs.take j) g (gs.drop (j + 1)) acc0 (n + j) (Sum.inl false) (by omega)
  rw [h1]
  have hlen : (elim n (gs.take j) acc0).1.length = n + j := by rw [elim_fst_len, hl, hplen]
  show ((elim n (gs.take j) acc0).1 ++ [_]).getD (n + j) (Sum.inl false) = _
  rw [← hlen, getD_snoc_eq]
  congr 2
  apply List.map_congr_left
  intro a ha
  dsimp only [acc]
  conv_rhs => rw [hsp]
  exact (elim_split_getD_lt n (gs.take j) g (gs.drop (j + 1)) acc0 a (Sum.inl false) (by
    have := hins a ha; omega)).symm

-- Helper: literal functions violate RestrNC.
theorem not_literal_of_restrNC {n : ℕ} (f : (Fin n → Bool) → Bool) (hdep : ∃ p, Dep f p)
    (hrnc : RestrNC f) (v : Fin n) (c : Bool) (h : ∀ x, f x = xor (x v) c) : False := by
  have hdv : Dep f v := by
    refine ⟨fun _ => false, ?_⟩
    rw [h, h]; simp
  obtain ⟨x, y, hxy⟩ := hrnc v hdv false
  rw [h, h] at hxy
  simp at hxy

-- Helper: constant functions violate hdep.
theorem not_const_of_dep {n : ℕ} (f : (Fin n → Bool) → Bool) (hdep : ∃ p, Dep f p) :
    ∃ x y, f x ≠ f y := by
  obtain ⟨p, x, hx⟩ := hdep
  exact ⟨Function.update x p (!x p), x, hx⟩

-- The 3-or-4 reader step (L107), self-contained.
theorem fanout_step_3_4 {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hdep : ∃ p, Dep f p) (hrnc : RestrNC f) (hnf : NoFunnel f)
    (hC : HasCircuitSize n f s) :
    (∃ (y : Fin n) (s' : ℕ), s' + 3 ≤ s ∧
      HasCircuitSize n (fun x => f (Function.update x y false)) s') ∨
    (∃ (y : Fin n) (s' : ℕ), s' + 4 ≤ s ∧
      HasCircuitSize n (fun x => f (Function.update x y true)) s') := by
  obtain ⟨C, hfan, hnok, hsz, hfun, hmin⟩ := exists_least_circuit f s hC
  have hnc : ∃ x y, f x ≠ f y := not_const_of_dep f hdep
  -- Helper to extract a HasCircuitSize witness from a Finset S of eliminated gates for fixing y := b.
  have mkFix : ∀ (y : Fin n) (b : Bool) (S : Finset ℕ), Dep f y →
      (∀ q ∈ S, ∃ g, C.gates[q]? = some g ∧ ∃ a ∈ g.inputs, a < n + q ∧
        ∃ c, (elim n C.gates (initFix n y b, [])).1.getD a (Sum.inl false) = Sum.inl c) →
      ∃ s', s' + S.card ≤ s ∧ HasCircuitSize n (fun x => f (Function.update x y b)) s' := by
    intro y b S hdy hS
    let acc := elim n C.gates (initFix n y b, [])
    have hcnt := elim_count n (initFix n y b, []) C.gates hnok S (by
      intro q hq
      obtain ⟨g, hqg, a, ha, halt, c, hc⟩ := hS q hq
      exact ⟨g, hqg, a, ha, by simpa [initFix] using halt, c, hc⟩)
    have hinv : ∀ z : Fin n → Bool, Inv n (List.ofFn z) (wiresFrom C.gates (List.ofFn (Function.update z y b))) acc :=
      fun z => inv_elim n (List.ofFn z) List.length_ofFn C.gates _ _ hfan (inv_initFix y b z)
    cases ho : acc.1.getD C.output (Sum.inl false) with
    | inr k =>
      refine ⟨acc.2.length, by
        change acc.2.length + S.card ≤ ([] : List Gate).length + C.gates.length at hcnt
        simp only [List.length_nil, Nat.zero_add] at hcnt
        change C.gates.length ≤ s at hsz; omega,
        ⟨⟨acc.2, k⟩, elim_ok n C.gates _ (by simp), le_refl _, ?_⟩⟩
      intro z
      have hv := ((hinv z).2 C.output).2
      rw [ho] at hv
      exact hv.trans (hfun _)
    | inl c =>
      obtain ⟨x1, x2, hne⟩ := hrnc y hdy b
      have hx1 := (((hinv x1).2 C.output).2).trans (hfun _)
      have hx2 := (((hinv x2).2 C.output).2).trans (hfun _)
      rw [ho] at hx1 hx2
      exact absurd (hx1.symm.trans hx2) hne
  have hinit_get : ∀ (y : Fin n) (b : Bool),
      (elim n C.gates (initFix n y b, [])).1.getD y.val (Sum.inl false) = Sum.inl b := by
    intro y b
    rw [elim_getD n y.val (Sum.inl false) C.gates (initFix n y b, []) (by simp [initFix, y.isLt])]
    rw [List.getD_eq_getElem _ _ (by simp [initFix, y.isLt])]
    simp [initFix, y.isLt]
  -- Case 1: Some input y has at least 2 distinct readers j1 < j2.
  by_cases hcase1 : ∃ (y : Fin n) (j1 j2 : ℕ) (g1 g2 : Gate),
      j1 < j2 ∧ C.gates[j1]? = some g1 ∧ C.gates[j2]? = some g2 ∧
      y.val ∈ g1.inputs ∧ y.val ∈ g2.inputs
  · obtain ⟨y, j1, j2, g1, g2, hj12, hg1, hg2, hy1, hy2⟩ := hcase1
    have hdy : Dep f y := least_read_dep f C hfan hnok hfun hmin hnc y j1 g1 hg1 hy1
    have hj1l : j1 < C.gates.length := (List.getElem?_eq_some_iff.1 hg1).1
    have hj2l : j2 < C.gates.length := (List.getElem?_eq_some_iff.1 hg2).1
    have hs1 := least_gate_shape f C hfan hnok hfun hmin hnc j1 g1 hg1
    have hs2 := least_gate_shape f C hfan hnok hfun hmin hnc j2 g2 hg2
    -- Helper: if g_k is NOT [y] or AND with y, fixing y := false makes gate k constant.
    have hfalse_const : ∀ (k : ℕ) (gk : Gate) (hk : C.gates[k]? = some gk),
        y.val ∈ gk.inputs → (gk.op = GateOp.not ∨ gk.op = GateOp.and) →
        ∃ c, (elim n C.gates (initFix n y false, [])).1.getD (n + k) (Sum.inl false) = Sum.inl c := by
      intro k gk hk hyk hop
      rcases least_gate_shape f C hfan hnok hfun hmin hnc k gk hk with
        ⟨hnk, a, ha, halt⟩ | ⟨hbk, a, b, hab, _, halt, hblt⟩
      · rw [ha] at hyk; simp at hyk; subst hyk
        have hst := elim_gate_stat n C.gates (initFix n y false, []) (by simp [initFix]) k gk hk
          (by rw [ha]; simp [halt])
        rw [hst, hnk, ha, List.map_singleton, hinit_get y false]
        exact ⟨true, rfl⟩
      · rcases hop with h | h
        · rcases hbk with h' | h' <;> rw [h] at h' <;> cases h'
        · have hst := elim_gate_stat n C.gates (initFix n y false, []) (by simp [initFix]) k gk hk
            (by rw [hab]; simp [halt, hblt])
          rw [hst, h, hab]
          rw [hab] at hyk; simp at hyk
          rcases hyk with rfl | rfl
          · rw [List.map_cons, List.map_singleton, hinit_get y false]
            cases (elim n C.gates (initFix n y false, [])).1.getD b (Sum.inl false) <;>
              exact ⟨false, by simp [simplify, simpAnd]⟩
          · rw [List.map_cons, List.map_singleton, hinit_get y false]
            cases (elim n C.gates (initFix n y false, [])).1.getD a (Sum.inl false) <;>
              exact ⟨false, by simp [simplify, simpAnd]⟩
    by_cases h1na : g1.op = GateOp.not ∨ g1.op = GateOp.and
    · obtain ⟨c1, hc1⟩ := hfalse_const j1 g1 hg1 hy1 h1na
      obtain ⟨r, gr, hr1, hgr, hrin⟩ := least_const_reader f C hfan hfun hmin hrnc y hdy false j1 hj1l c1 hc1
      have hr2 : r ≠ j2 := by
        intro heq; subst heq
        have hgr2 : gr = g2 := Option.some.inj (hgr.symm.trans hg2)
        subst hgr2
        exact least_no_tri f C hfan hnok hfun hmin hnc j1 r y.val g1 gr hg1 hgr hy1 hy2 hrin
      left
      obtain ⟨s', hs', hCs'⟩ := mkFix y false {j1, j2, r} hdy (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact ⟨g1, hg1, y.val, hy1, by omega, false, hinit_get y false⟩
        · exact ⟨g2, hg2, y.val, hy2, by omega, false, hinit_get y false⟩
        · exact ⟨gr, hgr, n + j1, hrin, by omega, c1, hc1⟩)
      have hcard : ({j1, j2, r} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega),
            Finset.card_insert_of_notMem (by simp; exact hr2.symm), Finset.card_singleton]
      exact ⟨y, s', by omega, hCs'⟩
    · by_cases h2na : g2.op = GateOp.not ∨ g2.op = GateOp.and
      · obtain ⟨c2, hc2⟩ := hfalse_const j2 g2 hg2 hy2 h2na
        obtain ⟨r, gr, hr2, hgr, hrin⟩ := least_const_reader f C hfan hfun hmin hrnc y hdy false j2 hj2l c2 hc2
        left
        obtain ⟨s', hs', hCs'⟩ := mkFix y false {j1, j2, r} hdy (by
          intro q hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl
          · exact ⟨g1, hg1, y.val, hy1, by omega, false, hinit_get y false⟩
          · exact ⟨g2, hg2, y.val, hy2, by omega, false, hinit_get y false⟩
          · exact ⟨gr, hgr, n + j2, hrin, by omega, c2, hc2⟩)
        have hcard : ({j1, j2, r} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
        exact ⟨y, s', by omega, hCs'⟩
      · -- Both g1 and g2 are OR gates reading y; set y := true.
        have h1or : g1.op = GateOp.or := by
          rcases hs1 with ⟨h, _⟩ | ⟨h | h, _⟩
          · exact absurd (Or.inl h) h1na
          · exact absurd (Or.inr h) h1na
          · exact h
        have h2or : g2.op = GateOp.or := by
          rcases hs2 with ⟨h, _⟩ | ⟨h | h, _⟩
          · exact absurd (Or.inl h) h2na
          · exact absurd (Or.inr h) h2na
          · exact h
        have htrue_or : ∀ (k : ℕ) (gk : Gate) (hk : C.gates[k]? = some gk),
            y.val ∈ gk.inputs → gk.op = GateOp.or →
            (elim n C.gates (initFix n y true, [])).1.getD (n + k) (Sum.inl false) = Sum.inl true := by
          intro k gk hk hyk hor
          rcases least_gate_shape f C hfan hnok hfun hmin hnc k gk hk with
            ⟨h, _⟩ | ⟨_, a, b, hab, _, halt, hblt⟩
          · rw [hor] at h; cases h
          · have hst := elim_gate_stat n C.gates (initFix n y true, []) (by simp [initFix]) k gk hk
              (by rw [hab]; simp [halt, hblt])
            rw [hst, hor, hab]
            rw [hab] at hyk; simp at hyk
            rcases hyk with rfl | rfl
            · rw [List.map_cons, List.map_singleton, hinit_get y true]
              cases (elim n C.gates (initFix n y true, [])).1.getD b (Sum.inl false) <;>
                simp [simplify, simpOr]
            · rw [List.map_cons, List.map_singleton, hinit_get y true]
              cases (elim n C.gates (initFix n y true, [])).1.getD a (Sum.inl false) <;>
                simp [simplify, simpOr]
        have hc1 := htrue_or j1 g1 hg1 hy1 h1or
        have hc2 := htrue_or j2 g2 hg2 hy2 h2or
        obtain ⟨r1, gr1, hr11, hgr1, hrin1⟩ := least_const_reader f C hfan hfun hmin hrnc y hdy true j1 hj1l true hc1
        obtain ⟨r2, gr2, hr22, hgr2, hrin2⟩ := least_const_reader f C hfan hfun hmin hrnc y hdy true j2 hj2l true hc2
        have hr1_ne_j2 : r1 ≠ j2 := by
          intro heq; subst heq
          have hgr : gr1 = g2 := Option.some.inj (hgr1.symm.trans hg2)
          subst hgr
          exact least_no_tri f C hfan hnok hfun hmin hnc j1 r1 y.val g1 gr1 hg1 hgr1 hy1 hy2 hrin1
        right
        by_cases hrr : r1 = r2
        · subst hrr
          have hgr_eq : gr1 = gr2 := Option.some.inj (hgr1.symm.trans hgr2)
          subst hgr_eq
          have hr1l : r1 < C.gates.length := (List.getElem?_eq_some_iff.1 hgr1).1
          -- r1 reads both n + j1 and n + j2, both mapped to Sum.inl true, so r1 itself maps to a constant!
          have hr1_const : ∃ c, (elim n C.gates (initFix n y true, [])).1.getD (n + r1) (Sum.inl false) = Sum.inl c := by
            rcases least_gate_shape f C hfan hnok hfun hmin hnc r1 gr1 hgr1 with
              ⟨hop, a, ha, halt⟩ | ⟨hop, a, b, hab, _, halt, hblt⟩
            · rw [ha] at hrin1 hrin2; simp at hrin1 hrin2; omega
            · have hst := elim_gate_stat n C.gates (initFix n y true, []) (by simp [initFix]) r1 gr1 hgr1
                (by rw [hab]; simp [halt, hblt])
              rw [hst, hab]
              rw [hab] at hrin1 hrin2; simp at hrin1 hrin2
              rcases hrin1 with rfl | rfl <;> rcases hrin2 with h | h
              · omega
              · subst h; refine ⟨true, ?_⟩
                rw [List.map_cons, List.map_singleton, hc1, hc2]
                rcases hop with h' | h' <;> simp [h', simplify, simpAnd, simpOr]
              · subst h; refine ⟨true, ?_⟩
                rw [List.map_cons, List.map_singleton, hc2, hc1]
                rcases hop with h' | h' <;> simp [h', simplify, simpAnd, simpOr]
              · omega
          obtain ⟨cr, hcr⟩ := hr1_const
          obtain ⟨r3, gr3, hr3r, hgr3, hr3in⟩ := least_const_reader f C hfan hfun hmin hrnc y hdy true r1 hr1l cr hcr
          obtain ⟨s', hs', hCs'⟩ := mkFix y true {j1, j2, r1, r3} hdy (by
            intro q hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · exact ⟨g1, hg1, y.val, hy1, by omega, true, hinit_get y true⟩
            · exact ⟨g2, hg2, y.val, hy2, by omega, true, hinit_get y true⟩
            · exact ⟨gr1, hgr1, n + j1, hrin1, by omega, true, hc1⟩
            · exact ⟨gr3, hgr3, n + r1, hr3in, by omega, cr, hcr⟩)
          have hcard : ({j1, j2, r1, r3} : Finset ℕ).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
          exact ⟨y, s', by omega, hCs'⟩
        · obtain ⟨s', hs', hCs'⟩ := mkFix y true {j1, j2, r1, r2} hdy (by
            intro q hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · exact ⟨g1, hg1, y.val, hy1, by omega, true, hinit_get y true⟩
            · exact ⟨g2, hg2, y.val, hy2, by omega, true, hinit_get y true⟩
            · exact ⟨gr1, hgr1, n + j1, hrin1, by omega, true, hc1⟩
            · exact ⟨gr2, hgr2, n + j2, hrin2, by omega, true, hc2⟩)
          have hcard : ({j1, j2, r1, r2} : Finset ℕ).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_insert_of_notMem (by simp; exact ⟨hr1_ne_j2.symm, by omega⟩),
                Finset.card_insert_of_notMem (by simp; exact hrr), Finset.card_singleton]
          exact ⟨y, s', by omega, hCs'⟩
  · -- Case 2: Every input has <= 1 reader. Check if some NOT gate on an input has >= 2 readers.
    push Not at hcase1
    by_cases hcase2 : ∃ (y : Fin n) (h j1 j2 : ℕ) (g1 g2 : Gate),
        C.gates[h]? = some ⟨GateOp.not, [y.val]⟩ ∧
        j1 < j2 ∧ C.gates[j1]? = some g1 ∧ C.gates[j2]? = some g2 ∧
        n + h ∈ g1.inputs ∧ n + h ∈ g2.inputs
    · obtain ⟨y, h, j1, j2, g1, g2, hgh, hj12, hg1, hg2, hh1, hh2⟩ := hcase2
      have hdy : Dep f y := least_read_dep f C hfan hnok hfun hmin hnc y h _ hgh (by simp)
      have hh1_lt : h < j1 := by
        rcases least_gate_shape f C hfan hnok hfun hmin hnc j1 g1 hg1 with
          ⟨_, a, ha, halt⟩ | ⟨_, a, b, hab, _, halt, hblt⟩
        · rw [ha] at hh1; simp at hh1; omega
        · rw [hab] at hh1; simp at hh1; rcases hh1 with rfl | rfl <;> omega
      have hch : (elim n C.gates (initFix n y false, [])).1.getD (n + h) (Sum.inl false) = Sum.inl true := by
        have hst := elim_gate_stat n C.gates (initFix n y false, []) (by simp [initFix]) h _ hgh
          (by simp; exact Nat.lt_of_lt_of_le y.isLt (Nat.le_add_right _ _))
        rw [hst, List.map_singleton, hinit_get y false]; rfl
      left
      obtain ⟨s', hs', hCs'⟩ := mkFix y false {h, j1, j2} hdy (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact ⟨⟨GateOp.not, [y.val]⟩, hgh, y.val, by simp, by omega, false, hinit_get y false⟩
        · exact ⟨g1, hg1, n + h, hh1, by omega, true, hch⟩
        · exact ⟨g2, hg2, n + h, hh2, by omega, true, hch⟩)
      have hcard : ({h, j1, j2} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega),
            Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      exact ⟨y, s', by omega, hCs'⟩
    · -- Case 3: Every input and every NOT-of-input has <= 1 reader. Derive contradiction via NoFunnel.
      push Not at hcase2
      exfalso
      -- There must be a binary gate (otherwise output is a literal or constant).
      have hgate_eq : ∀ (x : Gate) (op : GateOp) (ins : List ℕ),
          x.op = op → x.inputs = ins → x = ⟨op, ins⟩ := by
        intro ⟨_, _⟩ _ _ rfl rfl; rfl
      have hex_bin : ∃ j : ℕ, ∃ g : Gate, C.gates[j]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) := by
        by_contra hnobin
        have hallnot : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
            ∃ p : Fin n, g = ⟨GateOp.not, [p.val]⟩ := by
          intro j g hj
          rcases least_gate_shape f C hfan hnok hfun hmin hnc j g hj with
            ⟨hop, a, ha, halt⟩ | ⟨hop, _⟩
          · by_cases han : a < n
            · exact ⟨⟨a, han⟩, hgate_eq g _ _ hop ha⟩
            · let i := a - n
              have hi : i < C.gates.length := by
                have := (List.getElem?_eq_some_iff.1 hj).1; omega
              have hgi : C.gates[i]? = some (C.gates[i]) := List.getElem?_eq_getElem hi
              rcases least_gate_shape f C hfan hnok hfun hmin hnc i _ hgi with
                ⟨hopi, a', ha', _⟩ | ⟨hopi, _⟩
              · have hgi_eq : C.gates[i] = ⟨GateOp.not, [a']⟩ := hgate_eq _ _ _ hopi ha'
                rw [hgi_eq] at hgi
                have hgj' : g = ⟨GateOp.not, [n + i]⟩ :=
                  hgate_eq g _ _ hop (by rw [ha, show a = n + i by omega])
                rw [hgj'] at hj
                exact False.elim (least_no_not_not f C hfan hnok hfun hmin hnc i j a' hgi hj)
              · exact False.elim (hnobin ⟨i, _, hgi, hopi⟩)
          · exact False.elim (hnobin ⟨j, g, hj, hop⟩)
        by_cases ho1 : C.output < n
        · exact not_literal_of_restrNC f hdep hrnc ⟨C.output, ho1⟩ false (fun x => by
            rw [← hfun x]; show wv C x C.output = xor (x ⟨C.output, ho1⟩) false
            rw [wv_input C x ⟨C.output, ho1⟩]; simp)
        · by_cases ho2 : C.output < n + C.gates.length
          · let j := C.output - n
            have hj : C.gates[j]? = some (C.gates[j]) := List.getElem?_eq_getElem (by omega)
            obtain ⟨p, hp⟩ := hallnot j _ hj
            rw [hp] at hj
            exact not_literal_of_restrNC f hdep hrnc p true (fun x => by
              rw [← hfun x]
              show wv C x C.output = xor (x p) true
              rw [show C.output = n + j by omega, wv_gate C x j _ hj]
              simp only [List.map_cons, List.map_nil, Nat.lt_of_lt_of_le p.isLt (Nat.le_add_right _ _), ite_true, GateOp.eval]
              rw [wv_input C x p]; simp)
          · obtain ⟨x, y, hxy⟩ := hnc
            have hx : f x = false := (hfun x).symm.trans (wv_beyond C x C.output (by omega))
            have hy : f y = false := (hfun y).symm.trans (wv_beyond C y C.output (by omega))
            exact hxy (hx.trans hy.symm)
      -- Let t be the FIRST binary gate.
      classical
      obtain ⟨t, ⟨gt, hgt, hgt_op⟩, ht_min⟩ : ∃ t, (∃ g, C.gates[t]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or)) ∧
          ∀ j < t, ¬ ∃ g, C.gates[j]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) :=
        ⟨Nat.find hex_bin, Nat.find_spec hex_bin, fun j hj => Nat.find_min hex_bin hj⟩
      have ht_first : ∀ j < t, ∀ g, C.gates[j]? = some g → ∃ p : Fin n, g = ⟨GateOp.not, [p.val]⟩ := by
        intro j hjt g hgj
        have hnotbin : ¬ (g.op = GateOp.and ∨ g.op = GateOp.or) :=
          fun h => ht_min j hjt ⟨g, hgj, h⟩
        rcases least_gate_shape f C hfan hnok hfun hmin hnc j g hgj with
          ⟨hop, a, ha, halt⟩ | ⟨hop, _⟩
        · by_cases han : a < n
          · exact ⟨⟨a, han⟩, hgate_eq g _ _ hop ha⟩
          · let i := a - n
            have hit : i < t := by omega
            have hi : i < C.gates.length := by have := (List.getElem?_eq_some_iff.1 hgj).1; omega
            have hgi : C.gates[i]? = some (C.gates[i]) := List.getElem?_eq_getElem hi
            have hnotbin_i : ¬ ((C.gates[i]).op = GateOp.and ∨ (C.gates[i]).op = GateOp.or) :=
              fun h => ht_min i hit ⟨C.gates[i], hgi, h⟩
            rcases least_gate_shape f C hfan hnok hfun hmin hnc i _ hgi with
              ⟨hopi, a', ha', _⟩ | ⟨hopi, _⟩
            · have hgi_eq : C.gates[i] = ⟨GateOp.not, [a']⟩ := hgate_eq _ _ _ hopi ha'
              rw [hgi_eq] at hgi
              have hgj' : g = ⟨GateOp.not, [n + i]⟩ :=
                hgate_eq g _ _ hop (by rw [ha, show a = n + i by omega])
              rw [hgj'] at hgj
              exact False.elim (least_no_not_not f C hfan hnok hfun hmin hnc i j a' hgi hgj)
            · exact False.elim (hnotbin_i hopi)
        · exact False.elim (hnotbin hop)
      have hgt_shape : ∃ u v, gt.inputs = [u, v] ∧ u ≠ v ∧ u < n + t ∧ v < n + t := by
        rcases least_gate_shape f C hfan hnok hfun hmin hnc t gt hgt with ⟨h, _⟩ | ⟨_, h⟩
        · rcases hgt_op with h' | h' <;> rw [h] at h' <;> cases h'
        · exact h
      obtain ⟨u, v, hgt_in, huv_ne, hult, hvlt⟩ := hgt_shape
      -- Extract literals (p, cu) for u and (q, cv) for v.
      have hlit : ∀ w < n + t, ∃ (r : Fin n) (cr : Bool),
          (∀ x, wv C x w = xor (x r) cr) ∧
          (w = r.val ∨ ∃ h < t, w = n + h ∧ C.gates[h]? = some ⟨GateOp.not, [r.val]⟩) := by
        intro w hw
        by_cases hwn : w < n
        · exact ⟨⟨w, hwn⟩, false, fun x => by rw [wv_input C x ⟨w, hwn⟩]; simp, Or.inl rfl⟩
        · let h := w - n
          have hht : h < t := by omega
          have hhl : h < C.gates.length := by
            have := (List.getElem?_eq_some_iff.1 hgt).1; omega
          have hgh : C.gates[h]? = some (C.gates[h]) := List.getElem?_eq_getElem hhl
          obtain ⟨r, hr⟩ := ht_first h hht (C.gates[h]) hgh
          rw [hr] at hgh
          refine ⟨r, true, fun x => ?_, Or.inr ⟨h, hht, by omega, hgh⟩⟩
          rw [show w = n + h by omega, wv_gate C x h _ hgh]
          simp only [List.map_cons, List.map_nil, Nat.lt_of_lt_of_le r.isLt (Nat.le_add_right _ _), ite_true, GateOp.eval]
          rw [wv_input C x r]; simp
      obtain ⟨p, cu, hup, hu_src⟩ := hlit u hult
      obtain ⟨q, cv, hvq, hv_src⟩ := hlit v hvlt
      have hdp : Dep f p := by
        rcases hu_src with rfl | ⟨hu, _, _, hghu⟩
        · exact least_read_dep f C hfan hnok hfun hmin hnc p t gt hgt (by rw [hgt_in]; simp)
        · exact least_read_dep f C hfan hnok hfun hmin hnc p hu _ hghu (by simp)
      have hdq : Dep f q := by
        rcases hv_src with rfl | ⟨hv, _, _, hghv⟩
        · exact least_read_dep f C hfan hnok hfun hmin hnc q t gt hgt (by rw [hgt_in]; simp)
        · exact least_read_dep f C hfan hnok hfun hmin hnc q hv _ hghv (by simp)
      have hpq : p ≠ q := by
        intro heq; subst heq
        have htl : t < C.gates.length := (List.getElem?_eq_some_iff.1 hgt).1
        have htval : ∀ x, wv C x (n + t) =
            match gt.op with
            | GateOp.and => xor (x p) cu && xor (x p) cv
            | _ => xor (x p) cu || xor (x p) cv := by
          intro x
          rw [wv_gate C x t gt hgt, hgt_in]
          rcases hgt_op with h | h <;> simp [h, hult, hvlt, hup, hvq, GateOp.eval]
        by_cases hcc : cu = cv
        · subst hcc
          apply least_no_copy f C hfan hfun hmin hnc t htl u hult
          intro x; rw [htval x, hup x]; rcases hgt_op with h | h <;> simp [h]
        · rcases hgt_op with h | h
          · apply least_no_const f C hfan hfun hmin hnc t htl false
            intro x; rw [htval x, h]; cases cu <;> cases cv <;> try exact absurd rfl hcc
            · cases x p <;> rfl
            · cases x p <;> rfl
          · apply least_no_const f C hfan hfun hmin hnc t htl true
            intro x; rw [htval x, h]; cases cu <;> cases cv <;> try exact absurd rfl hcc
            · cases x p <;> rfl
            · cases x p <;> rfl
      -- Unique reader helper from hcase1 and hcase2.
      have huniq_in : ∀ (r : Fin n) (j1 j2 : ℕ) (g1 g2 : Gate),
          C.gates[j1]? = some g1 → C.gates[j2]? = some g2 →
          r.val ∈ g1.inputs → r.val ∈ g2.inputs → j1 = j2 := by
        intro r j1 j2 g1 g2 h1 h2 hr1 hr2
        rcases lt_trichotomy j1 j2 with hlt | heq | hgt'
        · exact False.elim (hcase1 r j1 j2 g1 g2 hlt h1 h2 hr1 hr2)
        · exact heq
        · exact False.elim (hcase1 r j2 j1 g2 g1 hgt' h2 h1 hr2 hr1)
      have huniq_not : ∀ (r : Fin n) (h j1 j2 : ℕ) (g1 g2 : Gate),
          C.gates[h]? = some ⟨GateOp.not, [r.val]⟩ →
          C.gates[j1]? = some g1 → C.gates[j2]? = some g2 →
          n + h ∈ g1.inputs → n + h ∈ g2.inputs → j1 = j2 := by
        intro r h j1 j2 g1 g2 hgh h1 h2 hr1 hr2
        rcases lt_trichotomy j1 j2 with hlt | heq | hgt'
        · exact False.elim (hcase2 r h j1 j2 g1 g2 hgh hlt h1 h2 hr1 hr2)
        · exact heq
        · exact False.elim (hcase2 r h j2 j1 g2 g1 hgh hgt' h2 h1 hr2 hr1)
      -- Any wire w outside {p.val, q.val, u, v} depends on (p, q) only through wire n + t.
      have hisol : ∀ (x1 x2 : Fin n → Bool),
          (∀ i : Fin n, i ≠ p → i ≠ q → x1 i = x2 i) →
          wv C x1 (n + t) = wv C x2 (n + t) →
          ∀ w : ℕ, w ≠ p.val → w ≠ q.val → w ≠ u → w ≠ v → wv C x1 w = wv C x2 w := by
        intro x1 x2 hagree ht_eq w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hwp hwq hwu hwv
          by_cases hwn : w < n
          · rw [wv_input C x1 ⟨w, hwn⟩, wv_input C x2 ⟨w, hwn⟩]
            exact hagree ⟨w, hwn⟩ (fun e => hwp (congrArg Fin.val e)) (fun e => hwq (congrArg Fin.val e))
          · by_cases hgl : w < n + C.gates.length
            · let j := w - n
              have hj : j < C.gates.length := by omega
              have hgj : C.gates[j]? = some (C.gates[j]) := List.getElem?_eq_getElem hj
              have hwj : w = n + j := by omega
              by_cases hjt : j = t
              · rw [hwj, hjt]; exact ht_eq
              · rw [hwj, wv_gate C x1 j _ hgj, wv_gate C x2 j _ hgj]
                congr 1
                apply List.map_congr_left
                intro a ha
                by_cases halt : a < n + j
                · simp only [halt, ite_true]
                  have hap : a ≠ p.val := by
                    intro e; subst e
                    rcases hu_src with hu_eq | ⟨hu, _, hu_eq, hghu⟩
                    · exact hjt (huniq_in p j t _ gt hgj hgt ha (by rw [hgt_in, ← hu_eq]; simp))
                    · have hjeq := huniq_in p j hu _ _ hgj hghu ha (by simp)
                      exact hwu (by omega)
                  have haq : a ≠ q.val := by
                    intro e; subst e
                    rcases hv_src with hv_eq | ⟨hv, _, hv_eq, hghv⟩
                    · exact hjt (huniq_in q j t _ gt hgj hgt ha (by rw [hgt_in, ← hv_eq]; simp))
                    · have hjeq := huniq_in q j hv _ _ hgj hghv ha (by simp)
                      exact hwv (by omega)
                  have hau : a ≠ u := by
                    intro e; subst e
                    rcases hu_src with hu_eq | ⟨hu, _, hu_eq, hghu⟩
                    · exact hap hu_eq
                    · exact hjt (huniq_not p hu j t _ gt hghu hgj hgt (by rwa [← hu_eq]) (by rw [hgt_in, ← hu_eq]; simp))
                  have hav : a ≠ v := by
                    intro e; subst e
                    rcases hv_src with hv_eq | ⟨hv, _, hv_eq, hghv⟩
                    · exact haq hv_eq
                    · exact hjt (huniq_not q hv j t _ gt hghv hgj hgt (by rwa [← hv_eq]) (by rw [hgt_in, ← hv_eq]; simp))
                  exact ih a (by omega) hap haq hau hav
                · simp only [halt, ite_false]
            · rw [wv_beyond C x1 w (by omega), wv_beyond C x2 w (by omega)]
      have ho_p : C.output ≠ p.val := fun e => not_literal_of_restrNC f hdep hrnc p false (fun x => by
        rw [← hfun x]; show wv C x C.output = xor (x p) false; rw [e, wv_input]; simp)
      have ho_q : C.output ≠ q.val := fun e => not_literal_of_restrNC f hdep hrnc q false (fun x => by
        rw [← hfun x]; show wv C x C.output = xor (x q) false; rw [e, wv_input]; simp)
      have ho_u : C.output ≠ u := fun e => not_literal_of_restrNC f hdep hrnc p cu (fun x => by
        rw [← hfun x]; show wv C x C.output = xor (x p) cu; rw [e, hup])
      have ho_v : C.output ≠ v := fun e => not_literal_of_restrNC f hdep hrnc q cv (fun x => by
        rw [← hfun x]; show wv C x C.output = xor (x q) cv; rw [e, hvq])
      -- Build the funnel witness (a, b).
      let a : Bool := match gt.op with | GateOp.and => !cu | _ => cu
      let b : Bool := match gt.op with | GateOp.and => !cv | _ => cv
      apply hnf p q hpq hdp hdq
      refine ⟨a, b, fun x => ?_⟩
      have hgt_eval : ∀ z : Fin n → Bool, wv C z (n + t) =
          match gt.op with
          | GateOp.and => xor (z p) cu && xor (z q) cv
          | _ => xor (z p) cu || xor (z q) cv := by
        intro z
        rw [wv_gate C z t gt hgt, hgt_in]
        rcases hgt_op with h | h <;> simp [h, hult, hvlt, hup, hvq, GateOp.eval]
      have h1_agree : ∀ i : Fin n, i ≠ p → i ≠ q →
          Function.update (Function.update x p (!a)) q b i =
            Function.update (Function.update x p a) q (!b) i := by
        intro i hip hiq; simp [Function.update_of_ne hiq, Function.update_of_ne hip]
      have h2_agree : ∀ i : Fin n, i ≠ p → i ≠ q →
          Function.update (Function.update x p a) q (!b) i =
            Function.update (Function.update x p (!a)) q (!b) i := by
        intro i hip hiq; simp [Function.update_of_ne hiq, Function.update_of_ne hip]
      have h1_t : wv C (Function.update (Function.update x p (!a)) q b) (n + t) =
          wv C (Function.update (Function.update x p a) q (!b)) (n + t) := by
        rw [hgt_eval, hgt_eval]
        simp only [Function.update_of_ne hpq, Function.update_self]
        rcases hgt_op with h | h <;> simp [a, b, h] <;> cases cu <;> cases cv <;> decide
      have h2_t : wv C (Function.update (Function.update x p a) q (!b)) (n + t) =
          wv C (Function.update (Function.update x p (!a)) q (!b)) (n + t) := by
        rw [hgt_eval, hgt_eval]
        simp only [Function.update_of_ne hpq, Function.update_self]
        rcases hgt_op with h | h <;> simp [a, b, h] <;> cases cu <;> cases cv <;> decide
      exact ⟨(hfun _).symm.trans ((hisol _ _ h1_agree h1_t C.output ho_p ho_q ho_u ho_v).trans (hfun _)),
             (hfun _).symm.trans ((hisol _ _ h2_agree h2_t C.output ho_p ho_q ho_u ho_v).trans (hfun _))⟩

-- Reindexing inputs: if f agrees with g along e : Fin m -> Fin n, HasCircuitSize n f s -> HasCircuitSize m g s.
theorem reindex_circuit {n m : ℕ} (f : (Fin n → Bool) → Bool) (g : (Fin m → Bool) → Bool)
    (e : Fin n → Option (Fin m)) (s : ℕ)
    (hfg : ∀ y : Fin m → Bool, g y = f (fun i => match e i with | some j => y j | none => false))
    (hC : HasCircuitSize n f s)
    (hnc : ∃ x y : Fin m → Bool, g x ≠ g y) :
    HasCircuitSize m g s := by
  obtain ⟨C, hfan, hsz, hfun⟩ := hC
  let init : List Stat := (List.finRange n).map fun i =>
    match e i with
    | some j => Sum.inr j.val
    | none => Sum.inl false
  let acc := elim m C.gates (init, [])
  have hinv : ∀ y : Fin m → Bool,
      Inv m (List.ofFn y) (wiresFrom C.gates (List.ofFn (fun i => match e i with | some j => y j | none => false))) acc := by
    intro y
    apply inv_elim m (List.ofFn y) List.length_ofFn C.gates _ _ hfan
    refine ⟨by simp [init], ?_⟩
    intro i
    by_cases hi : i < n
    · have hget : init.getD i (Sum.inl false) = match e ⟨i, hi⟩ with | some j => Sum.inr j.val | none => Sum.inl false := by
        rw [List.getD_eq_getElem _ _ (by simp [init, hi])]
        simp [init, hi]
      rw [hget]
      cases he : e ⟨i, hi⟩ with
      | none =>
        simp only [Stat.Valid, Stat.val, true_and]
        rw [List.getD_eq_getElem _ _ (by simp [hi])]
        simp [he]
      | some j =>
        simp only [Stat.Valid, Stat.val, wiresFrom, List.foldl_nil, List.length_nil, Nat.add_zero]
        refine ⟨j.isLt, ?_⟩
        rw [List.getD_eq_getElem _ _ (by simp [j.isLt]), List.getD_eq_getElem _ _ (by simp [hi])]
        simp [he]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hstep_le : ∀ (gs : List Gate) (a : List Stat × List Gate),
      (elim m gs a).2.length ≤ a.2.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro a; simp [elim]
    | cons g' gs' ih =>
      intro a
      rw [elim_cons]
      have h1 := ih (elimStep m a g')
      have h2 : (elimStep m a g').2.length ≤ a.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g'.op (m + a.2.length)
          (g'.inputs.map fun i => a.1.getD i (Sum.inl false))).1
        omega
      simp only [List.length_cons]
      omega
  have hsz_acc : acc.2.length ≤ s := by
    have h1 : acc.2.length ≤ ([] : List Gate).length + C.gates.length := hstep_le C.gates (init, [])
    simp only [List.length_nil, Nat.zero_add] at h1
    change C.gates.length ≤ s at hsz
    omega
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inr k =>
    refine ⟨⟨acc.2, k⟩, elim_ok m C.gates _ (by simp), hsz_acc, ?_⟩
    intro y
    have hv := ((hinv y).2 C.output).2
    rw [ho] at hv
    have hf := hfun (fun i => match e i with | some j => y j | none => false)
    exact hv.trans (hf.trans (hfg y).symm)
  | inl c =>
    obtain ⟨x, y, hxy⟩ := hnc
    have hx := (((hinv x).2 C.output).2).trans ((hfun _).trans (hfg x).symm)
    have hy := (((hinv y).2 C.output).2).trans ((hfun _).trans (hfg y).symm)
    rw [ho] at hx hy
    exact absurd (hx.symm.trans hy) hxy

-- A function that is neither constant nor a single-input projection requires at least 1 gate.
theorem size_ge_one {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hC : HasCircuitSize n f s)
    (hnc : ∃ x y, f x ≠ f y)
    (hnproj : ∀ i : Fin n, ∃ x, f x ≠ x i) : 1 ≤ s := by
  by_contra hlt
  have hs0 : s = 0 := by omega
  subst hs0
  obtain ⟨C, _, hsz, hfun⟩ := hC
  have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hsz)
  by_cases ho : C.output < n
  · obtain ⟨x, hx⟩ := hnproj ⟨C.output, ho⟩
    have he := hfun x
    simp only [Circuit.eval, Circuit.wires, hnil, List.foldl_nil] at he
    rw [List.getD_eq_getElem _ _ (by simp [ho])] at he
    simp at he
    exact hx he.symm
  · obtain ⟨x, y, hxy⟩ := hnc
    have hx := hfun x
    have hy := hfun y
    simp only [Circuit.eval, Circuit.wires, hnil, List.foldl_nil] at hx hy
    rw [List.getD_eq_default _ _ (by simp; omega)] at hx hy
    exact hxy (hx.symm.trans hy)

-- A function depending on 3 distinct inputs requires at least 2 FanInTwo gates.
theorem size_ge_two_of_three_dep {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hC : HasCircuitSize n f s) (p1 p2 p3 : Fin n) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (hd1 : Dep f p1) (hd2 : Dep f p2) (hd3 : Dep f p3) : 2 ≤ s := by
  obtain ⟨C, hfan, _, hsz, hfun, _⟩ := exists_least_circuit f s hC
  by_contra hlt
  change C.gates.length ≤ s at hsz
  have hlen : C.gates.length ≤ 1 := by omega
  rcases hgs : C.gates with _ | ⟨g, gs⟩
  · -- 0 gates: depends on at most 1 input.
    have hnot : ∀ i : Fin n, i.val ≠ C.output → ¬ Dep f i := by
      intro i hi ⟨x, hx⟩
      have h1 : f (Function.update x i (!x i)) = wv C (Function.update x i (!x i)) C.output := (hfun _).symm
      have h2 : f x = wv C x C.output := (hfun _).symm
      by_cases ho : C.output < n
      · rw [h1, h2, wv_input C _ ⟨C.output, ho⟩, wv_input C _ ⟨C.output, ho⟩] at hx
        rw [Function.update_of_ne (show (⟨C.output, ho⟩ : Fin n) ≠ i from fun e => hi (congrArg Fin.val e).symm)] at hx
        exact hx rfl
      · rw [h1, h2, wv_beyond C _ C.output (by rw [hgs]; simp; omega),
            wv_beyond C _ C.output (by rw [hgs]; simp; omega)] at hx
        exact hx rfl
    by_cases h1 : p1.val = C.output
    · exact hnot p2 (by intro e; exact h12 (Fin.ext (h1.trans e.symm))) hd2
    · exact hnot p1 h1 hd1
  · have hnil : gs = [] := by rw [hgs] at hlen; simpa using hlen
    subst hnil
    have hgin : g.inputs.length ≤ 2 := (hfan g (by rw [hgs]; simp)).2
    -- Any input i with i.val ≠ C.output and i.val ∉ g.inputs cannot be sensitive.
    have hnot : ∀ i : Fin n, i.val ≠ C.output → i.val ∉ g.inputs → ¬ Dep f i := by
      intro i hi hgi ⟨x, hx⟩
      have h1 : f (Function.update x i (!x i)) = wv C (Function.update x i (!x i)) C.output := (hfun _).symm
      have h2 : f x = wv C x C.output := (hfun _).symm
      by_cases ho : C.output < n
      · rw [h1, h2, wv_input C _ ⟨C.output, ho⟩, wv_input C _ ⟨C.output, ho⟩] at hx
        rw [Function.update_of_ne (show (⟨C.output, ho⟩ : Fin n) ≠ i from fun e => hi (congrArg Fin.val e).symm)] at hx
        exact hx rfl
      · by_cases ho2 : C.output = n
        · have hg0 : C.gates[0]? = some g := by rw [hgs]; rfl
          have hEq : C.output = n + 0 := by omega
          rw [h1, h2, hEq, wv_gate C _ 0 g hg0, wv_gate C _ 0 g hg0] at hx
          apply hx
          congr 1
          apply List.map_congr_left
          intro a ha
          by_cases han : a < n + 0
          · simp only [han, ite_true]
            rw [wv_input C _ ⟨a, by omega⟩, wv_input C _ ⟨a, by omega⟩]
            exact Function.update_of_ne (show (⟨a, by omega⟩ : Fin n) ≠ i from fun e => hgi (congrArg Fin.val e ▸ ha)) _ _
          · simp only [han, ite_false]
        · rw [h1, h2, wv_beyond C _ C.output (by rw [hgs]; simp; omega),
              wv_beyond C _ C.output (by rw [hgs]; simp; omega)] at hx
          exact hx rfl
    -- Case split on whether C.output < n (if so, depends on at most 1 input) or C.output >= n (only g.inputs matter, <= 2).
    by_cases ho : C.output < n
    · have hnot' : ∀ i : Fin n, i.val ≠ C.output → ¬ Dep f i := by
        intro i hi ⟨x, hx⟩
        have h1 : f (Function.update x i (!x i)) = wv C (Function.update x i (!x i)) C.output := (hfun _).symm
        have h2 : f x = wv C x C.output := (hfun _).symm
        rw [h1, h2, wv_input C _ ⟨C.output, ho⟩, wv_input C _ ⟨C.output, ho⟩] at hx
        rw [Function.update_of_ne (show (⟨C.output, ho⟩ : Fin n) ≠ i from fun e => hi (congrArg Fin.val e).symm)] at hx
        exact hx rfl
      by_cases h1 : p1.val = C.output
      · exact hnot' p2 (by intro e; exact h12 (Fin.ext (h1.trans e.symm))) hd2
      · exact hnot' p1 h1 hd1
    · have hm1 : p1.val ∈ g.inputs := by
        by_contra h; exact hnot p1 (by have := p1.isLt; omega) h hd1
      have hm2 : p2.val ∈ g.inputs := by
        by_contra h; exact hnot p2 (by have := p2.isLt; omega) h hd2
      have hm3 : p3.val ∈ g.inputs := by
        by_contra h; exact hnot p3 (by have := p3.isLt; omega) h hd3
      rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · simp [hins] at hm1
      · simp [hins] at hm1 hm2; exact h12 (Fin.ext (hm1.trans hm2.symm))
      · simp [hins] at hm1 hm2 hm3
        rcases hm1 with rfl | rfl <;> rcases hm2 with h2 | h2 <;> rcases hm3 with h3 | h3
        · exact h12 (Fin.ext h2.symm)
        · exact h12 (Fin.ext h2.symm)
        · exact h13 (Fin.ext h3.symm)
        · exact h23 (Fin.ext (h2.trans h3.symm))
        · exact h23 (Fin.ext (h2.trans h3.symm))
        · exact h13 (Fin.ext h3.symm)
        · exact h12 (Fin.ext h2.symm)
        · exact h12 (Fin.ext h2.symm)
      · simp [hins] at hgin

-- Concrete small graph edge functions and their exact lower bounds.
def fP3 (x : Fin 3 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2)
def fP4 (x : Fin 4 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)
def fP5 (x : Fin 5 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)
def fIso2P3 (x : Fin 5 → Bool) : Bool := x 0 || x 1 || (x 2 && x 3) || (x 3 && x 4)
def fC6 (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0)
def fIso2C6 (x : Fin 8 → Bool) : Bool :=
  x 0 || x 3 || (x 1 && x 2) || (x 2 && x 6) || (x 6 && x 4) || (x 4 && x 7) || (x 7 && x 5) || (x 5 && x 1)

theorem fP3_lb (s : ℕ) (h : HasCircuitSize 3 fP3 s) : 2 ≤ s :=
  size_ge_two_of_three_dep fP3 s h 0 1 2 (by decide) (by decide) (by decide)
    ⟨fun i => decide (i = 1), by decide⟩
    ⟨fun i => decide (i = 0), by decide⟩
    ⟨fun i => decide (i = 1), by decide⟩

theorem fIso2P3_lb (s : ℕ) (h : HasCircuitSize 5 fIso2P3 s) : 4 ≤ s := by
  have h1 := elim_one_var fIso2P3 0 false s h
    ⟨fun _ => false, by decide⟩
    ⟨fun _ => false, fun i => decide (i = 1), by decide⟩
  have h2 := elim_one_var (fun x => fIso2P3 (Function.update x 0 false)) 1 false (s - 1) h1
    ⟨fun _ => false, by decide⟩
    ⟨fun _ => false, fun i => decide (i = 2 ∨ i = 3), by decide⟩
  have h3 : HasCircuitSize 3 fP3 (s - 1 - 1) :=
    reindex_circuit _ fP3 (fun i => match i.val with
      | 2 => some 0 | 3 => some 1 | 4 => some 2 | _ => none) (s - 1 - 1)
      (by intro y; simp [fP3, fIso2P3, Function.update])
      h2 ⟨fun _ => false, fun _ => true, by decide⟩
  have hlb := fP3_lb (s - 1 - 1) h3
  omega

theorem fP4_lb (s : ℕ) (h : HasCircuitSize 4 fP4 s) : 4 ≤ s := by
  have hdep : ∃ p : Fin 4, Dep fP4 p := ⟨0, fun i => decide (i = 1), by decide⟩
  have hrnc : RestrNC fP4 := by
    intro p _ b
    fin_cases p <;> cases b
    · exact ⟨fun _ => false, fun i => decide (i = 1 ∨ i = 2), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 1), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 2 ∨ i = 3), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 0), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 3), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 2), by decide⟩
  have hnf : NoFunnel fP4 := by
    intro p q hpq _ _ ⟨a, b, hab⟩
    have hfin : ∀ p q : Fin 4, p ≠ q → ∀ a b : Bool,
        ∃ x : Fin 4 → Bool, ¬ (fP4 (Function.update (Function.update x p (!a)) q b) =
          fP4 (Function.update (Function.update x p a) q (!b)) ∧
          fP4 (Function.update (Function.update x p a) q (!b)) =
          fP4 (Function.update (Function.update x p (!a)) q (!b))) := by
      decide
    obtain ⟨x, hx⟩ := hfin p q hpq a b
    exact hx (hab x)
  rcases fanout_step_3_4 fP4 s hdep hrnc hnf h with ⟨y, s', hs', hC'⟩ | ⟨y, s', hs', _⟩
  · have hge1 : 1 ≤ s' := size_ge_one _ s' hC'
      (by
        fin_cases y
        · exact ⟨fun _ => false, fun i => decide (i = 1 ∨ i = 2), by decide⟩
        · exact ⟨fun _ => false, fun i => decide (i = 2 ∨ i = 3), by decide⟩
        · exact ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), by decide⟩
        · exact ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), by decide⟩)
      (by
        intro i
        have hfin : ∀ y i : Fin 4, ∃ x : Fin 4 → Bool, fP4 (Function.update x y false) ≠ x i := by decide
        exact hfin y i)
    omega
  · omega

theorem fP5_lb (s : ℕ) (h : HasCircuitSize 5 fP5 s) : 5 ≤ s := by
  have h1 := elim_one_var fP5 0 false s h
    ⟨fun i => decide (i = 1), by decide⟩
    ⟨fun _ => false, fun i => decide (i = 1 ∨ i = 2), by decide⟩
  have h2 : HasCircuitSize 4 fP4 (s - 1) :=
    reindex_circuit _ fP4 (fun i => match i.val with
      | 1 => some 0 | 2 => some 1 | 3 => some 2 | 4 => some 3 | _ => none) (s - 1)
      (by intro y; simp [fP4, fP5, Function.update])
      h1 ⟨fun _ => false, fun _ => true, by decide⟩
  have hlb := fP4_lb (s - 1) h2
  omega

def mapC6F (y i : Fin 6) : Option (Fin 5) :=
  match (i.val + 6 - y.val) % 6 with
  | 1 => some 0 | 2 => some 1 | 3 => some 2 | 4 => some 3 | 5 => some 4 | _ => none

def mapC6T (y i : Fin 6) : Option (Fin 5) :=
  match (i.val + 6 - y.val) % 6 with
  | 1 => some 0 | 5 => some 1 | 2 => some 2 | 3 => some 3 | 4 => some 4 | _ => none

theorem fC6_lb (s : ℕ) (h : HasCircuitSize 6 fC6 s) : 8 ≤ s := by
  have hdep : ∃ p : Fin 6, Dep fC6 p := ⟨0, fun i => decide (i = 1), by decide⟩
  have hrnc : RestrNC fC6 := by
    intro p _ b
    fin_cases p <;> cases b
    · exact ⟨fun _ => false, fun i => decide (i = 1 ∨ i = 2), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 1), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 2 ∨ i = 3), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 2), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 3 ∨ i = 4), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 3), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 4 ∨ i = 5), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 4), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 5), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), by decide⟩
    · exact ⟨fun _ => false, fun i => decide (i = 0), by decide⟩
  have hnf : NoFunnel fC6 := by
    intro p q hpq _ _ ⟨a, b, hab⟩
    have hfin : ∀ p q : Fin 6, p ≠ q → ∀ a b : Bool,
        ∃ x : Fin 6 → Bool, ¬ (fC6 (Function.update (Function.update x p (!a)) q b) =
          fC6 (Function.update (Function.update x p a) q (!b)) ∧
          fC6 (Function.update (Function.update x p a) q (!b)) =
          fC6 (Function.update (Function.update x p (!a)) q (!b))) := by
      decide
    obtain ⟨x, hx⟩ := hfin p q hpq a b
    exact hx (hab x)
  rcases fanout_step_3_4 fC6 s hdep hrnc hnf h with ⟨y, s', hs', hC'⟩ | ⟨y, s', hs', hC'⟩
  · -- Fixing y := false on C6 yields P5 (cyclic shift).
    have hP5 : HasCircuitSize 5 fP5 s' :=
      reindex_circuit _ fP5 (mapC6F y) s'
        (by
          intro z
          revert z
          clear hC' hs' h hdep hrnc hnf s s'
          revert y
          decide)
        hC' ⟨fun _ => false, fun _ => true, by decide⟩
    have := fP5_lb s' hP5
    omega
  · -- Fixing y := true on C6 yields fIso2P3 (two neighbors isolated + P3 on remaining 3).
    have hI2 : HasCircuitSize 5 fIso2P3 s' :=
      reindex_circuit _ fIso2P3 (mapC6T y) s'
        (by
          intro z
          revert z
          clear hC' hs' h hdep hrnc hnf s s'
          revert y
          decide)
        hC' ⟨fun _ => false, fun _ => true, by decide⟩
    have := fIso2P3_lb s' hI2
    omega

theorem fIso2C6_lb (s : ℕ) (h : HasCircuitSize 8 fIso2C6 s) : 10 ≤ s := by
  have h1 := elim_one_var fIso2C6 0 false s h
    ⟨fun _ => false, by decide⟩
    ⟨fun _ => false, fun i => decide (i = 3), by decide⟩
  have h2 := elim_one_var (fun x => fIso2C6 (Function.update x 0 false)) 3 false (s - 1) h1
    ⟨fun _ => false, by decide⟩
    ⟨fun _ => false, fun i => decide (i = 1 ∨ i = 2), by decide⟩
  have h3 : HasCircuitSize 6 fC6 (s - 1 - 1) :=
    reindex_circuit _ fC6 (fun i => match i.val with
      | 1 => some 0 | 2 => some 1 | 6 => some 2 | 4 => some 3 | 7 => some 4 | 5 => some 5 | _ => none)
      (s - 1 - 1) (by decide) h2 ⟨fun _ => false, fun _ => true, by decide⟩
  have := fC6_lb (s - 1 - 1) h3
  omega

end PEqualNP.Outside.L_meta_3059

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3059

theorem PEqualNP.Outside.L_meta_3059 : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Bool), PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.FanInTwo x3 → (∀ (x7 : Fin (8 : ℕ) → Bool), x3.eval (x2.wires (List.ofFn x7) ++ [x4]) = (x1 x7 || x7 (0 : Fin (8 : ℕ)) || x7 (3 : Fin (8 : ℕ)))) → (10 : ℕ) + List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (if x8.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x8.inputs else x8.inputs).contains ((8 : ℕ) + x2.size)) x3.gates ≤ x2.size + x3.size := by
  intro x1 x2 x3 x4 hfan2 hfan3 heval
  have heq_f : ∀ y : Fin 8 → Bool, (x1 y || y 0 || y 3) = fIso2C6 y := by
    intro y
    dsimp only [x1, fIso2C6]
    cases y 0 <;> cases y 3
    · simp only [Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false]
      cases y 1 <;> cases y 2 <;> cases y 4 <;> cases y 5 <;> cases y 6 <;> cases y 7 <;> rfl
    · simp
    · simp
    · simp
  let reader : Gate → Bool := fun g =>
    (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).contains (8 + x2.size)
  let gs3 := x3.gates.map normGate
  let acc0 : List Stat × List Gate := ((List.range (8 + x2.size)).map Sum.inr ++ [Sum.inl x4], x2.gates)
  let acc := elim 8 gs3 acc0
  let S := Finset.univ.filter (fun i : Fin x3.gates.length => reader (x3.gates.get i))
  have cardS : x3.gates.countP reader = S.card := by
    have h := List.countP_ofFn (fun i : Fin x3.gates.length => x3.gates.get i) reader
    simpa [S] using h
  have normOk3 : ∀ g ∈ gs3, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok _ (hfan3 _ hg0)
  have active : ∀ (g : Gate), Ok g → reader g = true → (8 + x2.size) ∈ (normGate g).inputs := by
    intro g hok hr
    obtain ⟨op, xs⟩ := g
    obtain ⟨hop, _⟩ := hok
    change op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not at hop
    rcases hop with rfl | rfl | rfl <;> simpa [reader, normGate, GateOp.eval] using hr
  have hcount := elim_count 8 acc0 gs3 normOk3 (S.image Fin.val) (by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have hr := (Finset.mem_filter.mp hi).2
    refine ⟨normGate (x3.gates.get i), ?_, 8 + x2.size, active _ (hfan3 _ (List.get_mem _ _)) hr, ?_, x4, ?_⟩
    · simp [gs3, i.isLt]
    · simp [acc0]; omega
    · rw [elim_getD 8 (8 + x2.size) (Sum.inl false) gs3 acc0 (by simp [acc0])]
      show ((List.range (8 + x2.size)).map (Sum.inr : ℕ → Stat) ++ [Sum.inl x4]).getD (8 + x2.size) (Sum.inl false) = Sum.inl x4
      have hrl : ((List.range (8 + x2.size)).map (Sum.inr : ℕ → Stat)).length = 8 + x2.size := by simp
      have hsn := getD_snoc_eq ((List.range (8 + x2.size)).map (Sum.inr : ℕ → Stat)) (Sum.inl x4) (Sum.inl false)
      rwa [hrl] at hsn)
  have hnum : acc.2.length + S.card ≤ x2.size + x3.size := by
    simpa [acc, acc0, gs3, Circuit.size, Finset.card_image_of_injective S Fin.val_injective] using hcount
  have hinv : ∀ y : Fin 8 → Bool,
      Inv 8 (List.ofFn y) (wiresFrom gs3 (x2.wires (List.ofFn y) ++ [x4])) acc := by
    intro y
    apply inv_elim 8 (List.ofFn y) List.length_ofFn gs3 _ acc0 (fun g hg => (normOk3 g hg).1)
    have hw2len : (x2.wires (List.ofFn y)).length = 8 + x2.size := by
      show (wiresFrom x2.gates (List.ofFn y)).length = 8 + x2.gates.length
      rw [length_wiresFrom, List.length_ofFn]
    refine ⟨by simp only [acc0, List.length_append, List.length_map, List.length_range, List.length_singleton, hw2len], ?_⟩
    intro i
    by_cases hi : i < 8 + x2.size
    · have hget : acc0.1.getD i (Sum.inl false) = Sum.inr i := by
        show ((List.range (8 + x2.size)).map Sum.inr ++ [Sum.inl x4]).getD i (Sum.inl false) = Sum.inr i
        rw [List.getD_append _ _ _ _ (by simp; omega)]
        rw [List.getD_eq_getElem _ _ (by simp; omega)]
        simp
      rw [hget]
      refine ⟨by simpa [acc0, Stat.Valid, Circuit.size] using hi, ?_⟩
      simp only [acc0, Stat.val]
      rw [List.getD_append _ _ _ _ (by rw [hw2len]; omega)]
      rfl
    · by_cases hi2 : i = 8 + x2.size
      · subst hi2
        have hget : acc0.1.getD (8 + x2.size) (Sum.inl false) = Sum.inl x4 := by
          show ((List.range (8 + x2.size)).map (Sum.inr : ℕ → Stat) ++ [Sum.inl x4]).getD (8 + x2.size) (Sum.inl false) = Sum.inl x4
          have hrl : ((List.range (8 + x2.size)).map (Sum.inr : ℕ → Stat)).length = 8 + x2.size := by simp
          have hsn := getD_snoc_eq ((List.range (8 + x2.size)).map (Sum.inr : ℕ → Stat)) (Sum.inl x4) (Sum.inl false)
          rwa [hrl] at hsn
        rw [hget]
        refine ⟨trivial, ?_⟩
        simp only [Stat.val]
        rw [← hw2len, getD_snoc_eq]
      · rw [List.getD_eq_default _ _ (by simp [acc0]; omega)]
        rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton, hw2len]; omega)]
        exact ⟨trivial, rfl⟩
  have hval : ∀ y : Fin 8 → Bool,
      (acc.1.getD x3.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) = fIso2C6 y := by
    intro y
    have hv := ((hinv y).2 x3.output).2
    rw [show gs3 = x3.gates.map normGate from rfl, wiresFrom_norm] at hv
    exact hv.trans ((heval y).trans (heq_f y))
  cases ho : acc.1.getD x3.output (Sum.inl false) with
  | inr k =>
    have hD : HasCircuitSize 8 fIso2C6 acc.2.length := by
      refine ⟨⟨acc.2, k⟩, elim_ok 8 gs3 acc0 hfan2, le_refl _, ?_⟩
      intro y
      have hv := hval y
      rw [ho] at hv
      exact hv
    have hlb := fIso2C6_lb acc.2.length hD
    change 10 + x3.gates.countP reader ≤ x2.size + x3.size
    rw [cardS]
    omega
  | inl b =>
    have h0 := hval (fun _ => false)
    have h1 := hval (fun _ => true)
    rw [ho] at h0 h1
    have hdiff : fIso2C6 (fun _ => false) ≠ fIso2C6 (fun _ => true) := by decide
    exact absurd (h0.symm.trans h1) hdiff

