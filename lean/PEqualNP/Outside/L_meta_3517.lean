import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_3517

def phi (i : ℕ) : ℕ :=
  if i < 10 then ([0, 1, 2, 3, 5, 6, 7, 8, 9, 12] : List ℕ).getD i 0 else i + 4

def rl (g : Gate) : Gate := ⟨g.op, g.inputs.map phi⟩

def extra (B : ℕ) : List Gate :=
  [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [B, 5]⟩, ⟨GateOp.and, [10, B + 1]⟩,
   ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [B + 3, 6]⟩, ⟨GateOp.and, [11, B + 4]⟩,
   ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [B + 6, 4]⟩, ⟨GateOp.and, [13, B + 7]⟩,
   ⟨GateOp.or, [B + 2, B + 5]⟩, ⟨GateOp.or, [B + 9, B + 8]⟩]

def build (C : Circuit) : Circuit :=
  if C.output < 10 + C.gates.length then
    ⟨C.gates.map rl ++ extra (14 + C.gates.length) ++
      [⟨GateOp.or, [phi C.output, 14 + C.gates.length + 10]⟩], 14 + C.gates.length + 11⟩
  else ⟨C.gates.map rl ++ extra (14 + C.gates.length), 14 + C.gates.length + 10⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl, ih, step]; omega

theorem fold_pre (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl step w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl]
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hk

theorem phi_lt (i : ℕ) (hi : i < 10) : phi i < 14 := by
  unfold phi; rw [if_pos hi]; interval_cases i <;> simp

theorem phi_inj : Function.Injective phi := by
  intro a b h
  unfold phi at h
  by_cases ha : a < 10 <;> by_cases hb : b < 10
  · simp only [ha, hb, ite_true] at h
    interval_cases a <;> interval_cases b <;> simp_all
  · simp only [ha, hb, ite_true, ite_false] at h
    have := phi_lt a ha; unfold phi at this; simp only [ha, ite_true] at this; omega
  · simp only [ha, hb, ite_true, ite_false] at h
    have := phi_lt b hb; unfold phi at this; simp only [hb, ite_true] at this; omega
  · simp only [ha, hb, ite_false] at h; omega

def H (w1 w4 : List Bool) : Prop :=
  w4.length = w1.length + 4 ∧ 10 ≤ w1.length ∧ ∀ i, w4.getD (phi i) false = w1.getD i false

theorem H_step (w1 w4 : List Bool) (g : Gate) (h : H w1 w4) : H (step w1 g) (step w4 (rl g)) := by
  obtain ⟨hl, h10, hv⟩ := h
  have hval : (rl g).op.eval ((rl g).inputs.map fun i => w4.getD i false) =
      g.op.eval (g.inputs.map fun i => w1.getD i false) := by
    simp only [rl, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hv i
  refine ⟨by simp [step, hl], by simp [step]; omega, ?_⟩
  intro i
  simp only [step]
  rw [hval]
  rcases lt_trichotomy i w1.length with hi | hi | hi
  · have hp : phi i < w4.length := by
      by_cases h9 : i < 10
      · have := phi_lt i h9; omega
      · unfold phi; rw [if_neg h9]; omega
    rw [List.getD_append _ _ _ _ hp, List.getD_append _ _ _ _ hi]
    exact hv i
  · have hp : phi i = w4.length := by
      unfold phi; rw [if_neg (by omega)]; omega
    rw [hp, hi]
    simp
  · have hp : phi i = i + 4 := by unfold phi; rw [if_neg (by omega)]
    rw [hp, List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem H_fold (gs : List Gate) (w1 w4 : List Bool) (h : H w1 w4) :
    H (gs.foldl step w1) ((gs.map rl).foldl step w4) := by
  induction gs generalizing w1 w4 with
  | nil => exact h
  | cons g gs ih => exact ih _ _ (H_step w1 w4 g h)

def pos (i : Fin 10) : Fin 14 :=
  ([(0 : Fin 14), 1, 2, 3, 5, 6, 7, 8, 9, 12] : List (Fin 14)).getD i 0

theorem H_init (X : Fin 14 → Bool) :
    H (List.ofFn fun i : Fin 10 => X (pos i)) (List.ofFn X) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  by_cases h9 : i < 10
  · have hp := phi_lt i h9
    rw [List.getD_eq_getElem _ _ (by simpa using hp), List.getD_eq_getElem _ _ (by simpa using h9),
      List.getElem_ofFn, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    interval_cases i <;> rfl
  · unfold phi; rw [if_neg h9]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def star (X : Fin 14 → Bool) : Bool :=
  (X 10 && ((X 0 || X 4) || X 5) || X 11 && ((X 3 || X 4) || X 6)) || X 13 && ((X 1 || X 2) || X 4)

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem step_lt (w : List Bool) (g : Gate) (k : ℕ) (h : k < w.length) :
    (step w g).getD k false = w.getD k false :=
  List.getD_append _ _ _ _ h

theorem step_eq (w : List Bool) (g : Gate) (k : ℕ) (h : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst h; simp [step]

theorem extra_fold (W : List Bool) (X : Fin 14 → Bool) (hlen : 14 ≤ W.length)
    (hin : ∀ k : Fin 14, W.getD k false = X k) :
    ((extra W.length).foldl step W).getD (W.length + 10) false = star X := by
  have h0 : W.getD 0 false = X 0 := hin 0
  have h1 : W.getD 1 false = X 1 := hin 1
  have h2 : W.getD 2 false = X 2 := hin 2
  have h3 : W.getD 3 false = X 3 := hin 3
  have h4 : W.getD 4 false = X 4 := hin 4
  have h5 : W.getD 5 false = X 5 := hin 5
  have h6 : W.getD 6 false = X 6 := hin 6
  have h10 : W.getD 10 false = X 10 := hin 10
  have h11 : W.getD 11 false = X 11 := hin 11
  have h13 : W.getD 13 false = X 13 := hin 13
  simp only [extra, List.foldl]
  simp (disch := (first | omega | (simp only [step_len]; omega) | (simp only [step_len]; done) | (rw [step_len]; omega))) only [step_lt, step_eq, List.map_cons,
    List.map_nil, h0, h1, h2, h3, h4, h5, h6, h10, h11, h13]
  simp [star, GateOp.eval]

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem star_eq (X : Fin 14 → Bool) : star X = decide (∃ (a : Fin 14) (b : Fin 14),
    ((a : ℕ), (b : ℕ)) ∈ ([(0, 10), (1, 13), (2, 13), (3, 11), (4, 10), (4, 11), (4, 13), (5, 10),
      (6, 11)] : List (ℕ × ℕ)) ∧ X a = true ∧ X b = true) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  constructor
  · intro h
    simp only [star, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ((⟨h1, (h2 | h2) | h2⟩ | ⟨h1, (h2 | h2) | h2⟩) | ⟨h1, (h2 | h2) | h2⟩)
    · exact ⟨0, 10, by simp, h2, h1⟩
    · exact ⟨4, 10, by simp, h2, h1⟩
    · exact ⟨5, 10, by simp, h2, h1⟩
    · exact ⟨3, 11, by simp, h2, h1⟩
    · exact ⟨4, 11, by simp, h2, h1⟩
    · exact ⟨6, 11, by simp, h2, h1⟩
    · exact ⟨1, 13, by simp, h2, h1⟩
    · exact ⟨2, 13, by simp, h2, h1⟩
    · exact ⟨4, 13, by simp, h2, h1⟩
  · rintro ⟨a, b, hm, ha, hb⟩
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases a with ⟨a, _⟩; rcases b with ⟨b, _⟩
      simp only at h1 h2; subst h1; subst h2
      have hx : X 0 = true := ha
      have hy : X 10 = true := hb
      simp [star, hx, hy]
    · rcases a with ⟨a, _⟩; rcases b with ⟨b, _⟩
      simp only at h1 h2; subst h1; subst h2
      have hx : X 1 = true := ha
      have hy : X 13 = true := hb
      simp [star, hx, hy]
    · rcases a with ⟨a, _⟩; rcases b with ⟨b, _⟩
      simp only at h1 h2; subst h1; subst h2
      have hx : X 2 = true := ha
      have hy : X 13 = true := hb
      simp [star, hx, hy]
    · rcases a with ⟨a, _⟩; rcases b with ⟨b, _⟩
      simp only at h1 h2; subst h1; subst h2
      have hx : X 3 = true := ha
      have hy : X 11 = true := hb
      simp [star, hx, hy]
    · rcases a with ⟨a, _⟩; rcases b with ⟨b, _⟩
      simp only at h1 h2; subst h1; subst h2
      have hx : X 4 = true := ha
      have hy : X 10 = true := hb
      simp [star, hx, hy]
    · rcases a with ⟨a, _⟩; rcases b with ⟨b, _⟩
      simp only at h1 h2; subst h1; subst h2
      have hx : X 4 = true := ha
      have hy : X 11 = true := hb
      simp [star, hx, hy]
    · rcases a with ⟨a, _⟩; rcases b with ⟨b, _⟩
      simp only at h1 h2; subst h1; subst h2
      have hx : X 4 = true := ha
      have hy : X 13 = true := hb
      simp [star, hx, hy]
    · rcases a with ⟨a, _⟩; rcases b with ⟨b, _⟩
      simp only at h1 h2; subst h1; subst h2
      have hx : X 5 = true := ha
      have hy : X 10 = true := hb
      simp [star, hx, hy]
    · rcases a with ⟨a, _⟩; rcases b with ⟨b, _⟩
      simp only at h1 h2; subst h1; subst h2
      have hx : X 6 = true := ha
      have hy : X 11 = true := hb
      simp [star, hx, hy]

theorem phi_bound (i j : ℕ) (h : i < 10 + j) : phi i < 14 + j := by
  by_cases h9 : i < 10
  · have := phi_lt i h9; omega
  · unfold phi; rw [if_neg h9]; omega

def fin (C : Circuit) : Gate := ⟨GateOp.or, [phi C.output, 14 + C.gates.length + 10]⟩

def tail (C : Circuit) : List Gate :=
  extra (14 + C.gates.length) ++ (if C.output < 10 + C.gates.length then [fin C] else [])

theorem gates_build (C : Circuit) : (build C).gates = C.gates.map rl ++ tail C := by
  unfold build tail fin; split_ifs <;> simp

theorem mem_tail (C : Circuit) (g : Gate) (h : g ∈ tail C) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup := by
  have hb : C.output < 10 + C.gates.length → phi C.output < 14 + C.gates.length := fun ho =>
    phi_bound _ _ ho
  unfold tail fin at h
  split_ifs at h with ho
  · have := hb ho
    simp only [extra, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with (h | h | h | h | h | h | h | h | h | h | h) | h <;> subst h <;>
      simp <;> omega
  · simp only [extra, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.append_nil] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp <;> omega

theorem tail_reads (C : Circuit) (k : ℕ) (hk : k < (tail C).length) :
    ∀ i ∈ ((tail C).getD k ⟨GateOp.or, []⟩).inputs, i < 14 + (C.gates.length + k) := by
  have hb : C.output < 10 + C.gates.length → phi C.output < 14 + C.gates.length := fun ho =>
    phi_bound _ _ ho
  unfold tail fin at hk ⊢
  split_ifs at hk ⊢ with ho
  · have := hb ho
    simp [extra] at hk
    interval_cases k <;> simp [extra] <;> (try constructor) <;>
      first | omega | (simp only [Nat.add_eq, Nat.succ_eq_add_one, Nat.le_eq] at *; omega)
  · simp [extra] at hk
    interval_cases k <;> simp [extra] <;> (try constructor) <;>
      first | omega | (simp only [Nat.add_eq, Nat.succ_eq_add_one, Nat.le_eq] at *; omega)

theorem ao2_build (C : Circuit) (hC : IsAO2 10 C) : IsAO2 14 (build C) := by
  obtain ⟨hao, hrb, hl⟩ := hC
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rw [gates_build, List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      exact hao g0 hg0
    · exact (mem_tail C g hg).1
  · intro j hj i hi
    rw [gates_build] at hj
    simp only [gateAt, gates_build] at hi
    by_cases hjs : j < C.gates.length
    · rw [List.getD_append _ _ _ _ (by simpa using hjs)] at hi
      rw [List.getD_eq_getElem _ _ (by simpa using hjs), List.getElem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
      have := hrb j hjs i0 (by simp only [gateAt]; rw [List.getD_eq_getElem _ _ hjs]; exact hi0)
      exact phi_bound _ _ this
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)] at hi
      have hk := tail_reads C (j - C.gates.length) (by simp at hj ⊢; omega)
      simp only [List.length_map] at hi
      have := hk i hi
      omega
  · intro g hg
    rw [gates_build, List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      simp [rl, hl g0 hg0]
    · exact (mem_tail C g hg).2.1

theorem nodup_build (C : Circuit) (hC : ∀ g ∈ C.gates, g.inputs.Nodup) :
    ∀ g ∈ (build C).gates, g.inputs.Nodup := by
  intro g hg
  rw [gates_build, List.mem_append] at hg
  rcases hg with hg | hg
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact (hC g0 hg0).map phi_inj
  · exact (mem_tail C g hg).2.2

theorem size_build (C : Circuit) :
    2 ≤ (build C).size ∧ (build C).size ≤ C.size + 12 := by
  simp only [Circuit.size, gates_build, tail]
  split_ifs <;> simp [extra] <;> omega

theorem eval_build (C : Circuit) (X : Fin 14 → Bool) :
    (build C).eval (List.ofFn X) =
      (C.eval (List.ofFn fun i : Fin 10 => X (pos i)) || star X) := by
  have hH := H_fold C.gates _ _ (H_init X)
  obtain ⟨hlen, _, hv⟩ := hH
  set W := (C.gates.map rl).foldl step (List.ofFn X) with hW
  have hWlen : W.length = 14 + C.gates.length := by rw [hW, fold_len]; simp
  have hin : ∀ k : Fin 14, W.getD k false = X k := by
    intro k
    rw [hW, fold_pre _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hst := extra_fold W X (by omega) hin
  rw [hWlen] at hst
  have hE : ((extra (14 + C.gates.length)).foldl step W).length = 14 + C.gates.length + 11 := by
    rw [fold_len, hWlen]; simp [extra]
  have hC1 : (C.gates.foldl step (List.ofFn fun i : Fin 10 => X (pos i))).length =
      10 + C.gates.length := by rw [fold_len]; simp
  unfold build
  split_ifs with ho
  · simp only [Circuit.eval, wires_eq, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [← hW, step_eq _ _ _ (by rw [hE])]
    simp only [List.map_cons, List.map_nil]
    rw [fold_pre _ _ _ (by rw [hWlen]; exact phi_bound _ _ ho), hv, hst]
    simp [GateOp.eval, wires_eq]
  · simp only [Circuit.eval, wires_eq, List.foldl_append]
    rw [← hW, hst, List.getD_eq_default _ _ (by rw [hC1]; omega)]
    simp

end PEqualNP.Outside.L_meta_3517

theorem PEqualNP.Outside.L_meta_3517 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (∀ x3 ∈ x1.gates, x3.inputs.Nodup) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (2 : ℕ) ≤ x4.size ∧ x4.size ≤ x1.size + (12 : ℕ) ∧ ∀ (x5 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x5) = (x1.eval (List.ofFn fun (x6 : Fin (10 : ℕ)) => x5 ([(0 : Fin (14 : ℕ)), (1 : Fin (14 : ℕ)), (2 : Fin (14 : ℕ)), (3 : Fin (14 : ℕ)), (5 : Fin (14 : ℕ)), (6 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ)), (8 : Fin (14 : ℕ)), (9 : Fin (14 : ℕ)), (12 : Fin (14 : ℕ))].getD ↑x6 (0 : Fin (14 : ℕ)))) || Decidable.decide (∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true)) := by
  intro C hC hnd
  refine ⟨PEqualNP.Outside.L_meta_3517.build C, PEqualNP.Outside.L_meta_3517.ao2_build C hC,
    PEqualNP.Outside.L_meta_3517.nodup_build C hnd,
    (PEqualNP.Outside.L_meta_3517.size_build C).1, (PEqualNP.Outside.L_meta_3517.size_build C).2,
    fun X => ?_⟩
  rw [PEqualNP.Outside.L_meta_3517.eval_build, PEqualNP.Outside.L_meta_3517.star_eq]
  rfl
