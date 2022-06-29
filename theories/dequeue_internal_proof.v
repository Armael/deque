From Coq Require Import Program List ZArith ssreflect Lia.
Import ListNotations.
From Equations Require Import Equations.
From deque Require Import dequeue_internal.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics Reflect.

#[local] Obligation Tactic := try constructor.

Definition option_seq {A B} (f: A -> list B) (o: option A) : list B :=
  match o with
  | None => []
  | Some x => f x
  end.

Definition pair_seq {A} (p: A * A) : list A := let '(a, b) := p in [a;b].

Fixpoint flattenp {A} (l: list (A * A)): list A :=
  match l with
  | [] => []
  | (x, y) :: l' => x :: y :: flattenp l'
  end.

Lemma flattenp_app A (l1: list (A * A)) l2 : flattenp (l1 ++ l2) = flattenp l1 ++ flattenp l2.
Proof. revert l2; induction l1; hauto. Qed.

#[export] Hint Rewrite <-app_assoc : rlist.
#[export] Hint Rewrite <-app_comm_cons : rlist.
#[export] Hint Rewrite flattenp_app : rlist.
#[export] Hint Rewrite app_nil_r : rlist.
#[export] Hint Rewrite compose_id_right : rlist.

Equations buffer_seq {A C} : buffer A C -> list A :=
buffer_seq B0 := [];
buffer_seq (B1 a) := [a];
buffer_seq (B2 a b) := [a;b];
buffer_seq (B3 a b c) := [a;b;c];
buffer_seq (B4 a b c d) := [a;b;c;d];
buffer_seq (B5 a b c d e) := [a;b;c;d;e].

Equations yellow_buffer_seq {A} : yellow_buffer A -> list A :=
yellow_buffer_seq (Yellowish buf) := buffer_seq buf.

Equations any_buffer_seq {A} : any_buffer A -> list A :=
any_buffer_seq (Any buf) := buffer_seq buf.

Equations deque_seq {A B C K} : deque A B C K -> list A * list A * (list B -> list A) :=
deque_seq HOLE := ([], [], id);
deque_seq (Yellow buf1 dq buf2) with (deque_seq dq) => {
  deque_seq (Yellow buf1 _ buf2) (l1, l2, k) :=
    (buffer_seq buf1 ++ flattenp l1, flattenp l2 ++ buffer_seq buf2, (flattenp ∘ k))
};
deque_seq (Green buf1 dq buf2) with (deque_seq dq) => {
  deque_seq (Green buf1 _ buf2) (l1, l2, k) :=
    (buffer_seq buf1 ++ flattenp l1, flattenp l2 ++ buffer_seq buf2, (flattenp ∘ k))
};
deque_seq (Red buf1 dq buf2) with (deque_seq dq) => {
  deque_seq (Red buf1 _ buf2) (l1, l2, k) :=
    (buffer_seq buf1 ++ flattenp l1, flattenp l2 ++ buffer_seq buf2, (flattenp ∘ k))
}.

Equations kont_seq {A C} : kont A C -> list A :=
kont_seq (Small buf) := buffer_seq buf;
kont_seq (G dq kont) with (deque_seq dq), (kont_seq kont) => {
  kont_seq _ (l1, l2, k) lk := l1 ++ k lk ++ l2
};
kont_seq (Y dq kont) with (deque_seq dq), (kont_seq kont) => {
  kont_seq _ (l1, l2, k) lk := l1 ++ k lk ++ l2
};
kont_seq (R dq kont) with (deque_seq dq), (kont_seq kont) => {
  kont_seq _ (l1, l2, k) lk := l1 ++ k lk ++ l2
}.

Equations s_seq {A} : s A -> list A :=
s_seq (T kont) := kont_seq kont.

Lemma green_prefix_cons_correct A (x:A) buf :
  buffer_seq (green_prefix_cons x buf) = x :: buffer_seq buf.
Proof. funelim (green_prefix_cons x buf); sfirstorder. Qed.

Lemma green_suffix_snoc_correct A (x:A) buf :
  buffer_seq (green_suffix_snoc buf x) = buffer_seq buf ++ [x].
Proof. funelim (green_suffix_snoc buf x); sfirstorder. Qed.

Lemma yellow_prefix_cons_correct A (x:A) buf :
  any_buffer_seq (yellow_prefix_cons x buf) = x :: yellow_buffer_seq buf.
Proof. funelim (yellow_prefix_cons x buf); sfirstorder. Qed.

Lemma yellow_suffix_snoc_correct A buf (x:A) :
  any_buffer_seq (yellow_suffix_snoc buf x) = yellow_buffer_seq buf ++ [x].
Proof. funelim (yellow_suffix_snoc buf x); sfirstorder. Qed.

Lemma buffer_cons_correct A C (x:A) (buf:buffer A C) :
  kont_seq (buffer_cons x buf) = x :: buffer_seq buf.
Proof. funelim (buffer_cons x buf); sfirstorder. Qed.

Lemma buffer_snoc_correct A C (x:A) (buf:buffer A C) :
  kont_seq (buffer_snoc buf x) = buffer_seq buf ++ [x].
Proof. funelim (buffer_snoc buf x); sfirstorder. Qed.

Definition cons_seq {A B} (f: B -> list A) (p: A * B) : list A :=
  let '(a, b) := p in a :: f b.

Definition snoc_seq {A B} (f: B -> list A) (p: B * A) : list A :=
  let '(b, a) := p in f b ++ [a].

Lemma green_uncons_correct A (buf:buffer A is_green) x buf':
  green_uncons buf = (x, buf') ->
  buffer_seq buf = x :: yellow_buffer_seq buf'.
Proof. funelim (green_uncons buf); fcrush. Qed.

(* Lemma green_uncons_correct' A (buf:buffer A is_green): *)
(*   cons_seq yellow_buffer_seq (green_uncons buf) = buffer_seq buf. *)
(* Proof. *)
(*   funelim (green_uncons buf); unfold cons_seq; now simp green_uncons buffer_seq yellow_buffer_seq. *)
(* Qed. *)

Lemma green_unsnoc_correct A (buf:buffer A is_green) x buf':
  green_unsnoc buf = (buf', x) ->
  buffer_seq buf = yellow_buffer_seq buf' ++ [x].
Proof. funelim (green_unsnoc buf); fcrush. Qed.

(* Lemma green_unsnoc_correct' A (buf:buffer A is_green) : *)
(*   snoc_seq yellow_buffer_seq (green_unsnoc buf) = buffer_seq buf. *)
(* Proof. *)
(*   funelim (green_unsnoc buf); unfold snoc_seq; now simp green_unsnoc buffer_seq. *)
(* Qed. *)

Lemma yellow_uncons_correct A (buf:yellow_buffer A) x buf' :
  yellow_uncons buf = (x, buf') ->
  yellow_buffer_seq buf = x :: any_buffer_seq buf'.
Proof. funelim (yellow_uncons buf); fcrush. Qed.

(* Lemma yellow_uncons_correct' A (buf:yellow_buffer A) : *)
(*   cons_seq any_buffer_seq (yellow_uncons buf) = yellow_buffer_seq buf. *)
(* Proof. *)
(*   funelim (yellow_uncons buf); unfold cons_seq; now simp yellow_uncons yellow_buffer_seq buffer_seq. *)
(* Qed. *)

Lemma yellow_unsnoc_correct A (buf:yellow_buffer A) x buf' :
  yellow_unsnoc buf = (buf', x) ->
  yellow_buffer_seq buf = any_buffer_seq buf' ++ [x].
Proof. funelim (yellow_unsnoc buf); fcrush. Qed.

(* Lemma yellow_unsnoc_correct' A (buf:yellow_buffer A) : *)
(*   snoc_seq any_buffer_seq (yellow_unsnoc buf) = yellow_buffer_seq buf. *)
(* Proof. *)
(*   funelim (yellow_unsnoc buf); unfold snoc_seq; now simp yellow_unsnoc yellow_buffer_seq buffer_seq. *)
(* Qed. *)

Lemma buffer_uncons_Some_correct A C (buf:buffer A C) x buf':
  buffer_uncons buf = Some (x, buf') ->
  buffer_seq buf = x :: any_buffer_seq buf'.
Proof. funelim (buffer_uncons buf); fcrush. Qed.

Lemma buffer_uncons_None_correct A C (buf:buffer A C):
  buffer_uncons buf = None ->
  buffer_seq buf = [].
Proof. funelim (buffer_uncons buf); fcrush. Qed.

Lemma buffer_unsnoc_Some_correct A C (buf:buffer A C) x buf':
  buffer_unsnoc buf = Some (buf', x) ->
  buffer_seq buf = any_buffer_seq buf' ++ [x].
Proof. funelim (buffer_unsnoc buf); fcrush. Qed.

Lemma buffer_unsnoc_None_correct A C (buf:buffer A C) :
  buffer_unsnoc buf = None ->
  buffer_seq buf = [].
Proof. funelim (buffer_unsnoc buf); fcrush. Qed.

Lemma prefix_rot_correct A C x (buf:buffer A C) buf' y :
  prefix_rot x buf = (buf', y) ->
  x :: buffer_seq buf = buffer_seq buf' ++ [y].
Proof. funelim (prefix_rot x buf); fcrush. Qed.

Lemma suffix_rot_correct A C x (buf:buffer A C) buf' y :
  suffix_rot buf x = (y, buf') ->
  buffer_seq buf ++ [x] = y :: buffer_seq buf'.
Proof. funelim (suffix_rot buf x); fcrush. Qed.

Lemma prefix_decompose_underflow_correct A C (buf:buffer A C) opt:
  prefix_decompose buf = Underflow opt ->
  buffer_seq buf = option_seq (fun x => [x]) opt.
Proof. funelim (prefix_decompose buf); fcrush. Qed.

Lemma prefix_decompose_ok_correct A C (buf:buffer A C) buf':
  prefix_decompose buf = Ok buf' ->
  buffer_seq buf = buffer_seq buf'.
Proof. funelim (prefix_decompose buf); fcrush. Qed.

Lemma prefix_decompose_overflow_correct A C (buf:buffer A C) buf' p :
  prefix_decompose buf = Overflow buf' p ->
  buffer_seq buf = buffer_seq buf' ++ pair_seq p.
Proof. funelim (prefix_decompose buf); fcrush. Qed.

Lemma suffix_decompose_underflow_correct A C (buf:buffer A C) opt:
  suffix_decompose buf = Underflow opt ->
  buffer_seq buf = option_seq (fun x => [x]) opt.
Proof. funelim (suffix_decompose buf); fcrush. Qed.

Lemma suffix_decompose_ok_correct A C (buf:buffer A C) buf':
  suffix_decompose buf = Ok buf' ->
  buffer_seq buf = buffer_seq buf'.
Proof. funelim (suffix_decompose buf); fcrush. Qed.

Lemma suffix_decompose_overflow_correct A C (buf:buffer A C) buf' p :
  suffix_decompose buf = Overflow buf' p ->
  buffer_seq buf = pair_seq p ++ buffer_seq buf'.
Proof. funelim (suffix_decompose buf); fcrush. Qed.

Lemma prefix23_correct A G Y (o: option A) (p: A * A) :
  buffer_seq (@prefix23 A G Y o p) = option_seq (fun x => [x]) o ++ pair_seq p.
Proof. funelim (prefix23 o p); reflexivity. Qed.

Lemma suffix23_correct A G Y (o: option A) (p: A * A) :
  buffer_seq (@suffix23 A G Y p o) = pair_seq p ++ option_seq (fun x => [x]) o.
Proof. funelim (suffix23 p o); reflexivity. Qed.

Lemma prefix12_correct A (x: A) (o: option A) :
  buffer_seq (prefix12 x o) = x :: option_seq (fun x => [x]) o.
Proof. funelim (prefix12 x o); reflexivity. Qed.

Lemma green_prefix_concat_correct A C (buf1:buffer A C) buf2 buf1' buf2' :
  green_prefix_concat buf1 buf2 = (buf1', buf2') ->
  buffer_seq buf1 ++ flattenp (buffer_seq buf2) = buffer_seq buf1' ++ flattenp (yellow_buffer_seq buf2').
Proof.
  funelim (green_prefix_concat buf1 buf2); rewrite <- Heqcall.
  { hauto use:prefix_decompose_underflow_correct,prefix23_correct,green_uncons_correct db:green_prefix_concat,rlist. }
  { hauto use:prefix_decompose_ok_correct. }
  { hauto use:prefix_decompose_overflow_correct,green_prefix_cons_correct db:yellow_buffer_seq,rlist. }
Qed.

Lemma green_suffix_concat_correct A C buf1 (buf2: buffer A C) buf1' buf2' :
  green_suffix_concat buf1 buf2 = (buf1', buf2') ->
  flattenp (buffer_seq buf1) ++ buffer_seq buf2 = flattenp (yellow_buffer_seq buf1') ++ buffer_seq buf2'.
Proof.
  funelim (green_suffix_concat buf1 buf2); rewrite <- Heqcall.
  { hauto use:green_unsnoc_correct,suffix_decompose_underflow_correct,suffix23_correct db:rlist. }
  { hauto use:suffix_decompose_ok_correct. }
  { hauto use:green_suffix_snoc_correct,suffix_decompose_overflow_correct db:yellow_buffer_seq,rlist. }
Qed.

Lemma prefix_concat_correct A B (buf1: buffer A B) buf2 buf1' buf2' :
  prefix_concat buf1 buf2 = (buf1', buf2') ->
  buffer_seq buf1 ++ flattenp (yellow_buffer_seq buf2) =
  buffer_seq buf1' ++ flattenp (any_buffer_seq buf2').
Proof.
  funelim (prefix_concat buf1 buf2); rewrite <- Heqcall.
  { hauto use:yellow_uncons_correct,prefix23_correct,prefix_decompose_underflow_correct db:rlist. }
  { hauto use:prefix_decompose_ok_correct. }
  { hauto use:prefix_decompose_overflow_correct,yellow_prefix_cons_correct db:rlist. }
Qed.

Lemma suffix_concat_correct A B buf1 (buf2: buffer A B) buf1' buf2' :
  suffix_concat buf1 buf2 = (buf1', buf2') ->
  flattenp (yellow_buffer_seq buf1) ++ buffer_seq buf2 =
  flattenp (any_buffer_seq buf1') ++ buffer_seq buf2'.
Proof.
  funelim (suffix_concat buf1 buf2); rewrite <- Heqcall.
  { hauto use:yellow_unsnoc_correct,suffix_decompose_underflow_correct,suffix23_correct db:rlist. }
  { hauto use:suffix_decompose_ok_correct. }
  { hauto use:suffix_decompose_overflow_correct,yellow_suffix_snoc_correct db:rlist. }
Qed.

Lemma buffer_unsandwich_alone_correct A C (buf:buffer A C) opt :
  buffer_unsandwich buf = Alone opt ->
  buffer_seq buf = option_seq (fun x => [x]) opt.
Proof. funelim (buffer_unsandwich buf); fcrush. Qed.

Lemma buffer_unsandwich_sandwich_correct A C C' (buf:buffer A C) (buf':buffer A C') x y :
  buffer_unsandwich buf = Sandwich x buf' y ->
  buffer_seq buf = x :: buffer_seq buf' ++ [y].
Proof.
  funelim (buffer_unsandwich buf); hauto db: buffer_unsandwich, buffer_seq.
Qed.

Lemma buffer_halve_correct A C (buf: buffer A C) opt buf' :
  buffer_halve buf = (opt, buf') ->
  buffer_seq buf = option_seq (fun x => [x]) opt ++ flattenp (any_buffer_seq buf').
Proof. funelim (buffer_halve buf); fcrush. Qed.

Lemma kont_of_opt3_correct A (opt1: option A) opt2 opt3 :
  kont_seq (kont_of_opt3 opt1 opt2 opt3) =
  option_seq (fun x => [x]) opt1 ++
  flattenp (option_seq (fun x => [x]) opt2) ++
  option_seq (fun x => [x]) opt3.
Proof. funelim (kont_of_opt3 opt1 opt2 opt3); sfirstorder. Qed.

Lemma flattenp_congr A (l l': list (A * A)) :
  l = l' ->
  flattenp l = flattenp l'.
Proof. fcrush. Qed.

Lemma make_small_correct A C1 C2 C3 (buf1: buffer A C1) (buf2: buffer (A * A) C2) (buf3: buffer A C3) :
  kont_seq (make_small buf1 buf2 buf3) =
  buffer_seq buf1 ++
  flattenp (buffer_seq buf2) ++
  buffer_seq buf3.
Proof.
  funelim (make_small buf1 buf2 buf3); rewrite <- Heqcall.
  { destruct (suffix_rot buf ab) as [[c d] center] eqn:Hsuffix.
    apply suffix_rot_correct, flattenp_congr in Hsuffix.
    erewrite prefix_decompose_underflow_correct; [|eassumption].
    erewrite (suffix_decompose_overflow_correct _ _ suffix1); [|eassumption].
    simp kont_seq deque_seq.
    rewrite prefix23_correct -!app_assoc//= compose_id_right. f_equal.
    destruct ab. cbn in *. rewrite 2!app_comm_cons -Hsuffix. hauto db:rlist. }
  { hauto use: prefix_decompose_ok_correct, suffix_decompose_ok_correct
          db: make_small, kont_seq, deque_seq, rlist. }
  { hauto use: prefix_decompose_ok_correct, suffix_decompose_overflow_correct, buffer_snoc_correct
          db: make_small, kont_seq, deque_seq, rlist. }
  { destruct (prefix_rot ab buf) as [center [c d]] eqn:Hprefix.
    apply prefix_rot_correct, flattenp_congr in Hprefix.
    simp kont_seq deque_seq.
    rewrite compose_id_right //= app_nil_r.
    erewrite (prefix_decompose_overflow_correct _ _ prefix1); [|eassumption].
    erewrite (suffix_decompose_underflow_correct _ _ suffix1); [|eassumption].
    rewrite suffix23_correct -!app_assoc. f_equal.
    destruct ab as [a b]. cbn in *. rewrite 2!app_comm_cons Hprefix. hauto db:rlist. }
  { hauto use:prefix_decompose_overflow_correct,suffix_decompose_ok_correct,buffer_cons_correct
          db:make_small,kont_seq,deque_seq,rlist. }
  { hauto use:prefix_decompose_overflow_correct,suffix_decompose_overflow_correct,
                buffer_halve_correct,prefix12_correct
          db:kont_seq,deque_seq,make_small,rlist q:on. }
  { hauto use:prefix_decompose_underflow_correct,suffix_decompose_underflow_correct,
              buffer_unsandwich_alone_correct, kont_of_opt3_correct
          db:kont_seq,deque_seq,make_small,rlist. }
  { hauto use:prefix_decompose_underflow_correct,suffix_decompose_underflow_correct,
              buffer_unsandwich_sandwich_correct, kont_of_opt3_correct,
              suffix23_correct,prefix23_correct,buffer_halve_correct
          db:kont_seq,deque_seq,make_small,rlist. }
  { hauto use:suffix_decompose_ok_correct,prefix_decompose_underflow_correct,
              buffer_uncons_Some_correct,prefix23_correct
           db:kont_seq,deque_seq,make_small,rlist. }
  { hauto use:prefix_decompose_underflow_correct,suffix_decompose_ok_correct,
              buffer_uncons_None_correct,buffer_cons_correct
           db:kont_seq,deque_seq,make_small,rlist lq:on. }
  { hauto use:prefix_decompose_underflow_correct,suffix_decompose_ok_correct,
              buffer_uncons_Some_correct,prefix23_correct
           db:kont_seq,deque_seq,make_small,rlist lq:on. }
  { hauto use:prefix_decompose_underflow_correct,suffix_decompose_ok_correct,
              buffer_uncons_None_correct
           db:kont_seq,deque_seq,make_small,rlist lq:on. }
  { hauto use:prefix_decompose_ok_correct,suffix_decompose_underflow_correct,
              buffer_unsnoc_Some_correct,suffix23_correct
           db:kont_seq,deque_seq,make_small,rlist lq:on. }
  { hauto use:prefix_decompose_ok_correct,suffix_decompose_underflow_correct,
              buffer_unsnoc_None_correct,buffer_snoc_correct
           db:kont_seq,deque_seq,make_small,rlist lq:on. }
  { hauto use:prefix_decompose_ok_correct,suffix_decompose_underflow_correct,
              buffer_unsnoc_None_correct
           db:kont_seq,deque_seq,make_small,rlist lq:on. }
Qed.

Lemma green_of_red_correct A (k: kont A is_red) :
  kont_seq (green_of_red k) = kont_seq k.
Proof.
  funelim (green_of_red k); simp green_of_red.
  { hauto use:make_small_correct db:kont_seq,deque_seq,rlist. }
  { destruct (green_prefix_concat p1 p2) as [p1' [? ? p2']] eqn:Hprefix.
    destruct (green_suffix_concat s2 s1) as [[? ? s2'] s1'] eqn:Hsuffix.
    simp kont_seq deque_seq.
    rewrite //= app_nil_r compose_id_right //.
    destruct (deque_seq child) as [[? ?] ?].
    simp kont_seq deque_seq.
    rewrite !flattenp_app -!app_assoc.
    rewrite (app_assoc (buffer_seq p1)).
    erewrite (green_prefix_concat_correct _ _ p1 p2);[|eassumption].
    hauto use:green_prefix_concat_correct,green_suffix_concat_correct,flattenp_app,app_assoc
           db:yellow_buffer_seq.
  }
  { destruct (prefix_concat p1 (Yellowish p2)) as [p1' [? p2']] eqn:Hprefix.
    destruct (suffix_concat (Yellowish s2) s1) as [[? s2'] s1'] eqn:Hsuffix.
    simp kont_seq deque_seq.
    rewrite //= app_nil_r compose_id_right //.
    destruct (deque_seq child) as [[? ?] ?].
    simp kont_seq deque_seq.
    rewrite !flattenp_app -!app_assoc.
    rewrite (app_assoc (buffer_seq p1)).
    apply (prefix_concat_correct _ _ p1 (Yellowish p2)) in Hprefix.
    simp yellow_buffer_seq in Hprefix. rewrite Hprefix.
    hauto use:prefix_concat_correct,suffix_concat_correct,app_assoc
           db:yellow_buffer_seq,any_buffer_seq.
  }
Qed.

Lemma ensure_green_correct A C (ny: not_yellow C) (k: kont A C) :
  kont_seq (ensure_green ny k) = kont_seq k.
Proof. funelim (ensure_green ny k); hauto use:green_of_red_correct. Qed.

Module S.

Lemma cons_correct A (x:A) s :
  s_seq (S.cons x s) = x :: s_seq s.
Proof.
  funelim (S.cons x s); simp cons s_seq yellow red kont_seq deque_seq.
  { hauto use:buffer_cons_correct. }
  { destruct (deque_seq child) as [[? ?] ?]. simp kont_seq deque_seq.
    hauto use:green_prefix_cons_correct,ensure_green_correct db:rlist. }
  { destruct (yellow_prefix_cons x (Yellowish p1)) as [? ?] eqn:Hprefix.
    epose proof (yellow_prefix_cons_correct _ x (Yellowish p1)) as HH. rewrite Hprefix in HH.
    simp s_seq red kont_seq. rewrite green_of_red_correct. simp kont_seq deque_seq.
    destruct (deque_seq child) as [[? ?] ?].
    hauto db:any_buffer_seq,kont_seq,deque_seq,rlist. }
Qed.

Lemma snoc_correct A s (x:A) :
  s_seq (S.snoc s x) = s_seq s ++ [x].
Proof.
  funelim (S.snoc s x); simp snoc s_seq yellow red kont_seq deque_seq.
  { hauto use:buffer_snoc_correct. }
  { destruct (deque_seq child) as [[? ?] ?]. simp kont_seq deque_seq.
    hauto use:green_suffix_snoc_correct,ensure_green_correct db:rlist. }
  { destruct (yellow_suffix_snoc (Yellowish s1) x) as [? ?] eqn:Hsuffix.
    simp s_seq red kont_seq. rewrite green_of_red_correct. simp kont_seq deque_seq.
    destruct (deque_seq child) as [[? ?] ?]. simp kont_seq deque_seq.
    epose proof (yellow_suffix_snoc_correct _ (Yellowish s1) x) as HH.
    rewrite Hsuffix in HH. simp any_buffer_seq in HH. rewrite HH -!app_assoc //. }
Qed.

Lemma uncons_correct A (dq: s A) :
  option_seq (cons_seq s_seq) (S.uncons dq) = s_seq dq.
Proof.
  funelim (S.uncons dq); simp uncons; cbn.
  { destruct (green_uncons p1) as [? [? ? ?]] eqn:Huncons. cbn.
    simp s_seq kont_seq yellow.
    destruct (deque_seq (Green p1 child s1)) as [[? ?] ?] eqn:Hdq1.
    simp kont_seq deque_seq.
    destruct (deque_seq child) as [[? ?] ?] eqn:Hdq2.
    simp deque_seq in Hdq1. rewrite Hdq2 in Hdq1.
    simp deque_seq in Hdq1.
    hauto use:ensure_green_correct,green_uncons_correct
           db:kont_seq,deque_seq,yellow_buffer_seq,rlist. }
  { destruct (yellow_uncons (Yellowish p1)) as [? [? ?]] eqn:Huncons.
    simp s_seq kont_seq deque_seq.
    destruct (deque_seq child) as [[? ?] ?] eqn:Hdq1. cbn.
    simp s_seq kont_seq deque_seq red.
    rewrite green_of_red_correct. simp kont_seq deque_seq. rewrite Hdq1.
    simp kont_seq deque_seq. eapply yellow_uncons_correct in Huncons.
    simp yellow_buffer_seq in Huncons. rewrite Huncons.
    rewrite -!app_assoc -app_comm_cons. now simp any_buffer_seq. }
  { simp s_seq kont_seq deque_seq. rewrite Heq/=. simp s_seq kont_seq.
    rewrite -(buffer_uncons_correct _ _ buf) Heq /=. now simp any_buffer_seq. }
  { simp s_seq kont_seq deque_seq. rewrite Heq/=.
    epose proof (buffer_uncons_correct _ _ buf) as HH. rewrite Heq //= in HH. }
Qed.

Lemma unsnoc_correct A (dq: s A) :
  option_seq (snoc_seq s_seq) (S.unsnoc dq) = s_seq dq.
Proof.
  funelim (S.unsnoc dq); simp unsnoc.
  { destruct (green_unsnoc s1) as [[? ? ?] ?] eqn:Hunsnoc. cbn.
    simp s_seq kont_seq deque_seq yellow.
    destruct (deque_seq child) as [[? ?] ?]. cbn. simp kont_seq deque_seq.
    rewrite ensure_green_correct. rewrite -!app_assoc.
    erewrite (green_unsnoc_correct _ s1); [| eassumption]. done. }
  { destruct (yellow_unsnoc (Yellowish s1)) as [[? ?] ?] eqn:Hunsnoc. cbn.
    simp s_seq kont_seq deque_seq red.
    rewrite green_of_red_correct. simp kont_seq deque_seq.
    destruct (deque_seq child) as [[? ?] ?]. simp kont_seq deque_seq.
    eapply yellow_unsnoc_correct in Hunsnoc. simp yellow_buffer_seq in Hunsnoc.
    rewrite Hunsnoc. rewrite -!app_assoc //. }
  { simp s_seq kont_seq deque_seq. rewrite Heq/=. simp s_seq kont_seq.
    rewrite -(buffer_unsnoc_correct _ _ buf) Heq /=. now simp any_buffer_seq. }
  { simp s_seq kont_seq deque_seq. rewrite Heq/=.
    epose proof (buffer_unsnoc_correct _ _ buf) as HH. rewrite Heq //= in HH. }
Qed.

End S.

Ltac case_if Hcond :=
  match goal with |- context [ if ?cond then _ else _ ] =>
    destruct cond eqn:Hcond
  end.

Tactic Notation "case_if" simple_intropattern(Hcond) := case_if Hcond.

Definition t_is_seq {A} (dq: t A) (l: list A) : Prop :=
  if tlength dq >=? 0 then
    l = s_seq (tseq dq) /\
    List.length l = Z.to_nat (tlength dq)
  else
    l = List.rev (s_seq (tseq dq)) /\
    List.length l = Z.to_nat (- (tlength dq)).

Lemma empty_correct {A} : t_is_seq (@empty A) [].
Proof. done. Qed.

Lemma is_empty_correct {A} (dq: t A) l :
  t_is_seq dq l ->
  is_empty dq = true <-> l = [].
Proof.
  destruct dq as [x s]. rewrite /is_empty /t_is_seq /=.
  case_if Hcond; cbn.
  { intros [-> HH]. rewrite Z.eqb_eq.
    split; [intros -> | intros HHH; rewrite HHH in HH].
    by rewrite length_zero_iff_nil in HH. by cbn in *; lia. }
  { intros [-> HH]. rewrite Z.eqb_eq.
    split; [ intros -> | intros HHH; rewrite HHH in HH].
    by rewrite rev_length// in HH. by cbn in *; lia. }
Qed.

Lemma length_correct {A} (dq: t A) l :
  t_is_seq dq l ->
  length dq = Z.of_nat (List.length l).
Proof.
  destruct dq as [x s]. rewrite /length /t_is_seq /=.
  case_if Hcond; cbn; lia.
Qed.

Lemma rev_correct {A} (dq: t A) l :
  t_is_seq dq l ->
  t_is_seq (rev dq) (List.rev l).
Proof.
  destruct dq as [x s]. rewrite /rev /t_is_seq /=.
  destruct (Z_zerop x) as [->|?].
  { case_if ?; [|lia]. case_if ?; [|lia].
    by intros [-> ->%length_zero_iff_nil]. }
  case_if Hcond; cbn.
  { intros [-> HH]. case_if Hcond'; [lia|].
    rewrite Z.opp_involutive rev_length //. }
  { intros [-> HH]. case_if ?; [|lia]. rewrite rev_involutive.
    rewrite rev_length // in HH. }
Qed.

Lemma cons_correct {A} (x:A) dq l :
  t_is_seq dq l ->
  t_is_seq (cons x dq) (x :: l).
Proof.
  destruct dq as [n s]. rewrite /t_is_seq /cons /=.
  case_if Hcond.
  { intros [-> Hlen]; cbn.
    case_if ?; [|lia]. rewrite S.cons_correct. rewrite Hlen.
    split; auto. lia. }
  { intros [-> Hlen]; cbn. case_if ?; [lia|].
    rewrite rev_length in Hlen |- *.
    rewrite S.snoc_correct rev_app_distr /=. split; auto. lia. }
Qed.
