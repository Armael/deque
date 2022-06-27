From Coq Require Import Program List ssreflect.
Import ListNotations.
From Equations Require Import Equations.
From deque Require Import dequeue_internal.

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
Proof. revert l2; induction l1 as [| [x y] l1]; intros; cbn; auto. now rewrite IHl1. Qed.

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
Proof. funelim (green_prefix_cons x buf); now simp green_prefix_cons buffer_seq. Qed.

Lemma green_suffix_snoc_correct A (x:A) buf :
  buffer_seq (green_suffix_snoc buf x) = buffer_seq buf ++ [x].
Proof. funelim (green_suffix_snoc buf x); now simp green_suffix_snoc buffer_seq. Qed.

Lemma yellow_prefix_cons_correct A (x:A) buf :
  any_buffer_seq (yellow_prefix_cons x buf) = x :: yellow_buffer_seq buf.
Proof.
  funelim (yellow_prefix_cons x buf);
    now simp any_buffer_seq yellow_prefix_cons buffer_seq yellow_buffer_seq.
Qed.

Lemma yellow_suffix_snoc_correct A buf (x:A) :
  any_buffer_seq (yellow_suffix_snoc buf x) = yellow_buffer_seq buf ++ [x].
Proof.
  funelim (yellow_suffix_snoc buf x);
    now simp any_buffer_seq yellow_suffix_snoc buffer_seq yellow_buffer_seq.
Qed.

Lemma buffer_cons_correct A C (x:A) (buf:buffer A C) :
  kont_seq (buffer_cons x buf) = x :: buffer_seq buf.
Proof.
  funelim (buffer_cons x buf);
    now simp buffer_cons kont_seq buffer_seq deque_seq.
Qed.

Lemma buffer_snoc_correct A C (x:A) (buf:buffer A C) :
  kont_seq (buffer_snoc buf x) = buffer_seq buf ++ [x].
Proof.
  funelim (buffer_snoc buf x);
    now simp buffer_snoc kont_seq buffer_seq deque_seq.
Qed.

Definition cons_seq {A B} (f: B -> list A) (p: A * B) : list A :=
  let '(a, b) := p in a :: f b.

Definition snoc_seq {A B} (f: B -> list A) (p: B * A) : list A :=
  let '(b, a) := p in f b ++ [a].

Lemma green_uncons_correct A (buf:buffer A is_green) x buf':
  green_uncons buf = (x, buf') ->
  buffer_seq buf = x :: yellow_buffer_seq buf'.
Proof.
  funelim (green_uncons buf); simp green_uncons buffer_seq.
  all: inversion 1; subst; now simp yellow_buffer_seq.
Qed.

(* Lemma green_uncons_correct' A (buf:buffer A is_green): *)
(*   cons_seq yellow_buffer_seq (green_uncons buf) = buffer_seq buf. *)
(* Proof. *)
(*   funelim (green_uncons buf); unfold cons_seq; now simp green_uncons buffer_seq yellow_buffer_seq. *)
(* Qed. *)

Lemma green_unsnoc_correct A (buf:buffer A is_green) x buf':
  green_unsnoc buf = (buf', x) ->
  buffer_seq buf = yellow_buffer_seq buf' ++ [x].
Proof.
  funelim (green_unsnoc buf); simp green_unsnoc buffer_seq.
  all: inversion 1; subst; now simp yellow_buffer_seq.
Qed.

(* Lemma green_unsnoc_correct' A (buf:buffer A is_green) : *)
(*   snoc_seq yellow_buffer_seq (green_unsnoc buf) = buffer_seq buf. *)
(* Proof. *)
(*   funelim (green_unsnoc buf); unfold snoc_seq; now simp green_unsnoc buffer_seq. *)
(* Qed. *)

Lemma yellow_uncons_correct A (buf:yellow_buffer A) x buf' :
  yellow_uncons buf = (x, buf') ->
  yellow_buffer_seq buf = x :: any_buffer_seq buf'.
Proof.
  funelim (yellow_uncons buf); simp yellow_uncons yellow_buffer_seq buffer_seq.
  all: inversion 1; subst; now simp any_buffer_seq.
Qed.

(* Lemma yellow_uncons_correct' A (buf:yellow_buffer A) : *)
(*   cons_seq any_buffer_seq (yellow_uncons buf) = yellow_buffer_seq buf. *)
(* Proof. *)
(*   funelim (yellow_uncons buf); unfold cons_seq; now simp yellow_uncons yellow_buffer_seq buffer_seq. *)
(* Qed. *)

Lemma yellow_unsnoc_correct A (buf:yellow_buffer A) x buf' :
  yellow_unsnoc buf = (buf', x) ->
  yellow_buffer_seq buf = any_buffer_seq buf' ++ [x].
Proof.
  funelim (yellow_unsnoc buf); simp yellow_unsnoc yellow_buffer_seq buffer_seq.
  all: inversion 1; subst; now simp any_buffer_seq.
Qed.

(* Lemma yellow_unsnoc_correct' A (buf:yellow_buffer A) : *)
(*   snoc_seq any_buffer_seq (yellow_unsnoc buf) = yellow_buffer_seq buf. *)
(* Proof. *)
(*   funelim (yellow_unsnoc buf); unfold snoc_seq; now simp yellow_unsnoc yellow_buffer_seq buffer_seq. *)
(* Qed. *)

Lemma buffer_uncons_unsafe_correct A C (buf:buffer A C) (ne: buffer_is_empty buf = false) x buf':
  buffer_uncons_unsafe buf ne = (x, buf') ->
  buffer_seq buf = x :: any_buffer_seq buf'.
Proof.
  funelim (buffer_uncons_unsafe buf ne); simp buffer_uncons_unsafe yellow_uncons.
  now inversion eq.
  all: inversion 1; subst; now simp buffer_seq any_buffer_seq.
Qed.

(* Lemma buffer_uncons_unsafe_correct' A C (buf:buffer A C) (ne: buffer_is_empty buf = false) : *)
(*   cons_seq any_buffer_seq (buffer_uncons_unsafe buf ne) = buffer_seq buf. *)
(* Proof. *)
(*   funelim (buffer_uncons_unsafe buf ne); unfold cons_seq; now simp buffer_uncons_unsafe yellow_uncons. *)
(* Qed. *)

Lemma buffer_unsnoc_unsafe_correct A C (buf:buffer A C) (ne: buffer_is_empty buf = false) x buf':
  buffer_unsnoc_unsafe buf ne = (buf', x) ->
  buffer_seq buf = any_buffer_seq buf' ++ [x].
Proof.
  funelim (buffer_unsnoc_unsafe buf ne); simp buffer_unsnoc_unsafe yellow_uncons.
  now inversion eq.
  all: inversion 1; subst; now simp buffer_seq any_buffer_seq.
Qed.

(* Lemma buffer_unsnoc_unsafe_correct' A C (buf:buffer A C) (ne: buffer_is_empty buf = false) : *)
(*   snoc_seq any_buffer_seq (buffer_unsnoc_unsafe buf ne) = buffer_seq buf. *)
(* Proof. *)
(*   funelim (buffer_unsnoc_unsafe buf ne); unfold snoc_seq; now simp buffer_snoc_unsafe yellow_uncons. *)
(* Qed. *)

Lemma buffer_uncons_correct A C (buf:buffer A C) :
  option_seq (cons_seq any_buffer_seq) (buffer_uncons buf) = buffer_seq buf.
Proof.
  funelim (buffer_uncons buf); unfold option_seq, cons_seq; now simp buffer_uncons buffer_seq.
Qed.

Lemma buffer_unsnoc_correct A C (buf:buffer A C) :
  option_seq (snoc_seq any_buffer_seq) (buffer_unsnoc buf) = buffer_seq buf.
Proof.
  funelim (buffer_unsnoc buf); unfold option_seq, snoc_seq; now simp buffer_snoc buffer_seq.
Qed.

Lemma prefix_rot_correct A C x (buf:buffer A C) :
  snoc_seq buffer_seq (prefix_rot x buf) = x :: buffer_seq buf.
Proof. funelim (prefix_rot x buf); unfold snoc_seq; now simp prefix_rot buffer_seq. Qed.

Lemma suffix_rot_correct A C x (buf:buffer A C) :
  cons_seq buffer_seq (suffix_rot buf x) = buffer_seq buf ++ [x].
Proof. funelim (suffix_rot buf x); unfold cons_seq; now simp suffix_rot buffer_seq. Qed.

Lemma prefix_decompose_underflow_correct A C (buf:buffer A C) opt:
  prefix_decompose buf = Underflow opt ->
  buffer_seq buf = option_seq (fun x => [x]) opt.
Proof.
  funelim (prefix_decompose buf); simp prefix_decompose; inversion 1; subst.
  all: now simp option_seq.
Qed.

Lemma prefix_decompose_ok_correct A C (buf:buffer A C) buf':
  prefix_decompose buf = Ok buf' ->
  buffer_seq buf = buffer_seq buf'.
Proof.
  funelim (prefix_decompose buf); simp prefix_decompose; now inversion 1; subst.
Qed.

Lemma prefix_decompose_overflow_correct A C (buf:buffer A C) buf' p :
  prefix_decompose buf = Overflow buf' p ->
  buffer_seq buf = buffer_seq buf' ++ pair_seq p.
Proof.
  funelim (prefix_decompose buf); simp prefix_decompose; now inversion 1; subst.
Qed.

Lemma suffix_decompose_underflow_correct A C (buf:buffer A C) opt:
  suffix_decompose buf = Underflow opt ->
  buffer_seq buf = option_seq (fun x => [x]) opt.
Proof.
  funelim (suffix_decompose buf); simp suffix_decompose; inversion 1; subst.
  all: now simp option_seq.
Qed.

Lemma suffix_decompose_ok_correct A C (buf:buffer A C) buf':
  suffix_decompose buf = Ok buf' ->
  buffer_seq buf = buffer_seq buf'.
Proof.
  funelim (suffix_decompose buf); simp suffix_decompose; now inversion 1; subst.
Qed.

Lemma suffix_decompose_overflow_correct A C (buf:buffer A C) buf' p :
  suffix_decompose buf = Overflow buf' p ->
  buffer_seq buf = pair_seq p ++ buffer_seq buf'.
Proof.
  funelim (suffix_decompose buf); simp suffix_decompose; now inversion 1; subst.
Qed.

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
  funelim (green_prefix_concat buf1 buf2); simp green_prefix_concat; rewrite Heq.
  all: simp green_prefix_concat.
  { destruct (green_uncons buf2) as [[a b] buf] eqn:HH. inversion 1; subst.
    erewrite green_uncons_correct; [| eassumption]. cbn.
    rewrite prefix23_correct /pair_seq -!app_assoc //.
    erewrite prefix_decompose_underflow_correct; [|eassumption]. done. }
  { inversion 1; subst. erewrite prefix_decompose_ok_correct; eauto. }
  { inversion 1; subst. simp yellow_buffer_seq. rewrite green_prefix_cons_correct.
    destruct ab as [a b]. simpl. erewrite prefix_decompose_overflow_correct; eauto.
    rewrite -app_assoc //. }
Qed.

Lemma green_suffix_concat_correct A C buf1 (buf2: buffer A C) buf1' buf2' :
  green_suffix_concat buf1 buf2 = (buf1', buf2') ->
  flattenp (buffer_seq buf1) ++ buffer_seq buf2 = flattenp (yellow_buffer_seq buf1') ++ buffer_seq buf2'.
Proof.
  funelim (green_suffix_concat buf1 buf2); simp green_suffix_concat; rewrite Heq.
  all: simp green_suffix_concat.
  { destruct (green_unsnoc buf1) as [buf [a b]] eqn:HH. inversion 1; subst.
    erewrite green_unsnoc_correct; [| eassumption].
    rewrite suffix23_correct /pair_seq !app_assoc //.
    erewrite suffix_decompose_underflow_correct; [|eassumption].
    now rewrite flattenp_app. }
  { inversion 1; subst. erewrite (suffix_decompose_ok_correct _ _ buf2); eauto. }
  { inversion 1; subst. simp yellow_buffer_seq. rewrite green_suffix_snoc_correct.
    destruct ab as [a b]. rewrite flattenp_app -app_assoc//=.
    erewrite (suffix_decompose_overflow_correct _ _ buf2); eauto. rewrite /pair_seq//. }
Qed.

Lemma prefix_concat_correct A B (buf1: buffer A B) buf2 buf1' buf2' :
  prefix_concat buf1 buf2 = (buf1', buf2') ->
  buffer_seq buf1 ++ flattenp (yellow_buffer_seq buf2) =
  buffer_seq buf1' ++ flattenp (any_buffer_seq buf2').
Proof.
  funelim (prefix_concat buf1 buf2); simp prefix_concat; rewrite Heq.
  all: simp prefix_concat.
  { destruct (yellow_uncons buf2) as [[a b] buf] eqn:HH. inversion 1; subst.
    erewrite yellow_uncons_correct; [| eassumption].
    rewrite prefix23_correct /pair_seq -!app_assoc.
    erewrite prefix_decompose_underflow_correct; eauto. }
  { inversion 1; subst. simp yellow_buffer_seq any_buffer_seq.
    now erewrite prefix_decompose_ok_correct. }
  { inversion 1; subst. erewrite prefix_decompose_overflow_correct;[|eassumption].
    destruct ab. rewrite -app_assoc yellow_prefix_cons_correct //. }
Qed.

Lemma suffix_concat_correct A B buf1 (buf2: buffer A B) buf1' buf2' :
  suffix_concat buf1 buf2 = (buf1', buf2') ->
  flattenp (yellow_buffer_seq buf1) ++ buffer_seq buf2 =
  flattenp (any_buffer_seq buf1') ++ buffer_seq buf2'.
Proof.
  funelim (suffix_concat buf1 buf2); simp suffix_concat; rewrite Heq.
  all: simp suffix_concat.
  { destruct (yellow_unsnoc (Yellowish _)) as [buf [? ?]] eqn:HH. inversion 1; subst.
    erewrite yellow_unsnoc_correct; [| eassumption].
    rewrite suffix23_correct /pair_seq flattenp_app -!app_assoc.
    erewrite suffix_decompose_underflow_correct; eauto. }
  { inversion 1; subst. simp yellow_buffer_seq any_buffer_seq.
    now erewrite (suffix_decompose_ok_correct _ _ buf2). }
  { inversion 1; subst. erewrite suffix_decompose_overflow_correct;[|eassumption].
    destruct ab. rewrite yellow_suffix_snoc_correct flattenp_app -app_assoc //. }
Qed.

Lemma buffer_unsandwich_alone_correct A C (buf:buffer A C) opt :
  buffer_unsandwich buf = Alone opt ->
  buffer_seq buf = option_seq (fun x => [x]) opt.
Proof.
  funelim (buffer_unsandwich buf); simp buffer_unsandwich; inversion 1; subst;
    now simp buffer_seq.
Qed.

Lemma buffer_unsandwich_sandwich_correct A C C' (buf:buffer A C) (buf':buffer A C') x y :
  buffer_unsandwich buf = Sandwich x buf' y ->
  buffer_seq buf = x :: buffer_seq buf' ++ [y].
Proof.
  funelim (buffer_unsandwich buf); simp buffer_unsandwich; inversion 1; subst.
  all: now simp buffer_seq.
Qed.

Lemma buffer_halve_correct A C (buf: buffer A C) opt buf' :
  buffer_halve buf = (opt, buf') ->
  buffer_seq buf = option_seq (fun x => [x]) opt ++ flattenp (any_buffer_seq buf').
Proof.
  funelim (buffer_halve buf); simp buffer_halve; inversion 1; subst.
  all: simp buffer_seq any_buffer_seq; cbn; done.
Qed.

Lemma kont_of_opt3_correct A (opt1: option A) opt2 opt3 :
  kont_seq (kont_of_opt3 opt1 opt2 opt3) =
  option_seq (fun x => [x]) opt1 ++
  flattenp (option_seq (fun x => [x]) opt2) ++
  option_seq (fun x => [x]) opt3.
Proof.
  funelim (kont_of_opt3 opt1 opt2 opt3); now simp kont_of_opt3 kont_seq buffer_seq.
Qed.

Lemma make_small_correct A C1 C2 C3 (buf1: buffer A C1) (buf2: buffer (A * A) C2) (buf3: buffer A C3) :
  kont_seq (make_small buf1 buf2 buf3) =
  buffer_seq buf1 ++
  flattenp (buffer_seq buf2) ++
  buffer_seq buf3.
Proof.
  funelim (make_small buf1 buf2 buf3); simp make_small.
  { rewrite Heq Heq0. simp make_small.
    destruct (suffix_rot buf ab) as [[c d] center] eqn:Hsuffix.
    erewrite prefix_decompose_underflow_correct; [|eassumption].
    erewrite (suffix_decompose_overflow_correct _ _ suffix1); [|eassumption].
    simp kont_seq deque_seq.
    rewrite prefix23_correct -!app_assoc//=.
    rewrite compose_id_right.
    assert (flattenp ((c, d) :: buffer_seq center) = flattenp (buffer_seq buf ++ [ab])) as HH.
    { epose proof (suffix_rot_correct _ _ ab buf) as HH.
      rewrite /cons_seq Hsuffix // in HH. rewrite HH//. }
    cbn in HH. f_equal. rewrite !app_comm_cons HH flattenp_app -app_assoc //. }
  { rewrite Heq Heq0. simp make_small kont_seq deque_seq.
    rewrite compose_id_right //= app_nil_r.
    erewrite (prefix_decompose_ok_correct _ _ prefix1); [|eassumption].
    erewrite (suffix_decompose_ok_correct _ _ suffix1); [|eassumption]. done. }
  { rewrite Heq Heq0. simp make_small kont_seq deque_seq.
    rewrite compose_id_right //= app_nil_r.
    erewrite (prefix_decompose_ok_correct _ _ prefix1); [|eassumption].
    erewrite (suffix_decompose_overflow_correct _ _ suffix1); [|eassumption].
    rewrite buffer_snoc_correct flattenp_app -!app_assoc //. }
  { rewrite Heq Heq0. simp make_small kont_seq deque_seq.
    destruct (prefix_rot ab buf) as [center [c d]] eqn:Hprefix.
    simp kont_seq deque_seq.
    rewrite compose_id_right //= app_nil_r.
    erewrite (prefix_decompose_overflow_correct _ _ prefix1); [|eassumption].
    erewrite (suffix_decompose_underflow_correct _ _ suffix1); [|eassumption].
    rewrite suffix23_correct -!app_assoc. f_equal.
    destruct ab as [a b]. cbn.
    epose proof (prefix_rot_correct _ _ (a, b) buf) as HH.
    rewrite /snoc_seq Hprefix in HH. rewrite !app_comm_cons.
    rewrite -/(flattenp ((a,b) :: buffer_seq buf)) -HH flattenp_app -app_assoc //. }
  { rewrite Heq Heq0. simp make_small kont_seq deque_seq.
    rewrite compose_id_right //= app_nil_r.
    erewrite (prefix_decompose_overflow_correct _ _ prefix1); [|eassumption].
    erewrite (suffix_decompose_ok_correct _ _ suffix1); [|eassumption].
    destruct ab as [a b]. rewrite buffer_cons_correct -!app_assoc //=. }
  { rewrite Heq Heq0. simp make_small kont_seq deque_seq.
    destruct (buffer_halve buf) as [x [C rest]] eqn:Hhalve.
    simp kont_seq deque_seq.
    rewrite compose_id_right //= app_nil_r -!app_assoc.
    rewrite prefix12_correct /=. destruct ab as [a b].
    erewrite (buffer_halve_correct _ _ buf);[|eassumption].
    erewrite (prefix_decompose_overflow_correct _ _ prefix1); [|eassumption].
    erewrite (suffix_decompose_overflow_correct _ _ suffix1); [|eassumption].
    rewrite !flattenp_app -!app_assoc //. }
  { rewrite Heq0 Heq1. simp make_small. rewrite Heq. simp make_small.
    rewrite kont_of_opt3_correct.
    erewrite (prefix_decompose_underflow_correct _ _ prefix1); [|eassumption].
    erewrite (suffix_decompose_underflow_correct _ _ suffix1); [|eassumption].
    erewrite buffer_unsandwich_alone_correct; eauto. }
  { rewrite Heq0 Heq1. simp make_small. rewrite Heq. simp make_small kont_seq deque_seq.
    rewrite compose_id_right //= app_nil_r.
    erewrite (prefix_decompose_underflow_correct _ _ prefix1); [|eassumption].
    erewrite (suffix_decompose_underflow_correct _ _ suffix1); [|eassumption].
    erewrite (buffer_unsandwich_sandwich_correct _ _ _ buf); [|eassumption].
    rewrite app_comm_cons flattenp_app -!app_assoc //. destruct ab. destruct cd.
    rewrite suffix23_correct prefix23_correct /pair_seq //= !app_comm_cons -!app_assoc//. }
  { rewrite Heq0 Heq1. simp make_small. rewrite Heq. simp make_small kont_seq deque_seq.
    rewrite compose_id_right //= app_nil_r.
    erewrite (prefix_decompose_underflow_correct _ _ prefix1); [|eassumption].
    erewrite (suffix_decompose_ok_correct _ _ suffix1); [|eassumption].
    rewrite prefix23_correct -!app_assoc //.
    epose proof (buffer_uncons_correct _ _ buf) as HH.
    rewrite Heq /option_seq /cons_seq in HH. destruct cd as [c d]. cbn.
    rewrite -HH //. }
  { rewrite Heq0 Heq1. simp make_small. rewrite Heq. simp make_small.
    erewrite (prefix_decompose_underflow_correct _ _ prefix1); [|eassumption].
    erewrite (suffix_decompose_ok_correct _ _ suffix1); [|eassumption].
    rewrite buffer_cons_correct /=.
    epose proof (buffer_uncons_correct _ _ buf) as HH.
    rewrite Heq /= in HH. rewrite -HH //. }
  { rewrite Heq0 Heq1. simp make_small. rewrite Heq. simp make_small kont_seq deque_seq.
    erewrite (prefix_decompose_underflow_correct _ _ prefix1); [|eassumption].
    erewrite (suffix_decompose_ok_correct _ _ suffix1); [|eassumption].
    rewrite compose_id_right //= app_nil_r prefix23_correct -!app_assoc.
    destruct cd as [c d]. cbn.
    epose proof (buffer_uncons_correct _ _ buf) as HH. rewrite Heq in HH.
    cbn in HH. rewrite -HH //. }
  { rewrite Heq0 Heq1. simp make_small. rewrite Heq. simp make_small kont_seq deque_seq.
    erewrite (prefix_decompose_underflow_correct _ _ prefix1); [|eassumption].
    erewrite (suffix_decompose_ok_correct _ _ suffix1); [|eassumption].
    epose proof (buffer_uncons_correct _ _ buf) as HH.
    rewrite Heq /= in HH. rewrite -HH //. }
  { rewrite Heq0 Heq1. simp make_small. rewrite Heq. simp make_small kont_seq deque_seq.
    erewrite (prefix_decompose_ok_correct _ _ prefix1); [|eassumption].
    erewrite (suffix_decompose_underflow_correct _ _ suffix1); [|eassumption].
    epose proof (buffer_unsnoc_correct _ _ buf) as HH.
    rewrite Heq /= in HH. rewrite -HH //.
    rewrite compose_id_right //= app_nil_r !flattenp_app suffix23_correct -!app_assoc//. }
  { rewrite Heq0 Heq1. simp make_small. rewrite Heq. simp make_small kont_seq deque_seq.
    erewrite (prefix_decompose_ok_correct _ _ prefix1); [|eassumption].
    erewrite (suffix_decompose_underflow_correct _ _ suffix1); [|eassumption].
    epose proof (buffer_unsnoc_correct _ _ buf) as HH.
    rewrite Heq /= in HH. rewrite -HH //= buffer_snoc_correct //. }
  { rewrite Heq0 Heq1. simp make_small. rewrite Heq. simp make_small kont_seq deque_seq.
    erewrite (prefix_decompose_ok_correct _ _ prefix1); [|eassumption].
    erewrite (suffix_decompose_underflow_correct _ _ suffix1); [|eassumption].
    epose proof (buffer_unsnoc_correct _ _ buf) as HH.
    rewrite Heq /= in HH. rewrite -HH //= app_nil_r //. }
Qed.

Lemma green_of_red_correct A (k: kont A is_red) :
  kont_seq (green_of_red k) = kont_seq k.
Proof.
  funelim (green_of_red k); simp green_of_red.
  { rewrite make_small_correct. simp kont_seq deque_seq.
    rewrite //= app_nil_r compose_id_right //. }
  { destruct (green_prefix_concat p1 p2) as [p1' [? ? p2']] eqn:Hprefix.
    destruct (green_suffix_concat s2 s1) as [[? ? s2'] s1'] eqn:Hsuffix.
    simp kont_seq deque_seq.
    rewrite //= app_nil_r compose_id_right //.
    destruct (deque_seq child) as [[? ?] ?].
    simp kont_seq deque_seq.
    rewrite !flattenp_app -!app_assoc.
    rewrite (app_assoc (buffer_seq p1)).
    erewrite (green_prefix_concat_correct _ _ p1 p2);[|eassumption].
    rewrite -!app_assoc. f_equal. simp yellow_buffer_seq. do 4 f_equal.
    erewrite green_suffix_concat_correct; eauto. now simp yellow_buffer_seq. }
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
    rewrite -!app_assoc. f_equal. simp yellow_buffer_seq. do 4 f_equal.
    apply suffix_concat_correct in Hsuffix. simp yellow_buffer_seq in Hsuffix.
    rewrite Hsuffix. now simp any_buffer_seq. }
Qed.

Lemma ensure_green_correct A C (ny: not_yellow C) (k: kont A C) :
  kont_seq (ensure_green ny k) = kont_seq k.
Proof.
  funelim (ensure_green ny k); simp ensure_green kont_seq deque_seq; auto.
  rewrite green_of_red_correct. now simp kont_seq.
Qed.

Lemma cons_correct A (x:A) s :
  s_seq (cons x s) = x :: s_seq s.
Proof.
  funelim (cons x s); simp cons s_seq yellow red kont_seq deque_seq.
  { rewrite buffer_cons_correct //. }
  { destruct (deque_seq child) as [[? ?] ?]. simp kont_seq deque_seq.
    rewrite green_prefix_cons_correct. rewrite -!app_assoc -app_comm_cons.
    now rewrite ensure_green_correct. }
  { destruct (yellow_prefix_cons x (Yellowish p1)) as [? ?] eqn:Hprefix.
    simp s_seq red kont_seq. rewrite green_of_red_correct. simp kont_seq deque_seq.
    destruct (deque_seq child) as [[? ?] ?]. simp kont_seq deque_seq.
    rewrite -!app_assoc.
    epose proof (yellow_prefix_cons_correct _ x (Yellowish p1)) as HH.
    rewrite Hprefix in HH. simp any_buffer_seq in HH. rewrite HH.
    rewrite -app_comm_cons. now simp yellow_buffer_seq. }
Qed.

Lemma snoc_correct A s (x:A) :
  s_seq (snoc s x) = s_seq s ++ [x].
Proof.
  funelim (snoc s x); simp snoc s_seq yellow red kont_seq deque_seq.
  { rewrite buffer_snoc_correct //. }
  { destruct (deque_seq child) as [[? ?] ?]. simp kont_seq deque_seq.
    rewrite green_suffix_snoc_correct ensure_green_correct -!app_assoc //. }
  { destruct (yellow_suffix_snoc (Yellowish s1) x) as [? ?] eqn:Hsuffix.
    simp s_seq red kont_seq. rewrite green_of_red_correct. simp kont_seq deque_seq.
    destruct (deque_seq child) as [[? ?] ?]. simp kont_seq deque_seq.
    epose proof (yellow_suffix_snoc_correct _ (Yellowish s1) x) as HH.
    rewrite Hsuffix in HH. simp any_buffer_seq in HH. rewrite HH -!app_assoc //. }
Qed.

Lemma uncons_unsafe_correct A (dq: s A) Hne x dq' :
  uncons_unsafe dq Hne = (x, dq') ->
  s_seq dq = x :: s_seq dq'.
Proof.
  funelim (uncons_unsafe dq Hne); simp uncons_unsafe.
  { destruct (buffer_uncons_unsafe buf _) as [? [? ?]] eqn:Huncons.
    inversion 1; subst. simp s_seq kont_seq.
    erewrite buffer_uncons_unsafe_correct; [|eassumption].
    now simp any_buffer_seq. }
  { destruct (green_uncons p1) as [? [? ? ?]] eqn:Huncons.
    inversion 1; subst. simp s_seq kont_seq yellow.
    destruct (deque_seq (Green p1 child s1)) as [[? ?] ?] eqn:Hdq1.
    simp kont_seq deque_seq.
    destruct (deque_seq child) as [[? ?] ?] eqn:Hdq2.
    simp kont_seq deque_seq.
    rewrite ensure_green_correct.
    simp deque_seq in Hdq1. rewrite Hdq2 in Hdq1.
    simp deque_seq in Hdq1. inversion Hdq1; subst.
    rewrite -!app_assoc. erewrite green_uncons_correct; [|eassumption].
    simp yellow_buffer_seq. rewrite app_comm_cons //. }
  { destruct (yellow_uncons (Yellowish p1)) as [? [? ?]] eqn:Huncons.
    inversion 1; subst. simp s_seq kont_seq deque_seq.
    destruct (deque_seq child) as [[? ?] ?] eqn:Hdq1. simp s_seq kont_seq deque_seq red.
    rewrite green_of_red_correct. simp kont_seq deque_seq. rewrite Hdq1.
    simp kont_seq deque_seq. eapply yellow_uncons_correct in Huncons.
    simp yellow_buffer_seq in Huncons. rewrite Huncons.
    rewrite -!app_assoc -app_comm_cons. now simp any_buffer_seq. }
Qed.
