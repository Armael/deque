From Coq Require Import ssreflect.
From Coq Require Import Program List ZArith Lia.
Import ListNotations.
From Equations Require Import Equations.
Open Scope Z_scope.
From Hammer Require Import Tactics.

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

#[local] Obligation Tactic :=
  try first [ done | hauto db:rlist ].

(* Types *)

Inductive phantom : Type :=
  | PGreen
  | PNotgreen
  | PYellow
  | PNotyellow
  | PRed
  | PNotred
  | PKont
  | PNotkont
  | PColor : phantom -> phantom -> phantom -> phantom.

Derive NoConfusion for phantom.

Notation is_green := (PColor PGreen PNotyellow PNotred).
Notation is_yellow := (PColor PNotgreen PYellow PNotred).
Notation is_red := (PColor PNotgreen PNotyellow PRed).

Inductive buffer : Type -> phantom -> Type :=
| B0 : forall {a : Type}, buffer a is_red
| B1 : forall {a : Type}, a -> buffer a is_yellow
| B2 : forall {a: Type} {G Y : phantom},
  a -> a -> buffer a (PColor G Y PNotred)
| B3 : forall {a : Type} {G Y : phantom},
  a -> a -> a -> buffer a (PColor G Y PNotred)
| B4 : forall {a : Type},
  a -> a -> a -> a -> buffer a is_yellow
| B5 : forall {a : Type},
  a -> a -> a -> a -> a -> buffer a is_red.

Inductive yellow_buffer (A: Type) : Type :=
| Yellowish : forall {G Y},
  buffer A (PColor G Y PNotred) ->
  yellow_buffer A.
Arguments Yellowish {A G Y}.

Inductive any_buffer (A: Type) : Type :=
| Any : forall {C}, buffer A C -> any_buffer A.
Arguments Any {A C}.

Inductive deque : Type -> Type -> phantom -> phantom -> Type :=
| HOLE : forall {a : Type},
  deque a a (PColor PNotgreen PNotyellow PNotred) PKont
| Yellow : forall {a b : Type} {G1 Y1 Y2 K G3 Y3},
  buffer a (PColor G1 Y1 PNotred) ->
  deque (a * a) b (PColor PNotgreen Y2 PNotred) K ->
  buffer a (PColor G3 Y3 PNotred) ->
  deque a b is_yellow PNotkont
| Green : forall {a b : Type} {Y K},
  buffer a is_green ->
  deque (a * a) b (PColor PNotgreen Y PNotred) K ->
  buffer a is_green ->
  deque a b is_green PNotkont
| Red : forall {a b : Type} {C Y K CC},
  buffer a C ->
  deque (a * a) b (PColor PNotgreen Y PNotred) K ->
  buffer a CC ->
  deque a b is_red PNotkont.

Inductive kont : Type -> phantom -> Type :=
| Small : forall {a C},
  buffer a C -> kont a is_green
| G : forall {a b G R},
  deque a b is_green PNotkont ->
  kont b (PColor G PNotyellow R) ->
  kont a is_green
| Y : forall {a b : Type},
  deque a b is_yellow PNotkont ->
  kont b is_green ->
  kont a is_yellow
| R : forall {a b : Type},
  deque a b is_red PNotkont ->
  kont b is_green ->
  kont a is_red.

Inductive decompose (A : Type) : Type :=
| Underflow : option A -> decompose A
| Ok : buffer A is_green -> decompose A
| Overflow : buffer A is_green -> A * A -> decompose A.

Arguments Underflow {_}.
Arguments Ok {_}.
Arguments Overflow {_}.

Inductive sandwich (A : Type) : Type :=
| Alone : option A -> sandwich A
| Sandwich {C} : A -> buffer A C -> A -> sandwich A.
Arguments Alone {A}.
Arguments Sandwich {A C}.

Inductive not_yellow : phantom -> Type :=
| Not_yellow {G R} : not_yellow (PColor G PNotyellow R).

Inductive s : Type -> Type :=
| T : forall {a G Y},
  kont a (PColor G Y PNotred) ->
  s a.

(* Models *)

Set Equations Transparent.

Equations option_seq {A} : option A -> list A :=
option_seq None := [];
option_seq (Some x) := [x].

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

Equations deque_front_seq {A B C K} : deque A B C K -> list A :=
deque_front_seq HOLE := [];
deque_front_seq (Yellow buf1 dq _) :=
  buffer_seq buf1 ++ flattenp (deque_front_seq dq);
deque_front_seq (Green buf1 dq _) :=
  buffer_seq buf1 ++ flattenp (deque_front_seq dq);
deque_front_seq (Red buf1 dq _) :=
  buffer_seq buf1 ++ flattenp (deque_front_seq dq).

Equations deque_rear_seq {A B C K} : deque A B C K -> list A :=
deque_rear_seq HOLE := [];
deque_rear_seq (Yellow _ dq buf2) :=
  flattenp (deque_rear_seq dq) ++ buffer_seq buf2;
deque_rear_seq (Green _ dq buf2) :=
  flattenp (deque_rear_seq dq) ++ buffer_seq buf2;
deque_rear_seq (Red _ dq buf2) :=
  flattenp (deque_rear_seq dq) ++ buffer_seq buf2.

Equations deque_hole_flatten {A B C K} : deque A B C K -> list B -> list A :=
deque_hole_flatten HOLE := id;
deque_hole_flatten (Yellow _ dq _) :=
  flattenp ∘ deque_hole_flatten dq;
deque_hole_flatten (Green _ dq _) :=
  flattenp ∘ deque_hole_flatten dq;
deque_hole_flatten (Red _ dq _) :=
  flattenp ∘ deque_hole_flatten dq.

Equations kont_seq {A C} : kont A C -> list A :=
kont_seq (Small buf) := buffer_seq buf;
kont_seq (G dq kont) :=
  deque_front_seq dq ++
  deque_hole_flatten dq (kont_seq kont) ++
  deque_rear_seq dq;
kont_seq (Y dq kont) :=
  deque_front_seq dq ++
  deque_hole_flatten dq (kont_seq kont) ++
  deque_rear_seq dq;
kont_seq (R dq kont) :=
  deque_front_seq dq ++
  deque_hole_flatten dq (kont_seq kont) ++
  deque_rear_seq dq.

Equations decompose_main_seq {A : Type} (dec : decompose A) : list A :=
decompose_main_seq (Underflow None) := [];
decompose_main_seq (Underflow (Some x)) := [x];
decompose_main_seq (Ok b) := buffer_seq b;
decompose_main_seq (Overflow b _) := buffer_seq b.

Equations decompose_rest_seq {A : Type} (dec : decompose A) : list A :=
decompose_rest_seq (Underflow _) := [];
decompose_rest_seq (Ok _) := [];
decompose_rest_seq (Overflow b (x, y)) := [x; y].

Equations sandwich_seq {A : Type} (sw : sandwich A) : list A :=
sandwich_seq (Alone None) := [];
sandwich_seq (Alone (Some x)) := [x];
sandwich_seq (Sandwich x b y) := x :: buffer_seq b ++ [y].

Equations s_seq {A} : s A -> list A :=
s_seq (T kont) := kont_seq kont.

Unset Equations Transparent.

(* Functions *)

Notation "? x" := (@exist _ _ x _) (at level 100).

Equations green_prefix_cons {A : Type} (x : A) (b : buffer A is_green) :
  { b' : buffer A is_yellow | buffer_seq b' = x :: buffer_seq b } :=
green_prefix_cons x (B2 a b) := ? B3 x a b;
green_prefix_cons x (B3 a b c) := ? B4 x a b c.

Equations green_suffix_snoc {A : Type} (b : buffer A is_green) (x : A) :
  { b' : buffer A is_yellow | buffer_seq b' = buffer_seq b ++ [x] } :=
green_suffix_snoc (B2 a b) x := ? B3 a b x;
green_suffix_snoc (B3 a b c) x := ? B4 a b c x.

#[derive(eliminator=no)]
Equations yellow_prefix_cons {A : Type} (x : A) (b : yellow_buffer A) :
  { b' : any_buffer A | any_buffer_seq b' = x :: yellow_buffer_seq b } :=
yellow_prefix_cons x (Yellowish buf) with buf => {
  | B1 a => ? Any (B2 x a);
  | B2 a b => ? Any (B3 x a b);
  | B3 a b c => ? Any (B4 x a b c);
  | B4 a b c d => ? Any (B5 x a b c d)
}.

#[derive(eliminator=no)]
Equations yellow_suffix_snoc {A : Type} (b : yellow_buffer A) (x : A) :
  { b' : any_buffer A | any_buffer_seq b' = yellow_buffer_seq b ++ [x] } :=
yellow_suffix_snoc (Yellowish buf) x with buf := {
  | B1 a => ? Any (B2 a x);
  | B2 a b => ? Any (B3 a b x);
  | B3 a b c => ? Any (B4 a b c x);
  | B4 a b c d => ? Any (B5 a b c d x)
}.

Equations buffer_cons {A : Type} {C : phantom} (x : A) (b : buffer A C) :
  { k : kont A is_green | kont_seq k = x :: buffer_seq b } :=
buffer_cons x B0 := ? Small (B1 x);
buffer_cons x (B1 a) := ? Small (B2 x a);
buffer_cons x (B2 a b) := ? Small (B3 x a b);
buffer_cons x (B3 a b c) := ? Small (B4 x a b c);
buffer_cons x (B4 a b c d) := ? Small (B5 x a b c d);
buffer_cons x (B5 a b c d e) := ? G (Green (B3 x a b) HOLE (B3 c d e)) (Small B0).

Equations buffer_snoc {A : Type} {C : phantom} (b : buffer A C) (x : A) :
  { k : kont A is_green | kont_seq k = buffer_seq b ++ [x] } :=
buffer_snoc B0 x := ? Small (B1 x);
buffer_snoc (B1 a) x := ? Small (B2 a x);
buffer_snoc (B2 a b) x := ? Small (B3 a b x);
buffer_snoc (B3 a b c) x := ? Small (B4 a b c x);
buffer_snoc (B4 a b c d) x := ? Small (B5 a b c d x);
buffer_snoc (B5 a b c d e) x := ? G (Green (B3 a b c) HOLE (B3 d e x)) (Small B0).

Equations green_uncons {A : Type} (b : buffer A is_green) :
  { '(x, b') : A * yellow_buffer A | buffer_seq b = x :: yellow_buffer_seq b' } :=
green_uncons (B2 a b) => ? (a, (Yellowish (B1 b)));
green_uncons (B3 a b c) => ? (a, (Yellowish (B2 b c))).

Equations green_unsnoc {A : Type} (b : buffer A is_green) :
  { '(b', x) : yellow_buffer A * A | buffer_seq b = yellow_buffer_seq b' ++ [x] } :=
green_unsnoc (B2 a b) => ? ((Yellowish (B1 a)), b);
green_unsnoc (B3 a b c) => ? ((Yellowish (B2 a b)), c).

#[derive(eliminator=no)]
Equations yellow_uncons {A : Type} (b : yellow_buffer A) :
  { '(x, b') : A * any_buffer A | yellow_buffer_seq b = x :: any_buffer_seq b' } :=
yellow_uncons (Yellowish buf) with buf => {
  | B1 a => ? (a, Any B0);
  | B2 a b => ? (a, Any (B1 b));
  | B3 a b c => ? (a, Any (B2 b c));
  | B4 a b c d => ? (a, Any (B3 b c d))
}.

#[derive(eliminator=no)]
Equations yellow_unsnoc {A : Type} (b : yellow_buffer A) :
  { '(b', x) : any_buffer A * A | yellow_buffer_seq b = any_buffer_seq b' ++ [x] } :=
yellow_unsnoc (Yellowish buf) with buf => {
  | B1 a => ? (Any B0, a);
  | B2 a b => ? (Any (B1 a), b);
  | B3 a b c => ? (Any (B2 a b), c);
  | B4 a b c d => ? (Any (B3 a b c), d)
}.

Equations buffer_uncons {A C} (b : buffer A C) :
  { o : option (A * any_buffer A) |
    buffer_seq b =
    match o with
    | None => []
    | Some (x, b') => x :: any_buffer_seq b'
    end } :=
buffer_uncons B0 := ? None;
buffer_uncons (B5 a b c d e) := ? Some (a, Any (B4 b c d e));
buffer_uncons buf with yellow_uncons (Yellowish buf) => { | ? o := ? Some o }.

Equations buffer_unsnoc {A C} (b : buffer A C) :
  { o : option (any_buffer A * A) |
    buffer_seq b =
    match o with
    | None => []
    | Some (b', x) => any_buffer_seq b' ++ [x]
    end } :=
buffer_unsnoc B0 := ? None;
buffer_unsnoc (B5 a b c d e) := ? Some (Any (B4 a b c d), e);
buffer_unsnoc buf with yellow_unsnoc (Yellowish buf) => { | ? o := ? Some o }.

Equations prefix_rot {A C} (x : A) (b : buffer A C) :
  { '(b', y) : buffer A C * A | x :: buffer_seq b = buffer_seq b' ++ [y] } :=
prefix_rot x B0 := ? (B0, x);
prefix_rot x (B1 a) := ? (B1 x, a);
prefix_rot x (B2 a b) := ? (B2 x a, b);
prefix_rot x (B3 a b c) := ? (B3 x a b, c);
prefix_rot x (B4 a b c d) := ? (B4 x a b c, d);
prefix_rot x (B5 a b c d e) := ? (B5 x a b c d, e).

Equations suffix_rot {A C} (b : buffer A C) (y : A) :
  { '(x, b') : A * buffer A C | buffer_seq b ++ [y] = x :: buffer_seq b' } :=
suffix_rot B0 x := ? (x, B0);
suffix_rot (B1 a) x := ? (a, B1 x);
suffix_rot (B2 a b) x := ? (a, B2 b x);
suffix_rot (B3 a b c) x := ? (a, B3 b c x);
suffix_rot (B4 a b c d) x := ? (a, B4 b c d x);
suffix_rot (B5 a b c d e) x := ? (a, B5 b c d e x).

Equations prefix_decompose {A C} (b : buffer A C) :
  { dec : decompose A | buffer_seq b = decompose_main_seq dec ++ decompose_rest_seq dec } :=
prefix_decompose B0 := ? Underflow None;
prefix_decompose (B1 x) := ? Underflow (Some x);
prefix_decompose (B2 a b) := ? Ok (B2 a b);
prefix_decompose (B3 a b c) := ? Ok (B3 a b c);
prefix_decompose (B4 a b c d) := ? Overflow (B2 a b) (c, d);
prefix_decompose (B5 a b c d e) := ? Overflow (B3 a b c) (d, e).

Equations suffix_decompose {A C} (b : buffer A C) :
  { dec : decompose A | buffer_seq b = decompose_rest_seq dec ++ decompose_main_seq dec } :=
suffix_decompose B0 := ? Underflow None;
suffix_decompose (B1 x) := ? Underflow (Some x);
suffix_decompose (B2 a b) := ? Ok (B2 a b);
suffix_decompose (B3 a b c) := ? Ok (B3 a b c);
suffix_decompose (B4 a b c d) := ? Overflow (B2 c d) (a, b);
suffix_decompose (B5 a b c d e) := ? Overflow (B3 c d e) (a, b).

Equations prefix23 {A G Y} (o : option A) (p: A * A) :
  { b : buffer A (PColor G Y PNotred) |
    let '(y, z) := p in
    buffer_seq b = option_seq o ++ [y; z] } :=
prefix23 None (b, c) := ? B2 b c;
prefix23 (Some a) (b, c) := ? B3 a b c.

Equations suffix23 {A G Y} (p : A * A) (o : option A) :
  { b : buffer A (PColor G Y PNotred) |
    let '(x, y) := p in
    buffer_seq b = [x; y] ++ option_seq o } :=
suffix23 (a, b) None := ? B2 a b;
suffix23 (a, b) (Some c) := ? B3 a b c.

Equations prefix12 {A} (x : A) (o : option A) :
  { b : buffer A is_yellow | buffer_seq b = x :: option_seq o } :=
prefix12 x None := ? B1 x;
prefix12 x (Some y) := ? B2 x y.

Equations green_prefix_concat {A C}
  (buf1 : buffer A C)
  (buf2 : buffer (A * A) is_green) :
  { '(buf1', buf2') : buffer A is_green * yellow_buffer (A * A) |
    buffer_seq buf1 ++ flattenp (buffer_seq buf2) =
    buffer_seq buf1' ++ flattenp (yellow_buffer_seq buf2') } :=
green_prefix_concat buf1 buf2 with prefix_decompose buf1 => {
  | (? Ok buf) => ? (buf, Yellowish buf2);
  | (? Underflow opt) with green_uncons buf2 => {
    | (? (ab, buf)) =>
        let '(? prefix) := prefix23 opt ab in
        ? (prefix, buf) };
  | (? Overflow buf ab) =>
    let '(? suffix) := green_prefix_cons ab buf2 in
    ? (buf, Yellowish suffix)
}.

Equations green_suffix_concat {A C}
  (buf1 : buffer (A * A) is_green)
  (buf2 : buffer A C) :
  { '(buf1', buf2') : yellow_buffer (A * A) * buffer A is_green |
    flattenp (buffer_seq buf1) ++ buffer_seq buf2 =
    flattenp (yellow_buffer_seq buf1') ++ buffer_seq buf2' } :=
green_suffix_concat buf1 buf2 with suffix_decompose buf2 => {
  | ? Ok buf => ? (Yellowish buf1, buf);
  | ? Underflow opt with green_unsnoc buf1 => {
    | ? (buf, ab) =>
        let '(? suffix) := suffix23 ab opt in
        ? (buf, suffix) };
  | ? Overflow buf ab =>
    let '(? prefix) := green_suffix_snoc buf1 ab in
    ? (Yellowish prefix, buf)
}.

Equations prefix_concat {A B}
  (buf1 : buffer A B)
  (buf2 : yellow_buffer (A * A)) :
  { '(buf1', buf2') : buffer A is_green * any_buffer (A * A) |
    buffer_seq buf1 ++ flattenp (yellow_buffer_seq buf2) =
    buffer_seq buf1' ++ flattenp (any_buffer_seq buf2') } :=
prefix_concat buf1 buf2 with prefix_decompose buf1 => {
  | ? (Ok buf) =>
    let '(Yellowish buf2) := buf2 in
    ? (buf, Any buf2);
  | ? (Underflow opt) with yellow_uncons buf2 => {
    | ? (ab, buf) =>
      let '(? prefix) := prefix23 opt ab in
      ? (prefix, buf) };
  | ? (Overflow buf ab) =>
    let '(? suffix) := yellow_prefix_cons ab buf2 in
    ? (buf, suffix)
}.

Equations suffix_concat {A B}
  (buf1 : yellow_buffer (A * A))
  (buf2 : buffer A B) :
  { '(buf1', buf2') : any_buffer (A * A) * buffer A is_green |
    flattenp (yellow_buffer_seq buf1) ++ buffer_seq buf2 =
    flattenp (any_buffer_seq buf1') ++ buffer_seq buf2' } :=
suffix_concat buf1 buf2 with suffix_decompose buf2 => {
  | ? (Ok buf) =>
    let '(Yellowish buf1) := buf1 in
    ? (Any buf1, buf);
  | ? (Underflow opt) with yellow_unsnoc buf1 => {
    | ? (buf, ab) =>
      let '(? suffix) := suffix23 ab opt in
      ? (buf, suffix) };
  | ? (Overflow buf ab) =>
    let '(? prefix) := yellow_suffix_snoc buf1 ab in
    ? (prefix, buf)
}.

Equations buffer_unsandwich {A C} (b : buffer A C) :
  { sw : sandwich A | buffer_seq b = sandwich_seq sw } :=
buffer_unsandwich B0 := ? Alone None;
buffer_unsandwich (B1 a) := ? Alone (Some a);
buffer_unsandwich (B2 a b) := ? Sandwich a B0 b;
buffer_unsandwich (B3 a b c) := ? Sandwich a (B1 b) c;
buffer_unsandwich (B4 a b c d) := ? Sandwich a (B2 b c) d;
buffer_unsandwich (B5 a b c d e) := ? Sandwich a (B3 b c d) e.

Equations buffer_halve {A C} (b : buffer A C) :
  { '(o, b') : option A * any_buffer (A * A) |
    buffer_seq b = option_seq o ++ flattenp (any_buffer_seq b') } :=
buffer_halve B0 := ? (None, Any B0);
buffer_halve (B1 a) := ? (Some a, Any B0);
buffer_halve (B2 a b) := ? (None, Any (B1 (a, b)));
buffer_halve (B3 a b c) := ? (Some a, Any (B1 (b, c)));
buffer_halve (B4 a b c d) := ? (None, Any (B2 (a, b) (c, d)));
buffer_halve (B5 a b c d e) := ? (Some a, Any (B2 (b, c) (d, e))).

Equations kont_of_opt3 {A} (o1 : option A) (o2 : option (A * A)) (o3 : option A) :
  { k : kont A is_green |
    kont_seq k = option_seq o1 ++ flattenp (option_seq o2) ++ option_seq o3 } :=
kont_of_opt3 None None None := ? Small B0;
kont_of_opt3 (Some a) None None := ? Small (B1 a);
kont_of_opt3 None None (Some a) := ? Small (B1 a);
kont_of_opt3 (Some a) None (Some b) := ? Small (B2 a b);
kont_of_opt3 None (Some (a, b)) None := ? Small (B2 a b);
kont_of_opt3 (Some a) (Some (b, c)) None := ? Small (B3 a b c);
kont_of_opt3 None (Some (a, b)) (Some c) := ? Small (B3 a b c);
kont_of_opt3 (Some a) (Some (b, c)) (Some d) := ? Small (B4 a b c d).

Equations make_small {A C1 C2 C3}
  (b1 : buffer A C1)
  (b2 : buffer (A * A) C2)
  (b3 : buffer A C3) :
  { k : kont A is_green |
    kont_seq k = buffer_seq b1 ++ flattenp (buffer_seq b2) ++ buffer_seq b3 } :=
make_small prefix1 buf suffix1 with (prefix_decompose prefix1), (suffix_decompose suffix1) => {
  | (? Ok p1), (? Ok s1) :=
    ? G (Green p1 HOLE s1) (Small buf);
  | (? Ok p1), (? Underflow opt) with buffer_unsnoc buf => {
    | ? None with opt => {
      | None := ? Small p1;
      | Some x with buffer_snoc p1 x => { | ? k := ? k } };
    | ? Some (Any rest, cd) with suffix23 cd opt => {
      | ? suffix := ? G (Green p1 HOLE suffix) (Small rest) }
  };
  | (? Underflow opt), (? Ok s1) with buffer_uncons buf => {
    | ? None with opt => {
      | None := ? Small s1;
      | Some x with buffer_cons x s1 => { | ? k := ? k } };
    | ? Some (cd, Any rest) with prefix23 opt cd => {
      | ? prefix := ? G (Green prefix HOLE s1) (Small rest) }
  };
  | (? Underflow p1), (? Underflow s1) with buffer_unsandwich buf => {
    | ? Sandwich ab rest cd with prefix23 p1 ab, suffix23 cd s1 => {
      | ? prefix, ? suffix := ? G (Green prefix HOLE suffix) (Small rest) };
    | ? Alone opt with kont_of_opt3 p1 opt s1 => { | ? k := ? k } }
  | (? Overflow p1 ab), (? Ok s1) with buffer_cons ab buf => {
    | ? rest => ? G (Green p1 HOLE s1) rest };
  | (? Ok p1), (? Overflow s1 ab) with buffer_snoc buf ab => {
    | ? rest => ? G (Green p1 HOLE s1) rest };
  | (? Underflow opt), (? Overflow s1 ab) with suffix_rot buf ab => {
    | ? (cd, center) with prefix23 opt cd => {
      | ? prefix => ? G (Green prefix HOLE s1) (Small center) } };
  | (? Overflow p1 ab), (? Underflow opt) with prefix_rot ab buf => {
    | ? (center, cd) with suffix23 cd opt => {
      | ? suffix => ? G (Green p1 HOLE suffix) (Small center) } };
  | (? Overflow p1 ab), (? Overflow s1 cd) with buffer_halve buf => {
    | ? (x, Any rest) with prefix12 ab x => {
      | ? prefix => ? G (Green p1 (Yellow prefix HOLE (B1 cd)) s1) (Small rest) } }
}.
Next Obligation.
  cbn. intros * Hpre1 * Hcenter%(f_equal flattenp) Hsuff * Hpre.
  destruct ab; destruct cd; autorewrite with rlist in *; cbn in *.
  rewrite Hpre. autorewrite with rlist; cbn.
  rewrite (_ : forall l1 x y l2, x :: y :: l1 ++ l2 = (x :: y :: l1) ++ l2) //.
  rewrite -Hcenter. hauto db:rlist.
Qed.
Next Obligation.
  cbn. intros * Hpre1 * Hcenter%(f_equal flattenp) * Hsuff1 * Hsuff.
  destruct ab; destruct cd; autorewrite with rlist in *; cbn in *.
  rewrite Hpre1. autorewrite with rlist; cbn.
  rewrite (_ : forall l1 x y l2, x :: y :: l1 ++ l2 = (x :: y :: l1) ++ l2) //.
  rewrite Hcenter. hauto db:rlist.
Qed.

Equations green_of_red {A : Type} (k : kont A is_red) :
  { k' : kont A is_green | kont_seq k' = kont_seq k } :=
green_of_red (R (Red p1 HOLE s1) (Small buf)) with make_small p1 buf s1 => {
  | ? k' := ? k' };
green_of_red (R (Red p1 (Yellow p2 child s2) s1) k)
  with prefix_concat p1 (Yellowish p2), suffix_concat (Yellowish s2) s1 => {
  | ? (p1', Any p2'), ? (Any s2', s1') :=
    ? G (Green p1' HOLE s1') (R (Red p2' child s2') k) };
green_of_red (R (Red p1 HOLE s1) (G (Green p2 child s2) k))
  with green_prefix_concat p1 p2, green_suffix_concat s2 s1 => {
  | ? (p1', Yellowish p2'), ? (Yellowish s2', s1') :=
    ? G (Green p1' (Yellow p2' child s2') s1') k }.
Next Obligation.
  cbn. intros * H1 * H2 *. autorewrite with rlist.
  rewrite !app_assoc H1. hauto db:rlist.
Qed.
Next Obligation.
  cbn. intros * H1 * H2 *. autorewrite with rlist.
  rewrite !app_assoc H1. hauto db:rlist.
Qed.

Equations ensure_green {A C} (ny: not_yellow C) (k : kont A C) :
  { k' : kont A is_green | kont_seq k' = kont_seq k } :=
ensure_green Not_yellow (Small buf) := ? Small buf;
ensure_green Not_yellow (G x k) := ? G x k;
ensure_green Not_yellow (R x k) := green_of_red (R x k).

Equations yellow {A B: Type} {G1 Y1 Y2 K2 G3 Y3 G4 R4 : phantom}
  (buf1 : buffer A (PColor G1 Y1 PNotred))
  (dq : deque (A * A) B (PColor PNotgreen Y2 PNotred) K2)
  (buf2 : buffer A (PColor G3 Y3 PNotred))
  (k : kont B (PColor G4 PNotyellow R4)) :
  { sq : s A |
    s_seq sq = buffer_seq buf1 ++
               flattenp (deque_front_seq dq) ++
               flattenp (deque_hole_flatten dq (kont_seq k)) ++
               flattenp (deque_rear_seq dq) ++
               buffer_seq buf2 }
:=
yellow p1 child s1 k with ensure_green Not_yellow k => {
  | ? k' => ? T (Y (Yellow p1 child s1) k') }.

Equations red {A B: Type} {C1 Y2 K2 C3 : phantom}
  (buf1 : buffer A C1)
  (dq : deque (A * A) B (PColor PNotgreen Y2 PNotred) K2)
  (buf2 : buffer A C3)
  (k : kont B is_green) :
  { sq : s A |
    s_seq sq = buffer_seq buf1 ++
               flattenp (deque_front_seq dq) ++
               flattenp (deque_hole_flatten dq (kont_seq k)) ++
               flattenp (deque_rear_seq dq) ++
               buffer_seq buf2 }
:=
red p1 child s1 k with green_of_red (R (Red p1 child s1) k) => {
  | ? k' => ? T k' }.

Module S.

Equations cons {A: Type} (x : A) (sq : s A) :
  { sq' : s A | s_seq sq' = x :: s_seq sq }
:=
cons x (T (Small buf)) with buffer_cons x buf => {
  | ? buf' => ? T buf' };
cons x (T (G (Green p1 child s1) kont)) with green_prefix_cons x p1 => {
  | ? buf' with yellow buf' child s1 kont => {
    | ? sq' => ? sq' } };
cons x (T (Y (Yellow p1 child s1) kont))
  with yellow_prefix_cons x (Yellowish p1) => {
  | ? (Any p1') with red p1' child s1 kont => {
    | ? sq' => ? sq' } }.

Equations snoc {A: Type} (sq : s A) (x : A) :
  { sq' : s A | s_seq sq' = s_seq sq ++ [x] }
:=
snoc (T (Small buf)) x with buffer_snoc buf x => {
  | ? buf' => ? T buf' };
snoc (T (G (Green p1 child s1) k)) x with green_suffix_snoc s1 x => {
  | ? buf' with yellow p1 child buf' k => {
    | ? sq' => ? sq' } };
snoc (T (Y (Yellow p1 child s1) k)) x
  with yellow_suffix_snoc (Yellowish s1) x => {
  | ? (Any s1') with red p1 child s1' k => {
    | ? sq' => ? sq' } }.

Equations uncons {A: Type} (sq : s A) :
  { o : option (A * s A) |
    s_seq sq = match o with
               | None => []
               | Some (x, sq') => x :: s_seq sq'
               end } :=
uncons (T (Small buf)) with buffer_uncons buf => {
  uncons _ (? None) := ? None;
  uncons _ (? Some (x, Any buf')) := ? Some (x, T (Small buf'))
};
uncons (T (G (Green p1 child s1) k)) with green_uncons p1 => {
  | ? (x, Yellowish p1') with yellow p1' child s1 k => {
    | ? sq' => ? Some (x, sq') } };
uncons (T (Y (Yellow p1 child s1) k)) with yellow_uncons (Yellowish p1) => {
  | ? (x, Any p1') with red p1' child s1 k => {
    | ? sq' => ? Some (x, sq') } }.

Equations unsnoc {A : Type} (sq : s A) :
  { o : option (s A * A) |
    s_seq sq = match o with
               | None => []
               | Some (sq', x) => s_seq sq' ++ [x]
               end } :=
unsnoc (T (Small buf)) with buffer_unsnoc buf => {
  unsnoc _ (? None) := ? None;
  unsnoc _ (? Some (Any buf', x)) := ? Some (T (Small buf'), x)
};
unsnoc (T (G (Green p1 child s1) k)) with green_unsnoc s1 => {
  | ? (Yellowish s1', x) with yellow p1 child s1' k => {
    | ? sq' => ? Some (sq', x) } };
unsnoc (T (Y (Yellow p1 child s1) k)) with yellow_unsnoc (Yellowish s1) => {
  | ? (Any s1', x) with red p1 child s1' k => {
    | ? sq' => ? Some (sq', x) } }.

End S.

(* Final structure wrapping everything *)

(* There might be a better setup for the definitions; currently the proofs are
   fairly tedious... *)

Record t (A: Type) : Type := {
  tlength : Z;
  tseq : s A;
  tlength_inv : Z.abs_nat tlength = length (s_seq tseq);
}.
Arguments tlength {A}.
Arguments tseq {A}.

Set Equations Transparent.
Equations t_seq {A} : t A -> list A :=
t_seq {| tlength := len; tseq := sq |} with Z_lt_le_dec len 0 => {
  | left _ => rev (s_seq sq)
  | right _ => s_seq sq
}.
Unset Equations Transparent.

Local Ltac case_lt :=
  match goal with |- context [ Z_lt_le_dec ?x ?y ] =>
    destruct (Z_lt_le_dec x y); cbn
  end.

Lemma rev_eq_nil A (l : list A) :
  rev l = [] -> l = [].
Proof.
  intros H%(f_equal (@length _)). cbn in H.
  rewrite rev_length in H. by apply length_zero_iff_nil.
Qed.

Local Ltac simplist :=
  cbn in *;
  repeat match goal with
  | H : 0%nat = length ?l |- _ =>
    symmetry in H; apply length_zero_iff_nil in H; subst
  | H : rev ?l = [] |- _ =>
    apply rev_eq_nil in H; subst
  end.

Equations empty {A} : { sq : t A | t_seq sq = [] } :=
empty := ? {| tlength := 0; tseq := T (Small B0) |}.

Equations is_empty {A} (sq : t A) :
  { b : bool | b = true <-> t_seq sq = [] } :=
is_empty sq := ? (tlength sq =? 0).
Next Obligation.
  cbn. intros *.
  destruct sq as [x s Hlen]. cbn. rewrite Z.eqb_eq. case_lt.
  all: split; [intros -> | intros HH]; simplist; try hauto.
  all: rewrite HH /= in Hlen; hauto.
Qed.

Equations length {A} (sq : t A) :
  { n : Z | n = Z.of_nat (List.length (t_seq sq)) } :=
length sq := ? Z.abs (tlength sq).
Next Obligation.
  intros. destruct sq as [x s Hlen]. cbn.
  case_lt; rewrite ?rev_length; lia.
Qed.

Equations rev {A} (sq : t A) : { sq' : t A | t_seq sq' = rev (t_seq sq) } :=
rev {| tlength := n; tseq := s |} :=
  ? {| tlength := - n; tseq := s |}.
Next Obligation.
  cbn. intros ? n s Hlen.
  case_lt; case_lt; auto; try lia.
  1: by rewrite rev_involutive //.
  assert (n = 0) by lia; subst. simplist; hauto.
Qed.

Equations cons {A} (x : A) (sq : t A) :
  { sq' : t A | t_seq sq' = x :: t_seq sq } :=
cons x {| tlength := n; tseq := s |} with Z_lt_le_dec n 0 => {
  | right _ with S.cons x s => {
    | ? s' => ? {| tlength := n + 1; tseq := s' |} };
  | left _ with S.snoc s x => {
    | ? s' => ? {| tlength := n - 1; tseq := s' |} }
}.
Next Obligation.
  cbn. intros * ? * -> **. rewrite app_length /=. lia.
Qed.
Next Obligation.
  cbn. intros ? ? ? ? ? ? Hseq Hlen *. case_lt.
  { rewrite Hseq rev_unit //. }
  { assert (n = 0) by lia; subst; simplist; hauto. }
Qed.
Next Obligation.
  cbn. intros * ? * Hseq Hlen. rewrite Hseq //=. lia.
Qed.
Next Obligation.
  cbn. intros ? ? ? ? ? ? Hseq Hlen *. case_lt; last hauto.
  { assert (n = 0) by lia; subst; simplist; hauto. }
Qed.

Equations snoc {A} (sq : t A) (x : A) :
  { sq' : t A | t_seq sq' = t_seq sq ++ [x] } :=
snoc {| tlength := n; tseq := s |} x with Z_lt_le_dec n 0 => {
  | right _ with S.snoc s x => {
    | ? s' => ? {| tlength := n + 1; tseq := s' |} };
  | left _ with S.cons x s => {
    | ? s' => ? {| tlength := n - 1; tseq := s' |} }
}.
Next Obligation. cbn. intros * ? * Hlen * ->. cbn. lia. Qed.
Next Obligation.
  cbn. intros ? ? ? ? Hlen ? ? Hseq. case_lt; first hauto.
  assert (n = 0) by lia; subst; simplist; hauto.
Qed.
Next Obligation.
  cbn. intros * ? * Hlen * ->. rewrite app_length /=. lia.
Qed.
Next Obligation.
  cbn. intros ? ? ? ? Hlen ? ? Hseq. case_lt; last hauto.
  assert (n = 0) by lia; subst; simplist; hauto.
Qed.

Equations uncons {A} (sq : t A) :
  { o : option (A * t A) |
    t_seq sq = match o with
               | None => []
               | Some (x, sq') => x :: t_seq sq'
               end } :=
uncons {| tlength := n; tseq := s |} with Z_lt_le_dec n 0 => {
  | right _ with S.uncons s => {
    | ? None => ? None;
    | ? Some (x, s') => ? Some (x, {| tlength := n-1; tseq := s' |})
  };
  | left _ with S.unsnoc s => {
    | ? None => ? None;
    | ? Some (s', x) => ? Some (x, {| tlength := n+1; tseq := s' |})
  }
}.
Next Obligation.
  cbn. intros * ? * Hseq%(f_equal (@List.length _)) Hlen.
  rewrite app_length /= in Hseq. lia.
Qed.
Next Obligation.
  cbn. intros ? ? ? ? ? ? Hseq Hlen. case_lt.
  { rewrite Hseq rev_unit //. }
  { assert (n = -1) by lia; subst; simplist.
    rewrite Hseq rev_unit. rewrite Hseq app_length /= in Hlen.
    assert (0%nat = List.length (s_seq s')) by lia; simplist. hauto. }
Qed.
Next Obligation.
  cbn. intros * ? * Hseq%(f_equal (@List.length _)) Hlen.
  cbn in *. lia.
Qed.
Next Obligation.
  cbn. intros ? ? ? ? ? ? Hseq Hlen. case_lt; last hauto.
  assert (n = 0) by lia; subst; simplist; hauto.
Qed.

Equations unsnoc {A} (sq : t A) :
  { o : option (t A * A) |
    t_seq sq = match o with
               | None => []
               | Some (sq', x) => t_seq sq' ++ [x]
               end } :=
unsnoc {| tlength := n; tseq := s |} with Z_lt_le_dec n 0 => {
  | right _ with S.unsnoc s => {
    | ? None => ? None;
    | ? Some (s', x) => ? Some ({| tlength := n-1; tseq := s' |}, x)
  };
  | left _ with S.uncons s => {
    | ? None => ? None;
    | ? Some (x, s') => ? Some ({| tlength := n+1; tseq := s' |}, x)
  }
}.
Next Obligation.
  cbn. intros * ? * Hseq%(f_equal (@List.length _)) Hlen. hauto.
Qed.
Next Obligation.
  cbn. intros ? ? ? ? ? ? Hseq Hlen. case_lt; first hauto.
  assert (n = -1) by lia; subst; simplist.
  rewrite Hseq /=. rewrite Hseq /= in Hlen.
  assert (0%nat = List.length (s_seq s')) by lia; simplist; hauto.
Qed.
Next Obligation.
  cbn. intros * ? * Hseq%(f_equal (@List.length _)) Hlen.
  rewrite app_length /= in Hseq. lia.
Qed.
Next Obligation.
  cbn. intros ? ? ? ? ? ? Hseq Hlen. case_lt; last hauto.
  assert (n = 0) by lia; subst; simplist. rewrite Hlen in Hseq |-*.
  destruct (s_seq s'); hauto.
Qed.

Definition is_rev {A} (sq : t A) : bool :=
  tlength sq <? 0.
