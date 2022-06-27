From Coq Require Import Program List.
Import ListNotations.
From Equations Require Import Equations.

#[local] Obligation Tactic := try constructor.

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

Inductive s : Type -> Type :=
| T : forall {a G Y},
  kont a (PColor G Y PNotred) ->
  s a.

Equations green_prefix_cons {A : Type} : A -> buffer A is_green -> buffer A is_yellow :=
green_prefix_cons x (B2 a b) := B3 x a b;
green_prefix_cons x (B3 a b c) := B4 x a b c.

Equations green_suffix_snoc {A : Type} : buffer A is_green -> A -> buffer A is_yellow :=
green_suffix_snoc (B2 a b) x := B3 a b x;
green_suffix_snoc (B3 a b c) x := B4 a b c x.

Equations yellow_prefix_cons {A : Type} : A -> yellow_buffer A -> any_buffer A :=
yellow_prefix_cons x (Yellowish buf) with buf => {
  yellow_prefix_cons x _ (B1 a) := Any (B2 x a);
  yellow_prefix_cons x _ (B2 a b) := Any (B3 x a b);
  yellow_prefix_cons x _ (B3 a b c) := Any (B4 x a b c);
  yellow_prefix_cons x _ (B4 a b c d) := Any (B5 x a b c d)
}.

Equations yellow_suffix_snoc {A : Type} : yellow_buffer A -> A -> any_buffer A :=
yellow_suffix_snoc (Yellowish buf) x with buf := {
  yellow_suffix_snoc _ x (B1 a) => Any (B2 a x);
  yellow_suffix_snoc _ x (B2 a b) => Any (B3 a b x);
  yellow_suffix_snoc _ x (B3 a b c) => Any (B4 a b c x);
  yellow_suffix_snoc _ x (B4 a b c d) => Any (B5 a b c d x)
}.

Equations buffer_cons {A : Type} {C: phantom} : A -> buffer A C -> kont A is_green :=
buffer_cons x B0 := Small (B1 x);
buffer_cons x (B1 a) := Small (B2 x a);
buffer_cons x (B2 a b) := Small (B3 x a b);
buffer_cons x (B3 a b c) := Small (B4 x a b c);
buffer_cons x (B4 a b c d) := Small (B5 x a b c d);
buffer_cons x (B5 a b c d e) := G (Green (B3 x a b) HOLE (B3 c d e)) (Small B0).

Equations buffer_snoc {A : Type} {C: phantom} : buffer A C -> A -> kont A is_green :=
buffer_snoc B0 x := Small (B1 x);
buffer_snoc (B1 a) x := Small (B2 a x);
buffer_snoc (B2 a b) x := Small (B3 a b x);
buffer_snoc (B3 a b c) x := Small (B4 a b c x);
buffer_snoc (B4 a b c d) x := Small (B5 a b c d x);
buffer_snoc (B5 a b c d e) x := G (Green (B3 a b c) HOLE (B3 d e x)) (Small B0).

Equations green_uncons {A : Type} : buffer A is_green -> A * yellow_buffer A :=
green_uncons (B2 a b) => (a, (Yellowish (B1 b)));
green_uncons (B3 a b c) => (a, (Yellowish (B2 b c))).

Equations green_unsnoc {A : Type} : buffer A is_green -> yellow_buffer A * A :=
green_unsnoc (B2 a b) => ((Yellowish (B1 a)), b);
green_unsnoc (B3 a b c) => ((Yellowish (B2 a b)), c).

Equations yellow_uncons {A : Type} : yellow_buffer A -> A * any_buffer A :=
yellow_uncons (Yellowish buf) with buf => {
  yellow_uncons _ (B1 a) := (a, Any B0);
  yellow_uncons _ (B2 a b) := (a, Any (B1 b));
  yellow_uncons _ (B3 a b c) := (a, Any (B2 b c));
  yellow_uncons _ (B4 a b c d) := (a, Any (B3 b c d))
}.

Equations yellow_unsnoc {A : Type} : yellow_buffer A -> any_buffer A * A :=
yellow_unsnoc (Yellowish buf) with buf => {
  yellow_unsnoc _ (B1 a) := (Any B0, a);
  yellow_unsnoc _ (B2 a b) := (Any (B1 a), b);
  yellow_unsnoc _ (B3 a b c) := (Any (B2 a b), c);
  yellow_unsnoc _ (B4 a b c d) := (Any (B3 a b c), d)
}.

Equations buffer_uncons {A C} : buffer A C -> option (A * any_buffer A) :=
buffer_uncons B0 := None;
buffer_uncons (B5 a b c d e) := Some (a, Any (B4 b c d e));
buffer_uncons buf := Some (yellow_uncons (Yellowish buf)).

Equations buffer_unsnoc {A C} : buffer A C -> option (any_buffer A * A) :=
buffer_unsnoc B0 := None;
buffer_unsnoc (B5 a b c d e) := Some (Any (B4 a b c d), e);
buffer_unsnoc buf := Some (yellow_unsnoc (Yellowish buf)).

Equations prefix_rot {A C} : A -> buffer A C -> buffer A C * A :=
prefix_rot x B0 := (B0, x);
prefix_rot x (B1 a) := (B1 x, a);
prefix_rot x (B2 a b) := (B2 x a, b);
prefix_rot x (B3 a b c) := (B3 x a b, c);
prefix_rot x (B4 a b c d) := (B4 x a b c, d);
prefix_rot x (B5 a b c d e) := (B5 x a b c d, e).

Equations suffix_rot {A C} : buffer A C -> A -> A * buffer A C :=
suffix_rot B0 x := (x, B0);
suffix_rot (B1 a) x := (a, B1 x);
suffix_rot (B2 a b) x := (a, B2 b x);
suffix_rot (B3 a b c) x := (a, B3 b c x);
suffix_rot (B4 a b c d) x := (a, B4 b c d x);
suffix_rot (B5 a b c d e) x := (a, B5 b c d e x).

Inductive decompose (A : Type) : Type :=
| Underflow : option A -> decompose A
| Ok : buffer A is_green -> decompose A
| Overflow : buffer A is_green -> A * A -> decompose A.

Arguments Underflow {_}.
Arguments Ok {_}.
Arguments Overflow {_}.

Equations prefix_decompose {A C} : buffer A C -> decompose A :=
prefix_decompose B0 := Underflow None;
prefix_decompose (B1 x) := Underflow (Some x);
prefix_decompose (B2 a b) := Ok (B2 a b);
prefix_decompose (B3 a b c) := Ok (B3 a b c);
prefix_decompose (B4 a b c d) := Overflow (B2 a b) (c, d);
prefix_decompose (B5 a b c d e) := Overflow (B3 a b c) (d, e).

Equations suffix_decompose {A C} : buffer A C -> decompose A :=
suffix_decompose B0 := Underflow None;
suffix_decompose (B1 x) := Underflow (Some x);
suffix_decompose (B2 a b) := Ok (B2 a b);
suffix_decompose (B3 a b c) := Ok (B3 a b c);
suffix_decompose (B4 a b c d) := Overflow (B2 c d) (a, b);
suffix_decompose (B5 a b c d e) := Overflow (B3 c d e) (a, b).

Equations prefix23 {A G Y} : option A -> A * A -> buffer A (PColor G Y PNotred) :=
prefix23 None (b, c) := B2 b c;
prefix23 (Some a) (b, c) := B3 a b c.

Equations suffix23 {A G Y} : A * A -> option A -> buffer A (PColor G Y PNotred) :=
suffix23 (a, b) None := B2 a b;
suffix23 (a, b) (Some c) := B3 a b c.

Equations prefix12 {A} : A -> option A -> buffer A is_yellow :=
prefix12 x None := B1 x;
prefix12 x (Some y) := B2 x y.

Equations green_prefix_concat {A C} :
  buffer A C -> buffer (A * A) is_green -> buffer A is_green * yellow_buffer (A * A) :=
green_prefix_concat buf1 buf2 with (prefix_decompose buf1) => {
  green_prefix_concat _ buf2 (Ok buf) => (buf, Yellowish buf2);
  green_prefix_concat _ buf2 (Underflow opt) =>
    let '(ab, buf) := green_uncons buf2 in
    (prefix23 opt ab, buf);
  green_prefix_concat _ buf2 (Overflow buf ab) =>
    (buf, Yellowish (green_prefix_cons ab buf2))
}.

Equations green_suffix_concat {A C} :
  buffer (A * A) is_green -> buffer A C -> yellow_buffer (A * A) * buffer A is_green :=
green_suffix_concat buf1 buf2 with (suffix_decompose buf2) => {
  green_suffix_concat buf1 _ (Ok buf) => (Yellowish buf1, buf);
  green_suffix_concat buf1 _ (Underflow opt) =>
    let '(buf, ab) := green_unsnoc buf1 in
    (buf, (suffix23 ab opt));
  green_suffix_concat buf1 _ (Overflow buf ab) =>
    (Yellowish (green_suffix_snoc buf1 ab), buf)
}.

Equations prefix_concat {A B} :
  buffer A B -> yellow_buffer (A * A) -> buffer A is_green * any_buffer (A * A) :=
prefix_concat buf1 buf2 with prefix_decompose buf1 => {
  prefix_concat _ (Yellowish buf2) (Ok buf) := (buf, Any buf2);
  prefix_concat _ buf2 (Underflow opt) :=
    let '(ab, buf) := yellow_uncons buf2 in
    (prefix23 opt ab, buf);
  prefix_concat _ buf2 (Overflow buf ab) :=
    (buf, yellow_prefix_cons ab buf2)
}.

Equations suffix_concat {A B} :
  yellow_buffer (A * A) -> buffer A B -> any_buffer (A * A) * buffer A is_green :=
suffix_concat _ buf2 with suffix_decompose buf2 => {
  suffix_concat (Yellowish buf1) _ (Ok buf) := (Any buf1, buf);
  suffix_concat buf1 _ (Underflow opt) :=
    let '(buf, ab) := yellow_unsnoc buf1 in
    (buf, suffix23 ab opt);
  suffix_concat buf1 _ (Overflow buf ab) :=
    (yellow_suffix_snoc buf1 ab, buf)
}.

Inductive sandwich (A: Type) : Type :=
| Alone : option A -> sandwich A
| Sandwich {C} : A -> buffer A C -> A -> sandwich A.
Arguments Alone {A}.
Arguments Sandwich {A C}.

Equations buffer_unsandwich {A C} : buffer A C -> sandwich A :=
buffer_unsandwich B0 := Alone None;
buffer_unsandwich (B1 a) := Alone (Some a);
buffer_unsandwich (B2 a b) := Sandwich a B0 b;
buffer_unsandwich (B3 a b c) := Sandwich a (B1 b) c;
buffer_unsandwich (B4 a b c d) := Sandwich a (B2 b c) d;
buffer_unsandwich (B5 a b c d e) := Sandwich a (B3 b c d) e.

Equations buffer_halve {A C} : buffer A C -> option A * any_buffer (A * A) :=
buffer_halve B0 := (None, Any B0);
buffer_halve (B1 a) := (Some a, Any B0);
buffer_halve (B2 a b) := (None, Any (B1 (a, b)));
buffer_halve (B3 a b c) := (Some a, Any (B1 (b, c)));
buffer_halve (B4 a b c d) := (None, Any (B2 (a, b) (c, d)));
buffer_halve (B5 a b c d e) := (Some a, Any (B2 (b, c) (d, e))).

Equations kont_of_opt3 {A} : option A -> option (A * A) -> option A -> kont A is_green :=
kont_of_opt3 None None None := Small B0;
kont_of_opt3 (Some a) None None := Small (B1 a);
kont_of_opt3 None None (Some a) := Small (B1 a);
kont_of_opt3 (Some a) None (Some b) := Small (B2 a b);
kont_of_opt3 None (Some (a, b)) None := Small (B2 a b);
kont_of_opt3 (Some a) (Some (b, c)) None := Small (B3 a b c);
kont_of_opt3 None (Some (a, b)) (Some c) := Small (B3 a b c);
kont_of_opt3 (Some a) (Some (b, c)) (Some d) := Small (B4 a b c d).

Equations make_small {A C1 C2 C3} :
  buffer A C1 ->
  buffer (A * A) C2 ->
  buffer A C3 ->
  kont A is_green :=
make_small prefix1 buf suffix1 with (prefix_decompose prefix1), (suffix_decompose suffix1) => {
make_small _ _ _ (Ok p1) (Ok s1) :=
  G (Green p1 HOLE s1) (Small buf);
make_small _ _ _ (Ok p1) (Underflow opt) with (buffer_unsnoc buf), opt => {
  make_small _ _ _ _ _ None None := Small p1;
  make_small _ _ _ _ _ None (Some x) := buffer_snoc p1 x;
  make_small _ _ _ _ _ (Some (Any rest, cd)) _ :=
    G (Green p1 HOLE (suffix23 cd opt)) (Small rest)
  };
make_small _ _ _ (Underflow opt) (Ok s1) with (buffer_uncons buf), opt => {
  make_small _ _ _ _ _ None None := Small s1;
  make_small _ _ _ _ _ None (Some x) := buffer_cons x s1;
  make_small _ _ _ _ _ (Some (cd, Any rest)) _ :=
    G (Green (prefix23 opt cd) HOLE s1) (Small rest)
  };
make_small _ _ _ (Underflow p1) (Underflow s1) with buffer_unsandwich buf => {
  make_small _ _ _ _ _ (Sandwich ab rest cd) :=
    G (Green (prefix23 p1 ab) HOLE (suffix23 cd s1)) (Small rest);
  make_small _ _ _ _ _ (Alone opt) :=
    kont_of_opt3 p1 opt s1;
 };
make_small _ _ _ (Overflow p1 ab) (Ok s1) :=
  G (Green p1 HOLE s1) (buffer_cons ab buf);
make_small _ _ _ (Ok p1) (Overflow s1 ab) :=
  G (Green p1 HOLE s1) (buffer_snoc buf ab);
make_small _ _ _ (Underflow opt) (Overflow s1 ab) :=
  let '(cd, center) := suffix_rot buf ab in
  G (Green (prefix23 opt cd) HOLE s1) (Small center);
make_small _ _ _ (Overflow p1 ab) (Underflow opt) :=
  let '(center, cd) := prefix_rot ab buf in
  G (Green p1 HOLE (suffix23 cd opt)) (Small center);
make_small _ buf _ (Overflow p1 ab) (Overflow s1 cd) :=
  let '(x, Any rest) := buffer_halve buf in
  G (Green p1 (Yellow (prefix12 ab x) HOLE (B1 cd)) s1) (Small rest)
}.

Equations green_of_red {A : Type} : kont A is_red -> kont A is_green :=
green_of_red (R (Red p1 HOLE s1) (Small buf)) :=
  make_small p1 buf s1;
green_of_red (R (Red p1 (Yellow p2 child s2) s1) k) :=
  let '(p1, Any p2) := prefix_concat p1 (Yellowish p2) in
  let '(Any s2, s1) := suffix_concat (Yellowish s2) s1 in
  G (Green p1 HOLE s1) (R (Red p2 child s2) k);
green_of_red (R (Red p1 HOLE s1) (G (Green p2 child s2) k)) :=
  let '(p1, Yellowish p2) := green_prefix_concat p1 p2 in
  let '(Yellowish s2, s1) := green_suffix_concat s2 s1 in
    G (Green p1 (Yellow p2 child s2) s1) k.

Inductive not_yellow : phantom -> Type :=
| Not_yellow {G R} : not_yellow (PColor G PNotyellow R).

Equations ensure_green {A C} : not_yellow C -> kont A C -> kont A is_green :=
ensure_green Not_yellow (Small buf) := Small buf;
ensure_green Not_yellow (G x k) := G x k;
ensure_green Not_yellow (R x k) := green_of_red (R x k).

Equations yellow {A B: Type} {G1 Y1 Y2 K2 G3 Y3 G4 R4 : phantom} :
  buffer A (PColor G1 Y1 PNotred) ->
  deque (A * A) B (PColor PNotgreen Y2 PNotred) K2 ->
  buffer A (PColor G3 Y3 PNotred) ->
  kont B (PColor G4 PNotyellow R4) ->
  s A
:=
yellow p1 child s1 k := T (Y (Yellow p1 child s1) (ensure_green Not_yellow k)).

Equations red {A B: Type} {C1 Y2 K2 C3 : phantom} :
  buffer A C1 ->
  deque (A * A) B (PColor PNotgreen Y2 PNotred) K2 ->
  buffer A C3 ->
  kont B is_green ->
  s A
:=
red p1 child s1 k := T (green_of_red (R (Red p1 child s1) k)).

Module S.

Equations cons {A: Type} : A -> s A -> s A :=
cons x (T (Small buf)) :=
  T (buffer_cons x buf);
cons x (T (G (Green p1 child s1) kont)) :=
  yellow (green_prefix_cons x p1) child s1 kont;
cons x (T (Y (Yellow p1 child s1) kont)) :=
  let 'Any p1 := yellow_prefix_cons x (Yellowish p1) in
  red p1 child s1 kont.

Equations snoc {A: Type} : s A -> A -> s A :=
snoc (T (Small buf)) x :=
  T (buffer_snoc buf x);
snoc (T (G (Green p1 child s1) k)) x :=
  yellow p1 child (green_suffix_snoc s1 x) k;
snoc (T (Y (Yellow p1 child s1) k)) x :=
  let 'Any s1 := yellow_suffix_snoc (Yellowish s1) x in
  red p1 child s1 k.

Equations uncons {A: Type} (dq: s A) : option (A * s A) :=
uncons (T (Small buf)) with (buffer_uncons buf) => {
  uncons _ None := None;
  uncons _ (Some (x, Any buf')) := Some (x, T (Small buf'))
};
uncons (T (G (Green p1 child s1) k)) :=
  let '(x, Yellowish p1) := green_uncons p1 in
  Some (x, yellow p1 child s1 k);
uncons (T (Y (Yellow p1 child s1) k)) :=
  let '(x, Any p1) := yellow_uncons (Yellowish p1) in
  Some (x, red p1 child s1 k).

Equations unsnoc {A : Type} (dq: s A) : option (s A * A) :=
unsnoc (T (Small buf)) with (buffer_unsnoc buf) => {
  unsnoc _ None := None;
  unsnoc _ (Some (Any buf', x)) := Some (T (Small buf'), x)
};
unsnoc (T (G (Green p1 child s1) k)) :=
  let '(Yellowish s1, x) := green_unsnoc s1 in
  Some (yellow p1 child s1 k, x);
unsnoc (T (Y (Yellow p1 child s1) k)) :=
  let '(Any s1, x) := yellow_unsnoc (Yellowish s1) in
  Some (red p1 child s1 k, x).

End S.
