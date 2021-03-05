include Dequeue_internal

let fold_left
: type a z. (z -> a -> z) -> z -> a s -> z
= fun f z (T t) ->

  let list_of_buffer
  : type b c. (z -> b -> z) -> z -> (b, c) buffer -> z
  = fun f z buf ->
    match buf with
    | B0 -> z
    | B1 a -> f z a
    | B2 (a, b) -> f (f z a) b
    | B3 (a, b, c) -> f (f (f z a) b) c
    | B4 (a, b, c, d) -> f (f (f (f z a) b) c) d
    | B5 (a, b, c, d, e) -> f (f (f (f (f z a) b) c) d) e
  in

  let rec go
  : type b1 b2 c1 c2.
    (z -> b1 -> z) -> z -> (b1, b2, c1) deque -> (b2, c2) kont -> z
  = fun f z deq kont ->
    match deq with
    | HOLE -> go_kont f z kont
    | Yellow (prefix, child, suffix) ->
        let z = list_of_buffer f z prefix in
        let z = go (go_pair f) z child kont in
        list_of_buffer f z suffix
    | Green (prefix, child, suffix) ->
        let z = list_of_buffer f z prefix in
        let z = go (go_pair f) z child kont in
        list_of_buffer f z suffix
    | Red (prefix, child, suffix) ->
        let z = list_of_buffer f z prefix in
        let z = go (go_pair f) z child kont in
        list_of_buffer f z suffix

  and go_pair
  : type b. (z -> b -> z) -> z -> (b * b) -> z
  = fun f z (x, y) -> f (f z x) y

  and go_kont
  : type b c. (z -> b -> z) -> z -> (b, c) kont -> z
  = fun f z kont ->
    match kont with
    | Small buf -> list_of_buffer f z buf
    | Y (child, kont) -> go f z child kont
    | R (child, kont) -> go f z child kont
    | G (child, kont) -> go f z child kont
  in

  go_kont f z t

let fold_right
: type a z. (a -> z -> z) -> a s -> z -> z
= fun f (T t) z ->

  let list_of_buffer
  : type b c. (b -> z -> z) -> (b, c) buffer -> z -> z
  = fun f buf z ->
    match buf with
    | B0 -> z
    | B1 a -> f a z
    | B2 (a, b) -> f a (f b z)
    | B3 (a, b, c) -> f a (f b (f c z))
    | B4 (a, b, c, d) -> f a (f b (f c (f d z)))
    | B5 (a, b, c, d, e) -> f a (f b (f c (f d (f e z))))
  in

  let rec go
  : type b1 b2 c1 c2.
    (b1 -> z -> z) -> (b1, b2, c1) deque -> z -> (b2, c2) kont -> z
  = fun f deq z kont ->
    match deq with
    | HOLE -> go_kont f kont z
    | Yellow (prefix, child, suffix) ->
        let z = list_of_buffer f suffix z in
        let z = go (go_pair f) child z kont in
        list_of_buffer f prefix z
    | Green (prefix, child, suffix) ->
        let z = list_of_buffer f suffix z in
        let z = go (go_pair f) child z kont in
        list_of_buffer f prefix z
    | Red (prefix, child, suffix) ->
        let z = list_of_buffer f suffix z in
        let z = go (go_pair f) child z kont in
        list_of_buffer f prefix z

  and go_pair
  : type b. (b -> z -> z) -> (b * b) -> z -> z
  = fun f (x, y) z -> f x (f y z)

  and go_kont
  : type b c. (b -> z -> z) -> (b, c) kont -> z -> z
  = fun f kont z ->
    match kont with
    | Small buf -> list_of_buffer f buf z
    | Y (child, kont) -> go f child z kont
    | R (child, kont) -> go f child z kont
    | G (child, kont) -> go f child z kont
  in

  go_kont f t z


let fold_left f z t = match t with
  | Is xs -> fold_left f z xs
  | Rev xs -> fold_right (fun x z -> f z x) xs z

and fold_right f t z = match t with
  | Is xs -> fold_right f xs z
  | Rev xs -> fold_left (fun x z -> f z x) z xs


let length
= fun (T t) ->
  let buffer_length
  : type b c. int -> (b, c) buffer -> int
  = fun s -> function
    | B0 -> 0
    | B1 _ -> s
    | B2 _ -> 2 * s
    | B3 _ -> 3 * s
    | B4 _ -> 4 * s
    | B5 _ -> 5 * s
  in
  let rec go
  : type b1 b2 c1 c2.
    int -> int -> (b1, b2, c1) deque -> (b2, c2) kont -> int
  = fun acc s deq kont ->
    match deq with
    | HOLE -> go_kont acc s kont
    | Yellow (prefix, child, suffix) ->
        go_level acc s prefix suffix child kont
    | Green (prefix, child, suffix) ->
        go_level acc s prefix suffix child kont
    | Red (prefix, child, suffix) ->
        go_level acc s prefix suffix child kont
  and go_level
  : type b1 c1 c2 c3 d3 d4.
       int
    -> int
    -> (b1, c1) buffer
    -> (b1, c2) buffer
    -> (b1 * b1, c3, d3) deque
    -> (c3, d4) kont
    -> int
  = fun acc s prefix suffix child kont ->
    let acc =
      acc
      + buffer_length s prefix
      + buffer_length s suffix in
    go acc (2 * s) child kont
  and go_kont
  : type b c. int -> int -> (b, c) kont -> int
  = fun acc s -> function
    | Small buf -> acc + buffer_length s buf
    | Y (child, kont) -> go acc s child kont
    | R (child, kont) -> go acc s child kont
    | G (child, kont) -> go acc s child kont
  in
  go_kont 0 1 t

let length = function
  | Is  t -> length t
  | Rev t -> length t


let rec of_list
: type a. a list -> (a, [`green]) kont
= function
  | [] -> Small B0
  | [a] -> Small (B1 a)
  | [a ; b] -> Small (B2 (a, b))
  | [a ; b ; c] -> Small (B3 (a, b, c))
  | a :: b :: c :: d :: lst ->
      let p = B2 (a, b) in
      let rec go acc = function
        | c, d, [] -> acc, B2 (c, d)
        | c, d, e :: [] -> acc, B3 (c, d, e)
        | c, d, e :: f :: xs -> go ((c, d) :: acc) (e, f, xs)
      in
      let lst, s = go [] (c, d, lst) in
      G (Green (p, HOLE, s), of_list (List.rev lst))

let of_list lst = Is (T (of_list lst))

let append xs ys = fold_right cons xs ys
