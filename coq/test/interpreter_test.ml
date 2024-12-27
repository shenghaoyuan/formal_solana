
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _::l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)
 let rec add n0 m =
   match n0 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n0 m =
    match n0 with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n' -> (match m with
               | O -> false
               | S m' -> eqb n' m')
 end

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val div2 : positive -> positive **)

  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH

  (** val size : positive -> positive **)

  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> false)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH -> (match q with
             | XO q0 -> XI q0
             | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH -> (match q with
             | XO _ -> N0
             | _ -> Npos XH)

  (** val ldiff : positive -> positive -> n **)

  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH -> (match q with
             | XO _ -> Npos XH
             | _ -> N0)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)

  (** val testbit : positive -> n -> bool **)

  let rec testbit p n0 =
    match p with
    | XI p0 -> (match n0 with
                | N0 -> true
                | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 -> (match n0 with
                | N0 -> false
                | Npos n1 -> testbit p0 (pred_N n1))
    | XH -> (match n0 with
             | N0 -> true
             | Npos _ -> false)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)

  (** val eq_dec : positive -> positive -> bool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> false)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> false)
    | XH -> (match x0 with
             | XH -> true
             | _ -> false)
 end

module N =
 struct
  (** val succ_double : n -> n **)

  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val double : n -> n **)

  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val succ_pos : n -> positive **)

  let succ_pos = function
  | N0 -> XH
  | Npos p -> Coq_Pos.succ p

  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Coq_Pos.compare n' m')

  (** val leb : n -> n -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val pos_div_eucl : positive -> n -> n * n **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | XH ->
      (match b with
       | N0 -> (N0, (Npos XH))
       | Npos p -> (match p with
                    | XH -> ((Npos XH), N0)
                    | _ -> (N0, (Npos XH))))

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Coq_Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Coq_Pos.coq_land p q)

  (** val ldiff : n -> n -> n **)

  let ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Coq_Pos.ldiff p q)

  (** val coq_lxor : n -> n -> n **)

  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Coq_Pos.coq_lxor p q)

  (** val testbit : n -> n -> bool **)

  let testbit a n0 =
    match a with
    | N0 -> false
    | Npos p -> Coq_Pos.testbit p n0
 end

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n0 l default =
  match n0 with
  | O -> (match l with
          | [] -> default
          | x::_ -> x)
  | S m -> (match l with
            | [] -> default
            | _::t0 -> nth m t0 default)

(** val nth_error : 'a1 list -> nat -> 'a1 option **)

let rec nth_error l = function
| O -> (match l with
        | [] -> None
        | x::_ -> Some x)
| S n1 -> (match l with
           | [] -> None
           | _::l0 -> nth_error l0 n1)

(** val removelast : 'a1 list -> 'a1 list **)

let rec removelast = function
| [] -> []
| a::l0 -> (match l0 with
            | [] -> []
            | _::_ -> a::(removelast l0))

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x::l' -> app (rev l') (x::[])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t0 -> (f a)::(map f t0)

(** val firstn : nat -> 'a1 list -> 'a1 list **)

let rec firstn n0 l =
  match n0 with
  | O -> []
  | S n1 -> (match l with
             | [] -> []
             | a::l0 -> a::(firstn n1 l0))

(** val skipn : nat -> 'a1 list -> 'a1 list **)

let rec skipn n0 l =
  match n0 with
  | O -> l
  | S n1 -> (match l with
             | [] -> []
             | _::l0 -> skipn n1 l0)

(** val repeat : 'a1 -> nat -> 'a1 list **)

let rec repeat x = function
| O -> []
| S k -> x::(repeat x k)

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Coq_Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val pred : z -> z **)

  let pred x =
    add x (Zneg XH)

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val pow_pos : z -> positive -> z **)

  let pow_pos z0 =
    Coq_Pos.iter (mul z0) (Zpos XH)

  (** val pow : z -> z -> z **)

  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg _ -> Z0

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Coq_Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Coq_Pos.eqb p q
                 | _ -> false)

  (** val to_nat : z -> nat **)

  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> O

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Coq_Pos.of_succ_nat n1)

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n0 f x =
    match n0 with
    | Zpos p -> Coq_Pos.iter f x p
    | _ -> x

  (** val pos_div_eucl : positive -> z -> z * z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XH -> if leb (Zpos (XO XH)) b then (Z0, (Zpos XH)) else ((Zpos XH), Z0)

  (** val div_eucl : z -> z -> z * z **)

  let div_eucl a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> (Z0, Z0)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> (Z0, Z0)
       | Zpos _ ->
         let (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' -> let (q, r) = pos_div_eucl a' (Zpos b') in (q, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let (q, _) = div_eucl a b in q

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let (_, r) = div_eucl a b in r

  (** val quotrem : z -> z -> z * z **)

  let quotrem a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a0 ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in ((of_N q), (of_N r))
       | Zneg b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in
         ((opp (of_N q)), (of_N r)))
    | Zneg a0 ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in
         ((opp (of_N q)), (opp (of_N r)))
       | Zneg b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in
         ((of_N q), (opp (of_N r))))

  (** val quot : z -> z -> z **)

  let quot a b =
    fst (quotrem a b)

  (** val rem : z -> z -> z **)

  let rem a b =
    snd (quotrem a b)

  (** val odd : z -> bool **)

  let odd = function
  | Z0 -> false
  | Zpos p -> (match p with
               | XO _ -> false
               | _ -> true)
  | Zneg p -> (match p with
               | XO _ -> false
               | _ -> true)

  (** val div2 : z -> z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p -> (match p with
               | XH -> Z0
               | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p -> Zneg (Coq_Pos.div2_up p)

  (** val log2 : z -> z **)

  let log2 = function
  | Zpos p0 ->
    (match p0 with
     | XI p -> Zpos (Coq_Pos.size p)
     | XO p -> Zpos (Coq_Pos.size p)
     | XH -> Z0)
  | _ -> Z0

  (** val testbit : z -> z -> bool **)

  let testbit a = function
  | Z0 -> odd a
  | Zpos p ->
    (match a with
     | Z0 -> false
     | Zpos a0 -> Coq_Pos.testbit a0 (Npos p)
     | Zneg a0 -> negb (N.testbit (Coq_Pos.pred_N a0) (Npos p)))
  | Zneg _ -> false

  (** val shiftl : z -> z -> z **)

  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Coq_Pos.iter (mul (Zpos (XO XH))) a p
  | Zneg p -> Coq_Pos.iter div2 a p

  (** val shiftr : z -> z -> z **)

  let shiftr a n0 =
    shiftl a (opp n0)

  (** val coq_lor : z -> z -> z **)

  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Coq_Pos.coq_lor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 ->
         Zneg
           (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))

  (** val coq_land : z -> z -> z **)

  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Coq_Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Coq_Pos.pred_N a0))
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))

  (** val coq_lxor : z -> z -> z **)

  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.coq_lxor a0 b0)
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Coq_Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 ->
         Zneg (N.succ_pos (N.coq_lxor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0)))

  (** val eq_dec : z -> z -> bool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos x0 -> (match y with
                  | Zpos p0 -> Coq_Pos.eq_dec x0 p0
                  | _ -> false)
    | Zneg x0 -> (match y with
                  | Zneg p0 -> Coq_Pos.eq_dec x0 p0
                  | _ -> false)
 end

(** val z_lt_dec : z -> z -> bool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> true
  | _ -> false

(** val z_le_dec : z -> z -> bool **)

let z_le_dec x y =
  match Z.compare x y with
  | Gt -> false
  | _ -> true

(** val z_le_gt_dec : z -> z -> bool **)

let z_le_gt_dec =
  z_le_dec

(** val zeq_bool : z -> z -> bool **)

let zeq_bool x y =
  match Z.compare x y with
  | Eq -> true
  | _ -> false

(** val zdivide_dec : z -> z -> bool **)

let zdivide_dec a b =
  let s = Z.eq_dec a Z0 in
  if s then Z.eq_dec b Z0 else Z.eq_dec (Z.modulo b a) Z0

(** val shift_nat : nat -> positive -> positive **)

let rec shift_nat n0 z0 =
  match n0 with
  | O -> z0
  | S n1 -> XO (shift_nat n1 z0)

(** val shift_pos : positive -> positive -> positive **)

let shift_pos n0 z0 =
  Coq_Pos.iter (fun x -> XO x) z0 n0

(** val two_power_nat : nat -> z **)

let two_power_nat n0 =
  Zpos (shift_nat n0 XH)

(** val two_power_pos : positive -> z **)

let two_power_pos x =
  Zpos (shift_pos x XH)

(** val two_p : z -> z **)

let two_p = function
| Z0 -> Zpos XH
| Zpos y -> two_power_pos y
| Zneg _ -> Z0

(** val peq : positive -> positive -> bool **)

let peq =
  Coq_Pos.eq_dec

(** val zeq : z -> z -> bool **)

let zeq =
  Z.eq_dec

(** val zlt : z -> z -> bool **)

let zlt =
  z_lt_dec

(** val zle : z -> z -> bool **)

let zle =
  z_le_gt_dec

(** val proj_sumbool : bool -> bool **)

let proj_sumbool = function
| true -> true
| false -> false

(** val p_mod_two_p : positive -> nat -> z **)

let rec p_mod_two_p p = function
| O -> Z0
| S m ->
  (match p with
   | XI q -> Z.succ_double (p_mod_two_p q m)
   | XO q -> Z.double (p_mod_two_p q m)
   | XH -> Zpos XH)

(** val zshiftin : bool -> z -> z **)

let zshiftin b x =
  if b then Z.succ_double x else Z.double x

(** val zzero_ext : z -> z -> z **)

let zzero_ext n0 x =
  Z.iter n0 (fun rec0 x0 -> zshiftin (Z.odd x0) (rec0 (Z.div2 x0))) (fun _ ->
    Z0) x

(** val zsign_ext : z -> z -> z **)

let zsign_ext n0 x =
  Z.iter (Z.pred n0) (fun rec0 x0 -> zshiftin (Z.odd x0) (rec0 (Z.div2 x0)))
    (fun x0 ->
    if (&&) (Z.odd x0) (proj_sumbool (zlt Z0 n0)) then Zneg XH else Z0) x

(** val z_one_bits : nat -> z -> z -> z list **)

let rec z_one_bits n0 x i =
  match n0 with
  | O -> []
  | S m ->
    if Z.odd x
    then i::(z_one_bits m (Z.div2 x) (Z.add i (Zpos XH)))
    else z_one_bits m (Z.div2 x) (Z.add i (Zpos XH))

(** val p_is_power2 : positive -> bool **)

let rec p_is_power2 = function
| XI _ -> false
| XO q -> p_is_power2 q
| XH -> true

(** val z_is_power2 : z -> z option **)

let z_is_power2 x = match x with
| Zpos p -> if p_is_power2 p then Some (Z.log2 x) else None
| _ -> None

(** val zsize : z -> z **)

let zsize = function
| Zpos p -> Zpos (Coq_Pos.size p)
| _ -> Z0

(** val emin : z -> z -> z **)

let emin prec emax =
  Z.sub (Z.sub (Zpos (XI XH)) emax) prec

type full_float =
| F754_zero of bool
| F754_infinity of bool
| F754_nan of bool * positive
| F754_finite of bool * positive * z

type binary_float =
| B754_zero of bool
| B754_infinity of bool
| B754_nan of bool * positive
| B754_finite of bool * positive * z

(** val fF2B : z -> z -> full_float -> binary_float **)

let fF2B _ _ = function
| F754_zero s -> B754_zero s
| F754_infinity s -> B754_infinity s
| F754_nan (b, pl) -> B754_nan (b, pl)
| F754_finite (s, m, e) -> B754_finite (s, m, e)

(** val join_bits : z -> z -> bool -> z -> z -> z **)

let join_bits mw ew s m e =
  Z.add (Z.shiftl (Z.add (if s then Z.pow (Zpos (XO XH)) ew else Z0) e) mw) m

(** val split_bits : z -> z -> z -> (bool * z) * z **)

let split_bits mw ew x =
  let mm = Z.pow (Zpos (XO XH)) mw in
  let em = Z.pow (Zpos (XO XH)) ew in
  (((Z.leb (Z.mul mm em) x), (Z.modulo x mm)), (Z.modulo (Z.div x mm) em))

(** val bits_of_binary_float : z -> z -> binary_float -> z **)

let bits_of_binary_float mw ew =
  let prec = Z.add mw (Zpos XH) in
  let emax = Z.pow (Zpos (XO XH)) (Z.sub ew (Zpos XH)) in
  (fun x ->
  match x with
  | B754_zero sx -> join_bits mw ew sx Z0 Z0
  | B754_infinity sx ->
    join_bits mw ew sx Z0 (Z.sub (Z.pow (Zpos (XO XH)) ew) (Zpos XH))
  | B754_nan (sx, plx) ->
    join_bits mw ew sx (Zpos plx) (Z.sub (Z.pow (Zpos (XO XH)) ew) (Zpos XH))
  | B754_finite (sx, mx, ex) ->
    let m = Z.sub (Zpos mx) (Z.pow (Zpos (XO XH)) mw) in
    if Z.leb Z0 m
    then join_bits mw ew sx m (Z.add (Z.sub ex (emin prec emax)) (Zpos XH))
    else join_bits mw ew sx (Zpos mx) Z0)

(** val binary_float_of_bits_aux : z -> z -> z -> full_float **)

let binary_float_of_bits_aux mw ew =
  let prec = Z.add mw (Zpos XH) in
  let emax = Z.pow (Zpos (XO XH)) (Z.sub ew (Zpos XH)) in
  (fun x ->
  let (p, ex) = split_bits mw ew x in
  let (sx, mx) = p in
  if zeq_bool ex Z0
  then (match mx with
        | Z0 -> F754_zero sx
        | Zpos px -> F754_finite (sx, px, (emin prec emax))
        | Zneg _ -> F754_nan (false, XH))
  else if zeq_bool ex (Z.sub (Z.pow (Zpos (XO XH)) ew) (Zpos XH))
       then (match mx with
             | Z0 -> F754_infinity sx
             | Zpos plx -> F754_nan (sx, plx)
             | Zneg _ -> F754_nan (false, XH))
       else (match Z.add mx (Z.pow (Zpos (XO XH)) mw) with
             | Zpos px ->
               F754_finite (sx, px,
                 (Z.sub (Z.add ex (emin prec emax)) (Zpos XH)))
             | _ -> F754_nan (false, XH)))

(** val binary_float_of_bits : z -> z -> z -> binary_float **)

let binary_float_of_bits mw ew x =
  let prec = Z.add mw (Zpos XH) in
  let emax = Z.pow (Zpos (XO XH)) (Z.sub ew (Zpos XH)) in
  fF2B prec emax (binary_float_of_bits_aux mw ew x)

type binary32 = binary_float

(** val b32_of_bits : z -> binary32 **)

let b32_of_bits =
  binary_float_of_bits (Zpos (XI (XI (XI (XO XH))))) (Zpos (XO (XO (XO XH))))

(** val bits_of_b32 : binary32 -> z **)

let bits_of_b32 =
  bits_of_binary_float (Zpos (XI (XI (XI (XO XH))))) (Zpos (XO (XO (XO XH))))

type binary64 = binary_float

(** val b64_of_bits : z -> binary64 **)

let b64_of_bits =
  binary_float_of_bits (Zpos (XO (XO (XI (XO (XI XH)))))) (Zpos (XI (XI (XO
    XH))))

(** val bits_of_b64 : binary64 -> z **)

let bits_of_b64 =
  bits_of_binary_float (Zpos (XO (XO (XI (XO (XI XH)))))) (Zpos (XI (XI (XO
    XH))))

(** val ptr64 : bool **)

let ptr64 =
  true

(** val big_endian : bool **)

let big_endian =
  false

type comparison0 =
| Ceq
| Cne
| Clt
| Cle
| Cgt
| Cge

module type WORDSIZE =
 sig
  val wordsize : nat
 end

module Make =
 functor (WS:WORDSIZE) ->
 struct
  (** val wordsize : nat **)

  let wordsize =
    WS.wordsize

  (** val zwordsize : z **)

  let zwordsize =
    Z.of_nat wordsize

  (** val modulus : z **)

  let modulus =
    two_power_nat wordsize

  (** val half_modulus : z **)

  let half_modulus =
    Z.div modulus (Zpos (XO XH))

  (** val max_unsigned : z **)

  let max_unsigned =
    Z.sub modulus (Zpos XH)

  (** val max_signed : z **)

  let max_signed =
    Z.sub half_modulus (Zpos XH)

  (** val min_signed : z **)

  let min_signed =
    Z.opp half_modulus

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  (** val intval : int -> z **)

  let intval i =
    i

  (** val coq_Z_mod_modulus : z -> z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> p_mod_two_p p wordsize
  | Zneg p ->
    let r = p_mod_two_p p wordsize in if zeq r Z0 then Z0 else Z.sub modulus r

  (** val unsigned : int -> z **)

  let unsigned =
    intval

  (** val signed : int -> z **)

  let signed n0 =
    let x = unsigned n0 in if zlt x half_modulus then x else Z.sub x modulus

  (** val repr : z -> int **)

  let repr =
    coq_Z_mod_modulus

  (** val zero : int **)

  let zero =
    repr Z0

  (** val one : int **)

  let one =
    repr (Zpos XH)

  (** val mone : int **)

  let mone =
    repr (Zneg XH)

  (** val iwordsize : int **)

  let iwordsize =
    repr zwordsize

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    zeq

  (** val eq : int -> int -> bool **)

  let eq x y =
    if zeq (unsigned x) (unsigned y) then true else false

  (** val lt : int -> int -> bool **)

  let lt x y =
    if zlt (signed x) (signed y) then true else false

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    if zlt (unsigned x) (unsigned y) then true else false

  (** val neg : int -> int **)

  let neg x =
    repr (Z.opp (unsigned x))

  (** val add : int -> int -> int **)

  let add x y =
    repr (Z.add (unsigned x) (unsigned y))

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Z.sub (unsigned x) (unsigned y))

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Z.mul (unsigned x) (unsigned y))

  (** val divs : int -> int -> int **)

  let divs x y =
    repr (Z.quot (signed x) (signed y))

  (** val mods : int -> int -> int **)

  let mods x y =
    repr (Z.rem (signed x) (signed y))

  (** val divu : int -> int -> int **)

  let divu x y =
    repr (Z.div (unsigned x) (unsigned y))

  (** val modu : int -> int -> int **)

  let modu x y =
    repr (Z.modulo (unsigned x) (unsigned y))

  (** val coq_and : int -> int -> int **)

  let coq_and x y =
    repr (Z.coq_land (unsigned x) (unsigned y))

  (** val coq_or : int -> int -> int **)

  let coq_or x y =
    repr (Z.coq_lor (unsigned x) (unsigned y))

  (** val xor : int -> int -> int **)

  let xor x y =
    repr (Z.coq_lxor (unsigned x) (unsigned y))

  (** val not : int -> int **)

  let not x =
    xor x mone

  (** val shl : int -> int -> int **)

  let shl x y =
    repr (Z.shiftl (unsigned x) (unsigned y))

  (** val shru : int -> int -> int **)

  let shru x y =
    repr (Z.shiftr (unsigned x) (unsigned y))

  (** val shr : int -> int -> int **)

  let shr x y =
    repr (Z.shiftr (signed x) (unsigned y))

  (** val rol : int -> int -> int **)

  let rol x y =
    let n0 = Z.modulo (unsigned y) zwordsize in
    repr
      (Z.coq_lor (Z.shiftl (unsigned x) n0)
        (Z.shiftr (unsigned x) (Z.sub zwordsize n0)))

  (** val ror : int -> int -> int **)

  let ror x y =
    let n0 = Z.modulo (unsigned y) zwordsize in
    repr
      (Z.coq_lor (Z.shiftr (unsigned x) n0)
        (Z.shiftl (unsigned x) (Z.sub zwordsize n0)))

  (** val rolm : int -> int -> int -> int **)

  let rolm x a m =
    coq_and (rol x a) m

  (** val shrx : int -> int -> int **)

  let shrx x y =
    divs x (shl one y)

  (** val mulhu : int -> int -> int **)

  let mulhu x y =
    repr (Z.div (Z.mul (unsigned x) (unsigned y)) modulus)

  (** val mulhs : int -> int -> int **)

  let mulhs x y =
    repr (Z.div (Z.mul (signed x) (signed y)) modulus)

  (** val negative : int -> int **)

  let negative x =
    if lt x zero then one else zero

  (** val add_carry : int -> int -> int -> int **)

  let add_carry x y cin =
    if zlt (Z.add (Z.add (unsigned x) (unsigned y)) (unsigned cin)) modulus
    then zero
    else one

  (** val add_overflow : int -> int -> int -> int **)

  let add_overflow x y cin =
    let s = Z.add (Z.add (signed x) (signed y)) (signed cin) in
    if (&&) (proj_sumbool (zle min_signed s))
         (proj_sumbool (zle s max_signed))
    then zero
    else one

  (** val sub_borrow : int -> int -> int -> int **)

  let sub_borrow x y bin =
    if zlt (Z.sub (Z.sub (unsigned x) (unsigned y)) (unsigned bin)) Z0
    then one
    else zero

  (** val sub_overflow : int -> int -> int -> int **)

  let sub_overflow x y bin =
    let s = Z.sub (Z.sub (signed x) (signed y)) (signed bin) in
    if (&&) (proj_sumbool (zle min_signed s))
         (proj_sumbool (zle s max_signed))
    then zero
    else one

  (** val shr_carry : int -> int -> int **)

  let shr_carry x y =
    if (&&) (lt x zero) (negb (eq (coq_and x (sub (shl one y) one)) zero))
    then one
    else zero

  (** val zero_ext : z -> int -> int **)

  let zero_ext n0 x =
    repr (zzero_ext n0 (unsigned x))

  (** val sign_ext : z -> int -> int **)

  let sign_ext n0 x =
    repr (zsign_ext n0 (unsigned x))

  (** val one_bits : int -> int list **)

  let one_bits x =
    map repr (z_one_bits wordsize (unsigned x) Z0)

  (** val is_power2 : int -> int option **)

  let is_power2 x =
    match z_is_power2 (unsigned x) with
    | Some i -> Some (repr i)
    | None -> None

  (** val cmp : comparison0 -> int -> int -> bool **)

  let cmp c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> lt x y
    | Cle -> negb (lt y x)
    | Cgt -> lt y x
    | Cge -> negb (lt x y)

  (** val cmpu : comparison0 -> int -> int -> bool **)

  let cmpu c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> ltu x y
    | Cle -> negb (ltu y x)
    | Cgt -> ltu y x
    | Cge -> negb (ltu x y)

  (** val notbool : int -> int **)

  let notbool x =
    if eq x zero then one else zero

  (** val divmodu2 : int -> int -> int -> (int * int) option **)

  let divmodu2 nhi nlo d =
    if eq_dec d zero
    then None
    else let (q, r) =
           Z.div_eucl (Z.add (Z.mul (unsigned nhi) modulus) (unsigned nlo))
             (unsigned d)
         in
         if zle q max_unsigned then Some ((repr q), (repr r)) else None

  (** val divmods2 : int -> int -> int -> (int * int) option **)

  let divmods2 nhi nlo d =
    if eq_dec d zero
    then None
    else let (q, r) =
           Z.quotrem (Z.add (Z.mul (signed nhi) modulus) (unsigned nlo))
             (signed d)
         in
         if (&&) (proj_sumbool (zle min_signed q))
              (proj_sumbool (zle q max_signed))
         then Some ((repr q), (repr r))
         else None

  (** val testbit : int -> z -> bool **)

  let testbit x i =
    Z.testbit (unsigned x) i

  (** val int_of_one_bits : int list -> int **)

  let rec int_of_one_bits = function
  | [] -> zero
  | a::b -> add (shl one a) (int_of_one_bits b)

  (** val no_overlap : int -> z -> int -> z -> bool **)

  let no_overlap ofs1 sz1 ofs2 sz2 =
    let x1 = unsigned ofs1 in
    let x2 = unsigned ofs2 in
    (&&)
      ((&&) (proj_sumbool (zlt (Z.add x1 sz1) modulus))
        (proj_sumbool (zlt (Z.add x2 sz2) modulus)))
      ((||) (proj_sumbool (zle (Z.add x1 sz1) x2))
        (proj_sumbool (zle (Z.add x2 sz2) x1)))

  (** val size : int -> z **)

  let size x =
    zsize (unsigned x)

  (** val unsigned_bitfield_extract : z -> z -> int -> int **)

  let unsigned_bitfield_extract pos width n0 =
    zero_ext width (shru n0 (repr pos))

  (** val signed_bitfield_extract : z -> z -> int -> int **)

  let signed_bitfield_extract pos width n0 =
    sign_ext width (shru n0 (repr pos))

  (** val bitfield_insert : z -> z -> int -> int -> int **)

  let bitfield_insert pos width n0 p =
    let mask0 = shl (repr (Z.sub (two_p width) (Zpos XH))) (repr pos) in
    coq_or (shl (zero_ext width p) (repr pos)) (coq_and n0 (not mask0))
 end

module Wordsize_32 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
 end

module Int = Make(Wordsize_32)

module Wordsize_8 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S O)))))))
 end

module Byte = Make(Wordsize_8)

module Wordsize_64 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 end

module Int64 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    Wordsize_64.wordsize

  (** val modulus : z **)

  let modulus =
    two_power_nat wordsize

  (** val half_modulus : z **)

  let half_modulus =
    Z.div modulus (Zpos (XO XH))

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  (** val intval : int -> z **)

  let intval i =
    i

  (** val coq_Z_mod_modulus : z -> z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> p_mod_two_p p wordsize
  | Zneg p ->
    let r = p_mod_two_p p wordsize in if zeq r Z0 then Z0 else Z.sub modulus r

  (** val unsigned : int -> z **)

  let unsigned =
    intval

  (** val signed : int -> z **)

  let signed n0 =
    let x = unsigned n0 in if zlt x half_modulus then x else Z.sub x modulus

  (** val repr : z -> int **)

  let repr =
    coq_Z_mod_modulus

  (** val zero : int **)

  let zero =
    repr Z0

  (** val one : int **)

  let one =
    repr (Zpos XH)

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    zeq

  (** val eq : int -> int -> bool **)

  let eq x y =
    if zeq (unsigned x) (unsigned y) then true else false

  (** val lt : int -> int -> bool **)

  let lt x y =
    if zlt (signed x) (signed y) then true else false

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    if zlt (unsigned x) (unsigned y) then true else false

  (** val neg : int -> int **)

  let neg x =
    repr (Z.opp (unsigned x))

  (** val add : int -> int -> int **)

  let add x y =
    repr (Z.add (unsigned x) (unsigned y))

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Z.sub (unsigned x) (unsigned y))

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Z.mul (unsigned x) (unsigned y))

  (** val divs : int -> int -> int **)

  let divs x y =
    repr (Z.quot (signed x) (signed y))

  (** val mods : int -> int -> int **)

  let mods x y =
    repr (Z.rem (signed x) (signed y))

  (** val divu : int -> int -> int **)

  let divu x y =
    repr (Z.div (unsigned x) (unsigned y))

  (** val modu : int -> int -> int **)

  let modu x y =
    repr (Z.modulo (unsigned x) (unsigned y))

  (** val coq_and : int -> int -> int **)

  let coq_and x y =
    repr (Z.coq_land (unsigned x) (unsigned y))

  (** val coq_or : int -> int -> int **)

  let coq_or x y =
    repr (Z.coq_lor (unsigned x) (unsigned y))

  (** val xor : int -> int -> int **)

  let xor x y =
    repr (Z.coq_lxor (unsigned x) (unsigned y))

  (** val shl : int -> int -> int **)

  let shl x y =
    repr (Z.shiftl (unsigned x) (unsigned y))

  (** val shru : int -> int -> int **)

  let shru x y =
    repr (Z.shiftr (unsigned x) (unsigned y))

  (** val shr : int -> int -> int **)

  let shr x y =
    repr (Z.shiftr (signed x) (unsigned y))

  (** val mulhu : int -> int -> int **)

  let mulhu x y =
    repr (Z.div (Z.mul (unsigned x) (unsigned y)) modulus)

  (** val mulhs : int -> int -> int **)

  let mulhs x y =
    repr (Z.div (Z.mul (signed x) (signed y)) modulus)

  (** val zero_ext : z -> int -> int **)

  let zero_ext n0 x =
    repr (zzero_ext n0 (unsigned x))

  (** val cmp : comparison0 -> int -> int -> bool **)

  let cmp c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> lt x y
    | Cle -> negb (lt y x)
    | Cgt -> lt y x
    | Cge -> negb (lt x y)

  (** val cmpu : comparison0 -> int -> int -> bool **)

  let cmpu c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> ltu x y
    | Cle -> negb (ltu y x)
    | Cgt -> ltu y x
    | Cge -> negb (ltu x y)

  (** val unsigned_bitfield_extract : z -> z -> int -> int **)

  let unsigned_bitfield_extract pos width n0 =
    zero_ext width (shru n0 (repr pos))
 end

module Wordsize_Ptrofs =
 struct
  (** val wordsize : nat **)

  let wordsize =
    if ptr64
    then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
 end

module Ptrofs =
 struct
  (** val wordsize : nat **)

  let wordsize =
    Wordsize_Ptrofs.wordsize

  (** val modulus : z **)

  let modulus =
    two_power_nat wordsize

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  (** val intval : int -> z **)

  let intval i =
    i

  (** val coq_Z_mod_modulus : z -> z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> p_mod_two_p p wordsize
  | Zneg p ->
    let r = p_mod_two_p p wordsize in if zeq r Z0 then Z0 else Z.sub modulus r

  (** val unsigned : int -> z **)

  let unsigned =
    intval

  (** val repr : z -> int **)

  let repr =
    coq_Z_mod_modulus

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    zeq

  (** val of_int64 : Int64.int -> int **)

  let of_int64 x =
    repr (Int64.unsigned x)

  (** val of_int64u : Int64.int -> int **)

  let of_int64u =
    of_int64
 end

module Wordsize_16 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
 end

module Int16 = Make(Wordsize_16)

type usize = Int64.int

(** val bit_left_shift_word : Int16.int -> nat -> Int16.int **)

let bit_left_shift_word x n0 =
  Int16.shl x (Int16.repr (Z.of_nat n0))

(** val bit_right_shift_word : Int16.int -> nat -> Int16.int **)

let bit_right_shift_word x n0 =
  Int16.shru x (Int16.repr (Z.of_nat n0))

(** val bit_left_shift_int : Int.int -> nat -> Int.int **)

let bit_left_shift_int x n0 =
  Int.shl x (Int.repr (Z.of_nat n0))

(** val bit_right_shift_int : Int.int -> nat -> Int.int **)

let bit_right_shift_int x n0 =
  Int.shru x (Int.repr (Z.of_nat n0))

(** val bit_left_shift_int64 : Int64.int -> nat -> Int64.int **)

let bit_left_shift_int64 x n0 =
  Int64.shl x (Int64.repr (Z.of_nat n0))

(** val bit_right_shift_int64 : Int64.int -> nat -> Int64.int **)

let bit_right_shift_int64 x n0 =
  Int64.shru x (Int64.repr (Z.of_nat n0))

(** val byte_list_of_word : Int16.int -> Byte.int list **)

let byte_list_of_word x =
  (Byte.repr
    (Int16.unsigned
      (Int16.coq_and x
        (Int16.repr (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))))::(
    (Byte.repr
      (Int16.unsigned
        (Int16.coq_and
          (bit_right_shift_word x (S (S (S (S (S (S (S (S O)))))))))
          (Int16.repr (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))))::[])

(** val byte_list_of_int : Int.int -> Byte.int list **)

let byte_list_of_int x =
  (Byte.repr
    (Int.unsigned
      (Int.coq_and x (Int.repr (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))))::(
    (Byte.repr
      (Int.unsigned
        (Int.coq_and
          (bit_right_shift_int x (S (S (S (S (S (S (S (S O)))))))))
          (Int.repr (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))))::(
    (Byte.repr
      (Int.unsigned
        (Int.coq_and
          (bit_right_shift_int x (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S O)))))))))))))))))
          (Int.repr (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))))::(
    (Byte.repr
      (Int.unsigned
        (Int.coq_and
          (bit_right_shift_int x (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))
          (Int.repr (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))))::[])))

(** val byte_list_of_int64 : Int64.int -> Byte.int list **)

let byte_list_of_int64 x =
  (Byte.repr
    (Int64.unsigned
      (Int64.coq_and x
        (Int64.repr (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))))::(
    (Byte.repr
      (Int64.unsigned
        (Int64.coq_and
          (bit_right_shift_int64 x (S (S (S (S (S (S (S (S O)))))))))
          (Int64.repr (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))))::(
    (Byte.repr
      (Int64.unsigned
        (Int64.coq_and
          (bit_right_shift_int64 x (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S O)))))))))))))))))
          (Int64.repr (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))))::(
    (Byte.repr
      (Int64.unsigned
        (Int64.coq_and
          (bit_right_shift_int64 x (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))
          (Int64.repr (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))))::(
    (Byte.repr
      (Int64.unsigned
        (Int64.coq_and
          (bit_right_shift_int64 x (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))
          (Int64.repr (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))))::(
    (Byte.repr
      (Int64.unsigned
        (Int64.coq_and
          (bit_right_shift_int64 x (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))
          (Int64.repr (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))))::(
    (Byte.repr
      (Int64.unsigned
        (Int64.coq_and
          (bit_right_shift_int64 x (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))
          (Int64.repr (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))))::(
    (Byte.repr
      (Int64.unsigned
        (Int64.coq_and
          (bit_right_shift_int64 x (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          (Int64.repr (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))))::[])))))))

(** val int64_of_byte_list : Byte.int list -> Int64.int option **)

let int64_of_byte_list l =
  if Z.eqb (Z.of_nat (length l)) (Zpos (XO (XO (XO XH))))
  then Some
         (Int64.coq_or
           (bit_left_shift_int64
             (Int64.repr
               (Byte.unsigned (nth (S (S (S (S (S (S (S O))))))) l Byte.zero)))
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           (Int64.coq_or
             (bit_left_shift_int64
               (Int64.repr
                 (Byte.unsigned (nth (S (S (S (S (S (S O)))))) l Byte.zero)))
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S
               O)))))))))))))))))))))))))))))))))))))))))))))))))
             (Int64.coq_or
               (bit_left_shift_int64
                 (Int64.repr
                   (Byte.unsigned (nth (S (S (S (S (S O))))) l Byte.zero)))
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 O)))))))))))))))))))))))))))))))))))))))))
               (Int64.coq_or
                 (bit_left_shift_int64
                   (Int64.repr
                     (Byte.unsigned (nth (S (S (S (S O)))) l Byte.zero))) (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S
                   O)))))))))))))))))))))))))))))))))
                 (Int64.coq_or
                   (bit_left_shift_int64
                     (Int64.repr
                       (Byte.unsigned (nth (S (S (S O))) l Byte.zero))) (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S O)))))))))))))))))))))))))
                   (Int64.coq_or
                     (bit_left_shift_int64
                       (Int64.repr
                         (Byte.unsigned (nth (S (S O)) l Byte.zero))) (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       O)))))))))))))))))
                     (Int64.coq_or
                       (bit_left_shift_int64
                         (Int64.repr (Byte.unsigned (nth (S O) l Byte.zero)))
                         (S (S (S (S (S (S (S (S O)))))))))
                       (Int64.repr (Byte.unsigned (nth O l Byte.zero))))))))))
  else None

(** val int_of_byte_list : Byte.int list -> Int.int option **)

let int_of_byte_list l =
  if Z.eqb (Z.of_nat (length l)) (Zpos (XO (XO XH)))
  then Some
         (Int.coq_or
           (bit_left_shift_int
             (Int.repr (Byte.unsigned (nth (S (S (S O))) l Byte.zero))) (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S O)))))))))))))))))))))))))
           (Int.coq_or
             (bit_left_shift_int
               (Int.repr (Byte.unsigned (nth (S (S O)) l Byte.zero))) (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))
             (Int.coq_or
               (bit_left_shift_int
                 (Int.repr (Byte.unsigned (nth (S O) l Byte.zero))) (S (S (S
                 (S (S (S (S (S O)))))))))
               (Int.repr (Byte.unsigned (nth O l Byte.zero))))))
  else None

(** val word_of_byte_list : Byte.int list -> Int16.int option **)

let word_of_byte_list l =
  if Z.eqb (Z.of_nat (length l)) (Zpos (XO XH))
  then Some
         (Int16.coq_or
           (bit_left_shift_word
             (Int16.repr (Byte.unsigned (nth (S O) l Byte.zero))) (S (S (S (S
             (S (S (S (S O)))))))))
           (Int16.repr (Byte.unsigned (nth O l Byte.zero))))
  else None

module PTree =
 struct
  type 'a tree' =
  | Node001 of 'a tree'
  | Node010 of 'a
  | Node011 of 'a * 'a tree'
  | Node100 of 'a tree'
  | Node101 of 'a tree' * 'a tree'
  | Node110 of 'a tree' * 'a
  | Node111 of 'a tree' * 'a * 'a tree'

  type 'a tree =
  | Empty
  | Nodes of 'a tree'

  type 'a t = 'a tree

  (** val empty : 'a1 t **)

  let empty =
    Empty

  (** val get' : positive -> 'a1 tree' -> 'a1 option **)

  let rec get' p m =
    match p with
    | XI q ->
      (match m with
       | Node001 m' -> get' q m'
       | Node011 (_, m') -> get' q m'
       | Node101 (_, m') -> get' q m'
       | Node111 (_, _, m') -> get' q m'
       | _ -> None)
    | XO q ->
      (match m with
       | Node100 m' -> get' q m'
       | Node101 (m', _) -> get' q m'
       | Node110 (m', _) -> get' q m'
       | Node111 (m', _, _) -> get' q m'
       | _ -> None)
    | XH ->
      (match m with
       | Node010 x -> Some x
       | Node011 (x, _) -> Some x
       | Node110 (_, x) -> Some x
       | Node111 (_, x, _) -> Some x
       | _ -> None)

  (** val get : positive -> 'a1 tree -> 'a1 option **)

  let get p = function
  | Empty -> None
  | Nodes m' -> get' p m'

  (** val set0 : positive -> 'a1 -> 'a1 tree' **)

  let rec set0 p x =
    match p with
    | XI q -> Node001 (set0 q x)
    | XO q -> Node100 (set0 q x)
    | XH -> Node010 x

  (** val set' : positive -> 'a1 -> 'a1 tree' -> 'a1 tree' **)

  let rec set' p x m =
    match p with
    | XI q ->
      (match m with
       | Node001 r -> Node001 (set' q x r)
       | Node010 y -> Node011 (y, (set0 q x))
       | Node011 (y, r) -> Node011 (y, (set' q x r))
       | Node100 l -> Node101 (l, (set0 q x))
       | Node101 (l, r) -> Node101 (l, (set' q x r))
       | Node110 (l, y) -> Node111 (l, y, (set0 q x))
       | Node111 (l, y, r) -> Node111 (l, y, (set' q x r)))
    | XO q ->
      (match m with
       | Node001 r -> Node101 ((set0 q x), r)
       | Node010 y -> Node110 ((set0 q x), y)
       | Node011 (y, r) -> Node111 ((set0 q x), y, r)
       | Node100 l -> Node100 (set' q x l)
       | Node101 (l, r) -> Node101 ((set' q x l), r)
       | Node110 (l, y) -> Node110 ((set' q x l), y)
       | Node111 (l, y, r) -> Node111 ((set' q x l), y, r))
    | XH ->
      (match m with
       | Node001 r -> Node011 (x, r)
       | Node010 _ -> Node010 x
       | Node011 (_, r) -> Node011 (x, r)
       | Node100 l -> Node110 (l, x)
       | Node101 (l, r) -> Node111 (l, x, r)
       | Node110 (l, _) -> Node110 (l, x)
       | Node111 (l, _, r) -> Node111 (l, x, r))

  (** val set : positive -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let set p x = function
  | Empty -> Nodes (set0 p x)
  | Nodes m' -> Nodes (set' p x m')

  (** val map1' : ('a1 -> 'a2) -> 'a1 tree' -> 'a2 tree' **)

  let rec map1' f = function
  | Node001 r -> Node001 (map1' f r)
  | Node010 x -> Node010 (f x)
  | Node011 (x, r) -> Node011 ((f x), (map1' f r))
  | Node100 l -> Node100 (map1' f l)
  | Node101 (l, r) -> Node101 ((map1' f l), (map1' f r))
  | Node110 (l, x) -> Node110 ((map1' f l), (f x))
  | Node111 (l, x, r) -> Node111 ((map1' f l), (f x), (map1' f r))

  (** val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map1 f = function
  | Empty -> Empty
  | Nodes m0 -> Nodes (map1' f m0)
 end

module PMap =
 struct
  type 'a t = 'a * 'a PTree.t

  (** val init : 'a1 -> 'a1 * 'a1 PTree.t **)

  let init x =
    (x, PTree.empty)

  (** val get : positive -> 'a1 t -> 'a1 **)

  let get i m =
    match PTree.get i (snd m) with
    | Some x -> x
    | None -> fst m

  (** val set : positive -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.tree **)

  let set i x m =
    ((fst m), (PTree.set i x (snd m)))

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    ((f (fst m)), (PTree.map1 f (snd m)))
 end

module type INDEXED_TYPE =
 sig
  type t

  val index : t -> positive

  val eq : t -> t -> bool
 end

module IMap =
 functor (X:INDEXED_TYPE) ->
 struct
  type elt = X.t

  (** val elt_eq : X.t -> X.t -> bool **)

  let elt_eq =
    X.eq

  type 'x t = 'x PMap.t

  (** val init : 'a1 -> 'a1 * 'a1 PTree.t **)

  let init =
    PMap.init

  (** val get : X.t -> 'a1 t -> 'a1 **)

  let get i m =
    PMap.get (X.index i) m

  (** val set : X.t -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.tree **)

  let set i v m =
    PMap.set (X.index i) v m

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map =
    PMap.map
 end

module ZIndexed =
 struct
  type t = z

  (** val index : z -> positive **)

  let index = function
  | Z0 -> XH
  | Zpos p -> XO p
  | Zneg p -> XI p

  (** val eq : z -> z -> bool **)

  let eq =
    zeq
 end

module ZMap = IMap(ZIndexed)

module type EQUALITY_TYPE =
 sig
  type t

  val eq : t -> t -> bool
 end

module EMap =
 functor (X:EQUALITY_TYPE) ->
 struct
  type elt = X.t

  (** val elt_eq : X.t -> X.t -> bool **)

  let elt_eq =
    X.eq

  type 'a t = X.t -> 'a

  (** val init : 'a1 -> X.t -> 'a1 **)

  let init v _ =
    v

  (** val get : X.t -> 'a1 t -> 'a1 **)

  let get x m =
    m x

  (** val set : X.t -> 'a1 -> 'a1 t -> X.t -> 'a1 **)

  let set x v m y =
    if X.eq y x then v else m y

  (** val map : ('a1 -> 'a2) -> 'a1 t -> X.t -> 'a2 **)

  let map f m x =
    f (m x)
 end

(** val beq_dec : z -> z -> binary_float -> binary_float -> bool **)

let beq_dec _ _ f1 f2 =
  match f1 with
  | B754_zero s1 ->
    (match f2 with
     | B754_zero s2 ->
       if s1 then if s2 then true else false else if s2 then false else true
     | _ -> false)
  | B754_infinity s1 ->
    (match f2 with
     | B754_infinity s2 ->
       if s1 then if s2 then true else false else if s2 then false else true
     | _ -> false)
  | B754_nan (s1, p1) ->
    (match f2 with
     | B754_nan (s2, p2) ->
       if s1
       then if s2 then Coq_Pos.eq_dec p1 p2 else false
       else if s2 then false else Coq_Pos.eq_dec p1 p2
     | _ -> false)
  | B754_finite (s1, m1, e1) ->
    (match f2 with
     | B754_finite (s2, m2, e2) ->
       if s1
       then if s2
            then let s = Coq_Pos.eq_dec m1 m2 in
                 if s then Z.eq_dec e1 e2 else false
            else false
       else if s2
            then false
            else let s = Coq_Pos.eq_dec m1 m2 in
                 if s then Z.eq_dec e1 e2 else false
     | _ -> false)

type float = binary64

type float32 = binary32

module Float =
 struct
  (** val eq_dec : float -> float -> bool **)

  let eq_dec =
    beq_dec (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO
      (XO (XO (XO (XO XH)))))))))))

  (** val to_bits : float -> Int64.int **)

  let to_bits f =
    Int64.repr (bits_of_b64 f)

  (** val of_bits : Int64.int -> float **)

  let of_bits b =
    b64_of_bits (Int64.unsigned b)
 end

module Float32 =
 struct
  (** val eq_dec : float32 -> float32 -> bool **)

  let eq_dec =
    beq_dec (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      XH))))))))

  (** val to_bits : float32 -> Int.int **)

  let to_bits f =
    Int.repr (bits_of_b32 f)

  (** val of_bits : Int.int -> float32 **)

  let of_bits b =
    b32_of_bits (Int.unsigned b)
 end

type memory_chunk =
| Mint8signed
| Mint8unsigned
| Mint16signed
| Mint16unsigned
| Mint32
| Mint64
| Mfloat32
| Mfloat64
| Many32
| Many64

type bpf_ireg =
| BR0
| BR1
| BR2
| BR3
| BR4
| BR5
| BR6
| BR7
| BR8
| BR9
| BR10

type off_ty = Int16.int

type snd_op =
| SOImm of Int.int
| SOReg of bpf_ireg

type condition =
| Eq0
| Gt0
| Ge
| Lt0
| Le
| SEt
| Ne
| SGt
| SGe
| SLt
| SLe

type binop =
| BPF_ADD
| BPF_SUB
| BPF_MUL
| BPF_DIV
| BPF_OR
| BPF_AND
| BPF_LSH
| BPF_RSH
| BPF_MOD
| BPF_XOR
| BPF_MOV
| BPF_ARSH

type pqrop =
| BPF_LMUL
| BPF_UDIV
| BPF_UREM
| BPF_SDIV
| BPF_SREM

type pqrop2 =
| BPF_UHMUL
| BPF_SHMUL

type sBPFV =
| V1
| V2

type bpf_instruction =
| BPF_LD_IMM of bpf_ireg * Int.int * Int.int
| BPF_LDX of memory_chunk * bpf_ireg * bpf_ireg * Int16.int
| BPF_ST of memory_chunk * bpf_ireg * snd_op * Int16.int
| BPF_ADD_STK of Int.int
| BPF_ALU of binop * bpf_ireg * snd_op
| BPF_NEG32_REG of bpf_ireg
| BPF_LE of bpf_ireg * Int.int
| BPF_BE of bpf_ireg * Int.int
| BPF_ALU64 of binop * bpf_ireg * snd_op
| BPF_NEG64_REG of bpf_ireg
| BPF_HOR64_IMM of bpf_ireg * Int.int
| BPF_PQR of pqrop * bpf_ireg * snd_op
| BPF_PQR64 of pqrop * bpf_ireg * snd_op
| BPF_PQR2 of pqrop2 * bpf_ireg * snd_op
| BPF_JA of off_ty
| BPF_JUMP of condition * bpf_ireg * snd_op * off_ty
| BPF_CALL_REG of bpf_ireg * Int.int
| BPF_CALL_IMM of bpf_ireg * Int.int
| BPF_EXIT

type bpf_bin = Int64.int list

(** val nat_to_bpf_ireg : nat -> bpf_ireg option **)

let nat_to_bpf_ireg dst =
  if Nat.eqb dst O
  then Some BR0
  else if Nat.eqb dst (S O)
       then Some BR1
       else if Nat.eqb dst (S (S O))
            then Some BR2
            else if Nat.eqb dst (S (S (S O)))
                 then Some BR3
                 else if Nat.eqb dst (S (S (S (S O))))
                      then Some BR4
                      else if Nat.eqb dst (S (S (S (S (S O)))))
                           then Some BR5
                           else if Nat.eqb dst (S (S (S (S (S (S O))))))
                                then Some BR6
                                else if Nat.eqb dst (S (S (S (S (S (S (S
                                          O)))))))
                                     then Some BR7
                                     else if Nat.eqb dst (S (S (S (S (S (S (S
                                               (S O))))))))
                                          then Some BR8
                                          else if Nat.eqb dst (S (S (S (S (S
                                                    (S (S (S (S O)))))))))
                                               then Some BR9
                                               else if Nat.eqb dst (S (S (S
                                                         (S (S (S (S (S (S (S
                                                         O))))))))))
                                                    then Some BR10
                                                    else None

(** val iNSN_SIZE : nat **)

let iNSN_SIZE =
  S (S (S (S (S (S (S (S O)))))))

(** val mM_STACK_START : Int64.int **)

let mM_STACK_START =
  Int64.repr (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
    (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
    (XO XH))))))))))))))))))))))))))))))))))

type func_key = Int.int

type func_val = Int64.int

module Coq_func_Eq =
 struct
  type t = func_key

  (** val eq : Int.int -> Int.int -> bool **)

  let eq =
    Int.eq_dec
 end

module Coq_func_Map = EMap(Coq_func_Eq)

type func_map = func_val option Coq_func_Map.t

(** val init_func_map : func_map **)

let init_func_map =
  Coq_func_Map.init None

(** val get_function_registry : func_key -> func_map -> func_val option **)

let get_function_registry =
  Coq_func_Map.get

(** val max_call_depth : usize **)

let max_call_depth =
  Int64.repr (Zpos (XO (XO (XO (XO (XO (XO XH)))))))

(** val stack_frame_size : usize **)

let stack_frame_size =
  Int64.repr (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
    XH)))))))))))))

type callFrame = { caller_saved_registers : Int64.int list;
                   frame_pointer : Int64.int; target_pc : Int64.int }

(** val reg_eq : bpf_ireg -> bpf_ireg -> bool **)

let reg_eq x y =
  match x with
  | BR0 -> (match y with
            | BR0 -> true
            | _ -> false)
  | BR1 -> (match y with
            | BR1 -> true
            | _ -> false)
  | BR2 -> (match y with
            | BR2 -> true
            | _ -> false)
  | BR3 -> (match y with
            | BR3 -> true
            | _ -> false)
  | BR4 -> (match y with
            | BR4 -> true
            | _ -> false)
  | BR5 -> (match y with
            | BR5 -> true
            | _ -> false)
  | BR6 -> (match y with
            | BR6 -> true
            | _ -> false)
  | BR7 -> (match y with
            | BR7 -> true
            | _ -> false)
  | BR8 -> (match y with
            | BR8 -> true
            | _ -> false)
  | BR9 -> (match y with
            | BR9 -> true
            | _ -> false)
  | BR10 -> (match y with
             | BR10 -> true
             | _ -> false)

module Coq_reg_Eq =
 struct
  type t = bpf_ireg

  (** val eq : bpf_ireg -> bpf_ireg -> bool **)

  let eq =
    reg_eq
 end

module Coq_reg_Map = EMap(Coq_reg_Eq)

type reg_map = Int64.int Coq_reg_Map.t

type block = positive

(** val eq_block : positive -> positive -> bool **)

let eq_block =
  peq

type val0 =
| Vundef
| Vint of Int.int
| Vlong of Int64.int
| Vfloat of float
| Vsingle of float32
| Vptr of block * Ptrofs.int

module Val =
 struct
  (** val eq : val0 -> val0 -> bool **)

  let eq x y =
    match x with
    | Vundef -> (match y with
                 | Vundef -> true
                 | _ -> false)
    | Vint x0 -> (match y with
                  | Vint i0 -> Int.eq_dec x0 i0
                  | _ -> false)
    | Vlong x0 -> (match y with
                   | Vlong i0 -> Int64.eq_dec x0 i0
                   | _ -> false)
    | Vfloat x0 -> (match y with
                    | Vfloat f0 -> Float.eq_dec x0 f0
                    | _ -> false)
    | Vsingle x0 ->
      (match y with
       | Vsingle f0 -> Float32.eq_dec x0 f0
       | _ -> false)
    | Vptr (x0, x1) ->
      (match y with
       | Vptr (b0, i0) ->
         if eq_block x0 b0 then Ptrofs.eq_dec x1 i0 else false
       | _ -> false)

  (** val load_result : memory_chunk -> val0 -> val0 **)

  let load_result chunk v =
    match chunk with
    | Mint8signed ->
      (match v with
       | Vint n0 -> Vint (Int.sign_ext (Zpos (XO (XO (XO XH)))) n0)
       | _ -> Vundef)
    | Mint8unsigned ->
      (match v with
       | Vint n0 -> Vint (Int.zero_ext (Zpos (XO (XO (XO XH)))) n0)
       | _ -> Vundef)
    | Mint16signed ->
      (match v with
       | Vint n0 -> Vint (Int.sign_ext (Zpos (XO (XO (XO (XO XH))))) n0)
       | _ -> Vundef)
    | Mint16unsigned ->
      (match v with
       | Vint n0 -> Vint (Int.zero_ext (Zpos (XO (XO (XO (XO XH))))) n0)
       | _ -> Vundef)
    | Mint32 ->
      (match v with
       | Vint n0 -> Vint n0
       | Vptr (b, ofs) -> if ptr64 then Vundef else Vptr (b, ofs)
       | _ -> Vundef)
    | Mint64 ->
      (match v with
       | Vlong n0 -> Vlong n0
       | Vptr (b, ofs) -> if ptr64 then Vptr (b, ofs) else Vundef
       | _ -> Vundef)
    | Mfloat32 -> (match v with
                   | Vsingle f -> Vsingle f
                   | _ -> Vundef)
    | Mfloat64 -> (match v with
                   | Vfloat f -> Vfloat f
                   | _ -> Vundef)
    | Many32 ->
      (match v with
       | Vint _ -> v
       | Vsingle _ -> v
       | Vptr (_, _) -> if ptr64 then Vundef else v
       | _ -> Vundef)
    | Many64 -> v
 end

(** val size_chunk : memory_chunk -> z **)

let size_chunk = function
| Mint8signed -> Zpos XH
| Mint8unsigned -> Zpos XH
| Mint16signed -> Zpos (XO XH)
| Mint16unsigned -> Zpos (XO XH)
| Mint32 -> Zpos (XO (XO XH))
| Mfloat32 -> Zpos (XO (XO XH))
| Many32 -> Zpos (XO (XO XH))
| _ -> Zpos (XO (XO (XO XH)))

(** val size_chunk_nat : memory_chunk -> nat **)

let size_chunk_nat chunk =
  Z.to_nat (size_chunk chunk)

(** val align_chunk : memory_chunk -> z **)

let align_chunk = function
| Mint8signed -> Zpos XH
| Mint8unsigned -> Zpos XH
| Mint16signed -> Zpos (XO XH)
| Mint16unsigned -> Zpos (XO XH)
| Mint64 -> Zpos (XO (XO (XO XH)))
| _ -> Zpos (XO (XO XH))

type quantity =
| Q32
| Q64

(** val quantity_eq : quantity -> quantity -> bool **)

let quantity_eq q1 q2 =
  match q1 with
  | Q32 -> (match q2 with
            | Q32 -> true
            | Q64 -> false)
  | Q64 -> (match q2 with
            | Q32 -> false
            | Q64 -> true)

(** val size_quantity_nat : quantity -> nat **)

let size_quantity_nat = function
| Q32 -> S (S (S (S O)))
| Q64 -> S (S (S (S (S (S (S (S O)))))))

type memval =
| Undef
| Byte of Byte.int
| Fragment of val0 * quantity * nat

(** val bytes_of_int : nat -> z -> Byte.int list **)

let rec bytes_of_int n0 x =
  match n0 with
  | O -> []
  | S m ->
    (Byte.repr x)::(bytes_of_int m
                     (Z.div x (Zpos (XO (XO (XO (XO (XO (XO (XO (XO
                       XH)))))))))))

(** val int_of_bytes : Byte.int list -> z **)

let rec int_of_bytes = function
| [] -> Z0
| b::l' ->
  Z.add (Byte.unsigned b)
    (Z.mul (int_of_bytes l') (Zpos (XO (XO (XO (XO (XO (XO (XO (XO
      XH))))))))))

(** val rev_if_be : Byte.int list -> Byte.int list **)

let rev_if_be l =
  if big_endian then rev l else l

(** val encode_int : nat -> z -> Byte.int list **)

let encode_int sz x =
  rev_if_be (bytes_of_int sz x)

(** val decode_int : Byte.int list -> z **)

let decode_int b =
  int_of_bytes (rev_if_be b)

(** val inj_bytes : Byte.int list -> memval list **)

let inj_bytes bl =
  map (fun x -> Byte x) bl

(** val proj_bytes : memval list -> Byte.int list option **)

let rec proj_bytes = function
| [] -> Some []
| m::vl' ->
  (match m with
   | Byte b ->
     (match proj_bytes vl' with
      | Some bl -> Some (b::bl)
      | None -> None)
   | _ -> None)

(** val inj_value_rec : nat -> val0 -> quantity -> memval list **)

let rec inj_value_rec n0 v q =
  match n0 with
  | O -> []
  | S m -> (Fragment (v, q, m))::(inj_value_rec m v q)

(** val inj_value : quantity -> val0 -> memval list **)

let inj_value q v =
  inj_value_rec (size_quantity_nat q) v q

(** val check_value : nat -> val0 -> quantity -> memval list -> bool **)

let rec check_value n0 v q vl =
  match n0 with
  | O -> (match vl with
          | [] -> true
          | _::_ -> false)
  | S m ->
    (match vl with
     | [] -> false
     | m0::vl' ->
       (match m0 with
        | Fragment (v', q', m') ->
          (&&)
            ((&&)
              ((&&) (proj_sumbool (Val.eq v v'))
                (proj_sumbool (quantity_eq q q'))) (Nat.eqb m m'))
            (check_value m v q vl')
        | _ -> false))

(** val proj_value : quantity -> memval list -> val0 **)

let proj_value q vl = match vl with
| [] -> Vundef
| m::_ ->
  (match m with
   | Fragment (v, _, _) ->
     if check_value (size_quantity_nat q) v q vl then v else Vundef
   | _ -> Vundef)

(** val encode_val : memory_chunk -> val0 -> memval list **)

let encode_val chunk v = match v with
| Vundef ->
  (match chunk with
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> repeat Undef (size_chunk_nat chunk))
| Vint n0 ->
  (match chunk with
   | Mint8signed -> inj_bytes (encode_int (S O) (Int.unsigned n0))
   | Mint8unsigned -> inj_bytes (encode_int (S O) (Int.unsigned n0))
   | Mint16signed -> inj_bytes (encode_int (S (S O)) (Int.unsigned n0))
   | Mint16unsigned -> inj_bytes (encode_int (S (S O)) (Int.unsigned n0))
   | Mint32 -> inj_bytes (encode_int (S (S (S (S O)))) (Int.unsigned n0))
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> repeat Undef (size_chunk_nat chunk))
| Vlong n0 ->
  (match chunk with
   | Mint64 ->
     inj_bytes
       (encode_int (S (S (S (S (S (S (S (S O)))))))) (Int64.unsigned n0))
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> repeat Undef (size_chunk_nat chunk))
| Vfloat n0 ->
  (match chunk with
   | Mfloat64 ->
     inj_bytes
       (encode_int (S (S (S (S (S (S (S (S O))))))))
         (Int64.unsigned (Float.to_bits n0)))
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> repeat Undef (size_chunk_nat chunk))
| Vsingle n0 ->
  (match chunk with
   | Mfloat32 ->
     inj_bytes
       (encode_int (S (S (S (S O)))) (Int.unsigned (Float32.to_bits n0)))
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> repeat Undef (size_chunk_nat chunk))
| Vptr (_, _) ->
  (match chunk with
   | Mint32 ->
     if ptr64 then repeat Undef (S (S (S (S O)))) else inj_value Q32 v
   | Mint64 ->
     if ptr64
     then inj_value Q64 v
     else repeat Undef (S (S (S (S (S (S (S (S O))))))))
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> repeat Undef (size_chunk_nat chunk))

(** val decode_val : memory_chunk -> memval list -> val0 **)

let decode_val chunk vl =
  match proj_bytes vl with
  | Some bl ->
    (match chunk with
     | Mint8signed ->
       Vint (Int.sign_ext (Zpos (XO (XO (XO XH)))) (Int.repr (decode_int bl)))
     | Mint8unsigned ->
       Vint (Int.zero_ext (Zpos (XO (XO (XO XH)))) (Int.repr (decode_int bl)))
     | Mint16signed ->
       Vint
         (Int.sign_ext (Zpos (XO (XO (XO (XO XH)))))
           (Int.repr (decode_int bl)))
     | Mint16unsigned ->
       Vint
         (Int.zero_ext (Zpos (XO (XO (XO (XO XH)))))
           (Int.repr (decode_int bl)))
     | Mint32 -> Vint (Int.repr (decode_int bl))
     | Mint64 -> Vlong (Int64.repr (decode_int bl))
     | Mfloat32 -> Vsingle (Float32.of_bits (Int.repr (decode_int bl)))
     | Mfloat64 -> Vfloat (Float.of_bits (Int64.repr (decode_int bl)))
     | _ -> Vundef)
  | None ->
    (match chunk with
     | Mint32 ->
       if ptr64 then Vundef else Val.load_result chunk (proj_value Q32 vl)
     | Mint64 ->
       if ptr64 then Val.load_result chunk (proj_value Q64 vl) else Vundef
     | Many32 -> Val.load_result chunk (proj_value Q32 vl)
     | Many64 -> Val.load_result chunk (proj_value Q64 vl)
     | _ -> Vundef)

type permission =
| Freeable
| Writable
| Readable
| Nonempty

type perm_kind =
| Max
| Cur

module Mem =
 struct
  type mem' = { mem_contents : memval ZMap.t PMap.t;
                mem_access : (z -> perm_kind -> permission option) PMap.t;
                nextblock : block }

  (** val mem_contents : mem' -> memval ZMap.t PMap.t **)

  let mem_contents m =
    m.mem_contents

  (** val mem_access :
      mem' -> (z -> perm_kind -> permission option) PMap.t **)

  let mem_access m =
    m.mem_access

  (** val nextblock : mem' -> block **)

  let nextblock m =
    m.nextblock

  type mem = mem'

  (** val perm_order_dec : permission -> permission -> bool **)

  let perm_order_dec p1 p2 =
    match p1 with
    | Freeable -> true
    | Writable -> (match p2 with
                   | Freeable -> false
                   | _ -> true)
    | Readable ->
      (match p2 with
       | Freeable -> false
       | Writable -> false
       | _ -> true)
    | Nonempty -> (match p2 with
                   | Nonempty -> true
                   | _ -> false)

  (** val perm_order'_dec : permission option -> permission -> bool **)

  let perm_order'_dec op p =
    match op with
    | Some p0 -> perm_order_dec p0 p
    | None -> false

  (** val perm_dec : mem -> block -> z -> perm_kind -> permission -> bool **)

  let perm_dec m b ofs k p =
    perm_order'_dec (PMap.get b m.mem_access ofs k) p

  (** val range_perm_dec :
      mem -> block -> z -> z -> perm_kind -> permission -> bool **)

  let rec range_perm_dec m b lo hi k p =
    let s = zlt lo hi in
    if s
    then let s0 = perm_dec m b lo k p in
         if s0
         then let y = Z.add lo (Zpos XH) in range_perm_dec m b y hi k p
         else false
    else true

  (** val valid_access_dec :
      mem -> memory_chunk -> block -> z -> permission -> bool **)

  let valid_access_dec m chunk b ofs p =
    let s = range_perm_dec m b ofs (Z.add ofs (size_chunk chunk)) Cur p in
    if s then zdivide_dec (align_chunk chunk) ofs else false

  (** val empty : mem **)

  let empty =
    { mem_contents = (PMap.init (ZMap.init Undef)); mem_access =
      (PMap.init (fun _ _ -> None)); nextblock = XH }

  (** val getN : nat -> z -> memval ZMap.t -> memval list **)

  let rec getN n0 p c =
    match n0 with
    | O -> []
    | S n' -> (ZMap.get p c)::(getN n' (Z.add p (Zpos XH)) c)

  (** val load : memory_chunk -> mem -> block -> z -> val0 option **)

  let load chunk m b ofs =
    if valid_access_dec m chunk b ofs Readable
    then Some
           (decode_val chunk
             (getN (size_chunk_nat chunk) ofs (PMap.get b m.mem_contents)))
    else None

  (** val loadv : memory_chunk -> mem -> val0 -> val0 option **)

  let loadv chunk m = function
  | Vptr (b, ofs) -> load chunk m b (Ptrofs.unsigned ofs)
  | _ -> None

  (** val setN : memval list -> z -> memval ZMap.t -> memval ZMap.t **)

  let rec setN vl p c =
    match vl with
    | [] -> c
    | v::vl' -> setN vl' (Z.add p (Zpos XH)) (ZMap.set p v c)

  (** val store : memory_chunk -> mem -> block -> z -> val0 -> mem option **)

  let store chunk m b ofs v =
    if valid_access_dec m chunk b ofs Writable
    then Some { mem_contents =
           (PMap.set b
             (setN (encode_val chunk v) ofs (PMap.get b m.mem_contents))
             m.mem_contents); mem_access = m.mem_access; nextblock =
           m.nextblock }
    else None

  (** val storev : memory_chunk -> mem -> val0 -> val0 -> mem option **)

  let storev chunk m addr v =
    match addr with
    | Vptr (b, ofs) -> store chunk m b (Ptrofs.unsigned ofs) v
    | _ -> None

  (** val storebytes : mem -> block -> z -> memval list -> mem option **)

  let storebytes m b ofs bytes =
    if range_perm_dec m b ofs (Z.add ofs (Z.of_nat (length bytes))) Cur
         Writable
    then Some { mem_contents =
           (PMap.set b (setN bytes ofs (PMap.get b m.mem_contents))
             m.mem_contents); mem_access = m.mem_access; nextblock =
           m.nextblock }
    else None
 end

(** val decode_bpf : Int64.int -> nat -> nat -> Int64.int **)

let decode_bpf ins from size0 =
  Int64.unsigned_bitfield_extract (Z.of_nat from) (Z.of_nat size0) ins

(** val rbpf_decoder_one :
    Byte.int -> nat -> nat -> Int16.int -> Int.int -> bpf_instruction option **)

let rbpf_decoder_one opc dv sv off imm =
  if Z.eqb (Byte.unsigned opc) (Z.of_nat (S (S (S (S (S (S (S O))))))))
  then if Nat.eqb dv (S (S (S (S (S (S (S (S (S (S (S O)))))))))))
       then Some (BPF_ADD_STK imm)
       else (match nat_to_bpf_ireg dv with
             | Some dst -> Some (BPF_ALU64 (BPF_ADD, dst, (SOImm imm)))
             | None -> None)
  else (match nat_to_bpf_ireg dv with
        | Some dst ->
          (match nat_to_bpf_ireg sv with
           | Some src ->
             if Z.eqb (Byte.unsigned opc)
                  (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S
                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
             then Some (BPF_LDX (Mint8unsigned, dst, src, off))
             else if Z.eqb (Byte.unsigned opc)
                       (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S
                         O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                  then Some (BPF_LDX (Mint16unsigned, dst, src, off))
                  else if Z.eqb (Byte.unsigned opc)
                            (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S
                              O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                       then Some (BPF_LDX (Mint32, dst, src, off))
                       else if Z.eqb (Byte.unsigned opc)
                                 (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S
                                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                   (S (S (S (S (S (S (S (S (S (S (S (S
                                   O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                            then Some (BPF_LDX (Mint64, dst, src, off))
                            else if Z.eqb (Byte.unsigned opc)
                                      (Z.of_nat (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S
                                        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                 then Some (BPF_ST (Mint8unsigned, dst,
                                        (SOImm imm), off))
                                 else if Z.eqb (Byte.unsigned opc)
                                           (Z.of_nat (S (S (S (S (S (S (S (S
                                             (S (S (S (S (S (S (S (S (S (S (S
                                             (S (S (S (S (S (S (S (S (S (S (S
                                             (S (S (S (S (S (S (S (S (S (S (S
                                             (S (S (S (S (S (S (S (S (S (S (S
                                             (S (S (S (S (S (S (S (S (S (S (S
                                             (S (S (S (S (S (S (S (S (S (S (S
                                             (S (S (S (S (S (S (S (S (S (S (S
                                             (S (S (S (S (S (S (S (S (S (S (S
                                             (S (S (S (S (S (S (S (S (S (S
                                             O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                      then Some (BPF_ST (Mint16unsigned, dst,
                                             (SOImm imm), off))
                                      else if Z.eqb (Byte.unsigned opc)
                                                (Z.of_nat (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S
                                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                           then Some (BPF_ST (Mint32, dst,
                                                  (SOImm imm), off))
                                           else if Z.eqb (Byte.unsigned opc)
                                                     (Z.of_nat (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S (S (S
                                                       (S (S (S (S (S
                                                       O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                then Some (BPF_ST (Mint64,
                                                       dst, (SOImm imm), off))
                                                else if Z.eqb
                                                          (Byte.unsigned opc)
                                                          (Z.of_nat (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S
                                                            O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                     then Some (BPF_ST
                                                            (Mint8unsigned,
                                                            dst, (SOReg src),
                                                            off))
                                                     else if Z.eqb
                                                               (Byte.unsigned
                                                                 opc)
                                                               (Z.of_nat (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S (S (S
                                                                 (S (S
                                                                 O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                          then Some (BPF_ST
                                                                 (Mint16unsigned,
                                                                 dst, (SOReg
                                                                 src), off))
                                                          else if Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                               then Some
                                                                    (BPF_ST
                                                                    (Mint32,
                                                                    dst,
                                                                    (SOReg
                                                                    src),
                                                                    off))
                                                               else if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ST
                                                                    (Mint64,
                                                                    dst,
                                                                    (SOReg
                                                                    src),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S O)))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_ADD,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_ADD,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_SUB,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_SUB,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_MUL,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_MUL,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_DIV,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_DIV,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_OR,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_OR,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_AND,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_AND,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_LSH,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_LSH,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_RSH,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_RSH,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_NEG32_REG
                                                                    dst)
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_MOD,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_MOD,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_XOR,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_XOR,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_MOV,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_MOV,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_ARSH,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU
                                                                    (BPF_ARSH,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_LE
                                                                    (dst,
                                                                    imm))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_BE
                                                                    (dst,
                                                                    imm))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_ADD,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_ADD,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_SUB,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_SUB,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_MUL,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_MUL,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_DIV,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_DIV,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_OR,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_OR,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_AND,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_AND,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_LSH,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_LSH,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_RSH,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_RSH,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_NEG64_REG
                                                                    dst)
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_MOD,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_MOD,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_XOR,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_XOR,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_MOV,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_MOV,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_ARSH,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_ALU64
                                                                    (BPF_ARSH,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_HOR64_IMM
                                                                    (dst,
                                                                    imm))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR
                                                                    (BPF_LMUL,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR
                                                                    (BPF_LMUL,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR64
                                                                    (BPF_LMUL,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR64
                                                                    (BPF_LMUL,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR2
                                                                    (BPF_UHMUL,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR2
                                                                    (BPF_UHMUL,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR2
                                                                    (BPF_SHMUL,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR2
                                                                    (BPF_SHMUL,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR
                                                                    (BPF_UDIV,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR
                                                                    (BPF_UDIV,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR64
                                                                    (BPF_UDIV,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR64
                                                                    (BPF_UDIV,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR
                                                                    (BPF_UREM,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR
                                                                    (BPF_UREM,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR64
                                                                    (BPF_UREM,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR64
                                                                    (BPF_UREM,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR
                                                                    (BPF_SDIV,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR
                                                                    (BPF_SDIV,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR64
                                                                    (BPF_SDIV,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR64
                                                                    (BPF_SDIV,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR
                                                                    (BPF_SREM,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR
                                                                    (BPF_SREM,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR64
                                                                    (BPF_SREM,
                                                                    dst,
                                                                    (SOImm
                                                                    imm)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_PQR64
                                                                    (BPF_SREM,
                                                                    dst,
                                                                    (SOReg
                                                                    src)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JA
                                                                    off)
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (Eq0,
                                                                    dst,
                                                                    (SOImm
                                                                    imm),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (Eq0,
                                                                    dst,
                                                                    (SOReg
                                                                    src),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (Gt0,
                                                                    dst,
                                                                    (SOImm
                                                                    imm),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (Gt0,
                                                                    dst,
                                                                    (SOReg
                                                                    src),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (Ge, dst,
                                                                    (SOImm
                                                                    imm),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (Ge, dst,
                                                                    (SOReg
                                                                    src),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (Lt0,
                                                                    dst,
                                                                    (SOImm
                                                                    imm),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (Lt0,
                                                                    dst,
                                                                    (SOReg
                                                                    src),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (Le, dst,
                                                                    (SOImm
                                                                    imm),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (Le, dst,
                                                                    (SOReg
                                                                    src),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (SEt,
                                                                    dst,
                                                                    (SOImm
                                                                    imm),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (SEt,
                                                                    dst,
                                                                    (SOReg
                                                                    src),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (Ne, dst,
                                                                    (SOImm
                                                                    imm),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (Ne, dst,
                                                                    (SOReg
                                                                    src),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (SGt,
                                                                    dst,
                                                                    (SOImm
                                                                    imm),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (SGt,
                                                                    dst,
                                                                    (SOReg
                                                                    src),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (SGe,
                                                                    dst,
                                                                    (SOImm
                                                                    imm),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (SGe,
                                                                    dst,
                                                                    (SOReg
                                                                    src),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (SLt,
                                                                    dst,
                                                                    (SOImm
                                                                    imm),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (SLt,
                                                                    dst,
                                                                    (SOReg
                                                                    src),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (SLe,
                                                                    dst,
                                                                    (SOImm
                                                                    imm),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_JUMP
                                                                    (SLe,
                                                                    dst,
                                                                    (SOReg
                                                                    src),
                                                                    off))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_CALL_REG
                                                                    (src,
                                                                    imm))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    (BPF_CALL_IMM
                                                                    (src,
                                                                    imm))
                                                                    else 
                                                                    if 
                                                                    Z.eqb
                                                                    (Byte.unsigned
                                                                    opc)
                                                                    (Z.of_nat
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    then 
                                                                    Some
                                                                    BPF_EXIT
                                                                    else None
           | None -> None)
        | None -> None)

(** val rbpf_decoder : nat -> Int64.int list -> bpf_instruction option **)

let rbpf_decoder pc l =
  match nth_error l pc with
  | Some data ->
    let op =
      Byte.repr
        (Int64.unsigned (decode_bpf data O (S (S (S (S (S (S (S (S O))))))))))
    in
    let dst =
      Z.to_nat
        (Int64.unsigned
          (decode_bpf data (S (S (S (S (S (S (S (S O)))))))) (S (S (S (S
            O))))))
    in
    let src =
      Z.to_nat
        (Int64.unsigned
          (decode_bpf data (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))
            (S (S (S (S O))))))
    in
    let off =
      Int16.repr
        (Int64.signed
          (decode_bpf data (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))
    in
    let imm =
      Int.repr
        (Int64.signed
          (decode_bpf data (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))) (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))
    in
    if Z.eqb (Byte.unsigned op)
         (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S O)))))))))))))))))))))))))
    then (match nth_error l (S pc) with
          | Some data2 ->
            let imm2 =
              Int.repr
                (Int64.signed
                  (decode_bpf data2 (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))))))))))))))))))))) (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S O))))))))))))))))))))))))))))))))))
            in
            (match nat_to_bpf_ireg dst with
             | Some dst_r -> Some (BPF_LD_IMM (dst_r, imm, imm2))
             | None -> None)
          | None -> None)
    else rbpf_decoder_one op dst src off imm
  | None -> None

type stack_state = { call_depth : Int64.int; stack_pointer : Int64.int;
                     call_frames : callFrame list }

(** val eval_reg : bpf_ireg -> reg_map -> Int64.int **)

let eval_reg =
  Coq_reg_Map.get

(** val create_list : nat -> 'a1 -> 'a1 list **)

let rec create_list n0 def_v =
  match n0 with
  | O -> []
  | S n' -> def_v::(create_list n' def_v)

(** val init_stack_state : stack_state **)

let init_stack_state =
  { call_depth = (Int64.repr Z0); stack_pointer =
    (Int64.add mM_STACK_START (Int64.mul stack_frame_size max_call_depth));
    call_frames =
    (create_list (Z.to_nat (Int64.unsigned max_call_depth))
      { caller_saved_registers = []; frame_pointer = (Int64.repr Z0);
      target_pc = (Int64.repr Z0) }) }

type bpf_state =
| BPF_OK of Int64.int * reg_map * Mem.mem * stack_state * sBPFV * func_map
   * Int64.int * Int64.int
| BPF_Success of Int64.int
| BPF_EFlag
| BPF_Err

(** val init_reg_map : reg_map **)

let init_reg_map =
  Coq_reg_Map.init (Int64.repr Z0)

(** val init_bpf_state :
    reg_map -> Mem.mem -> Int64.int -> sBPFV -> bpf_state **)

let init_bpf_state rm m v sbpfv =
  BPF_OK ((Int64.repr Z0),
    (Coq_reg_Map.set BR10
      (Int64.add mM_STACK_START (Int64.mul stack_frame_size max_call_depth))
      rm), m, init_stack_state, sbpfv, init_func_map, (Int64.repr Z0), v)

type 'a option2 =
| NOK
| OKS of 'a
| OKN

(** val eval_snd_op_u32 : snd_op -> reg_map -> Int.int **)

let eval_snd_op_u32 so rm =
  match so with
  | SOImm i -> i
  | SOReg r -> Int.repr (Int64.unsigned (rm r))

(** val eval_snd_op_i32 : snd_op -> reg_map -> Int.int **)

let eval_snd_op_i32 so rm =
  match so with
  | SOImm i -> i
  | SOReg r -> Int.repr (Int64.signed (rm r))

(** val eval_snd_op_u64 : snd_op -> reg_map -> Int64.int **)

let eval_snd_op_u64 so rm =
  match so with
  | SOImm i -> Int64.repr (Int.signed i)
  | SOReg r -> rm r

(** val eval_snd_op_i64 : snd_op -> reg_map -> Int64.int **)

let eval_snd_op_i64 so rm =
  match so with
  | SOImm i -> Int64.repr (Int.signed i)
  | SOReg r -> rm r

(** val eval_alu32_aux1 :
    binop -> bpf_ireg -> snd_op -> reg_map -> bool -> reg_map option2 **)

let eval_alu32_aux1 bop dst sop rm is_v1 =
  let dv = Int.repr (Int64.signed (eval_reg dst rm)) in
  let sv = eval_snd_op_i32 sop rm in
  (match bop with
   | BPF_ADD ->
     OKS (Coq_reg_Map.set dst (Int64.repr (Int.signed (Int.add dv sv))) rm)
   | BPF_SUB ->
     (match sop with
      | SOImm _ ->
        if is_v1
        then OKS
               (Coq_reg_Map.set dst (Int64.repr (Int.signed (Int.sub dv sv)))
                 rm)
        else OKS
               (Coq_reg_Map.set dst (Int64.repr (Int.signed (Int.sub sv dv)))
                 rm)
      | SOReg _ ->
        OKS (Coq_reg_Map.set dst (Int64.repr (Int.signed (Int.sub dv sv))) rm))
   | BPF_MUL ->
     OKS (Coq_reg_Map.set dst (Int64.repr (Int.signed (Int.mul dv sv))) rm)
   | _ -> OKN)

(** val eval_alu32_aux2 :
    binop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2 **)

let eval_alu32_aux2 bop dst sop rm =
  let dv = Int.repr (Int64.unsigned (eval_reg dst rm)) in
  let sv = eval_snd_op_u32 sop rm in
  (match bop with
   | BPF_DIV ->
     if Int.eq sv Int.zero
     then (match sop with
           | SOImm _ -> NOK
           | SOReg _ -> OKN)
     else OKS
            (Coq_reg_Map.set dst (Int64.repr (Int.unsigned (Int.divu dv sv)))
              rm)
   | BPF_OR ->
     OKS
       (Coq_reg_Map.set dst (Int64.repr (Int.unsigned (Int.coq_or sv dv))) rm)
   | BPF_AND ->
     OKS
       (Coq_reg_Map.set dst (Int64.repr (Int.unsigned (Int.coq_and sv dv)))
         rm)
   | BPF_LSH ->
     OKS
       (Coq_reg_Map.set dst
         (Int64.repr
           (Int.unsigned
             (Int.shl dv
               (Int.coq_and sv
                 (Int.repr
                   (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     O))))))))))))))))))))))))))))))))))))) rm)
   | BPF_RSH ->
     OKS
       (Coq_reg_Map.set dst
         (Int64.repr
           (Int.unsigned
             (Int.shru dv
               (Int.coq_and sv
                 (Int.repr
                   (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     O))))))))))))))))))))))))))))))))))))) rm)
   | BPF_MOD ->
     if Int.eq sv Int.zero
     then (match sop with
           | SOImm _ -> NOK
           | SOReg _ -> OKN)
     else OKS
            (Coq_reg_Map.set dst (Int64.repr (Int.unsigned (Int.modu dv sv)))
              rm)
   | BPF_XOR ->
     OKS (Coq_reg_Map.set dst (Int64.repr (Int.unsigned (Int.xor sv dv))) rm)
   | BPF_MOV -> OKS (Coq_reg_Map.set dst (Int64.repr (Int.unsigned sv)) rm)
   | _ -> OKN)

(** val eval_alu32_aux3 :
    binop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2 **)

let eval_alu32_aux3 bop dst sop rm =
  let dv = Int.repr (Int64.signed (eval_reg dst rm)) in
  let sv =
    Int.coq_and (eval_snd_op_u32 sop rm)
      (Int.repr
        (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))
  in
  (match bop with
   | BPF_ARSH ->
     OKS
       (Coq_reg_Map.set dst
         (Int64.repr
           (Int.unsigned
             (Int.coq_and
               (Int.shr dv
                 (Int.coq_and sv
                   (Int.repr
                     (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       O)))))))))))))))))))))))))))))))))))
               (Int.repr Int.max_unsigned)))) rm)
   | _ -> OKN)

(** val eval_alu32 :
    binop -> bpf_ireg -> snd_op -> reg_map -> bool -> reg_map option2 **)

let eval_alu32 bop dst sop rm is_v1 =
  match bop with
  | BPF_ADD -> eval_alu32_aux1 bop dst sop rm is_v1
  | BPF_SUB -> eval_alu32_aux1 bop dst sop rm is_v1
  | BPF_MUL -> if is_v1 then eval_alu32_aux1 bop dst sop rm is_v1 else OKN
  | BPF_DIV -> if is_v1 then eval_alu32_aux2 bop dst sop rm else OKN
  | BPF_MOD -> if is_v1 then eval_alu32_aux2 bop dst sop rm else OKN
  | BPF_ARSH -> eval_alu32_aux3 bop dst sop rm
  | _ -> eval_alu32_aux2 bop dst sop rm

(** val eval_alu64_aux1 :
    binop -> bpf_ireg -> snd_op -> reg_map -> bool -> reg_map option2 **)

let eval_alu64_aux1 bop dst sop rm is_v1 =
  let dv = eval_reg dst rm in
  let sv = eval_snd_op_u64 sop rm in
  (match bop with
   | BPF_ADD -> OKS (Coq_reg_Map.set dst (Int64.add dv sv) rm)
   | BPF_SUB ->
     (match sop with
      | SOImm _ ->
        if is_v1
        then OKS (Coq_reg_Map.set dst (Int64.sub dv sv) rm)
        else OKS (Coq_reg_Map.set dst (Int64.sub sv dv) rm)
      | SOReg _ -> OKS (Coq_reg_Map.set dst (Int64.sub dv sv) rm))
   | BPF_MUL -> OKS (Coq_reg_Map.set dst (Int64.mul dv sv) rm)
   | BPF_DIV ->
     if Int64.eq sv Int64.zero
     then (match sop with
           | SOImm _ -> NOK
           | SOReg _ -> OKN)
     else OKS (Coq_reg_Map.set dst (Int64.divu dv sv) rm)
   | BPF_OR -> OKS (Coq_reg_Map.set dst (Int64.coq_or sv dv) rm)
   | BPF_AND -> OKS (Coq_reg_Map.set dst (Int64.coq_and sv dv) rm)
   | BPF_MOD ->
     if Int64.eq sv Int64.zero
     then (match sop with
           | SOImm _ -> NOK
           | SOReg _ -> OKN)
     else OKS (Coq_reg_Map.set dst (Int64.modu dv sv) rm)
   | BPF_XOR -> OKS (Coq_reg_Map.set dst (Int64.xor sv dv) rm)
   | BPF_MOV -> OKS (Coq_reg_Map.set dst sv rm)
   | _ -> OKN)

(** val eval_alu64_aux2 :
    binop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2 **)

let eval_alu64_aux2 bop dst sop rm =
  let dv = eval_reg dst rm in
  let sv =
    Int.coq_and (eval_snd_op_i32 sop rm)
      (Int.repr
        (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  in
  (match bop with
   | BPF_LSH ->
     OKS
       (Coq_reg_Map.set dst (Int64.shl dv (Int64.repr (Int.unsigned sv))) rm)
   | BPF_RSH ->
     OKS
       (Coq_reg_Map.set dst (Int64.shru dv (Int64.repr (Int.unsigned sv))) rm)
   | _ -> OKN)

(** val eval_alu64_aux3 :
    binop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2 **)

let eval_alu64_aux3 bop dst sop rm =
  let dv = eval_reg dst rm in
  let sv =
    Int.coq_and (eval_snd_op_u32 sop rm)
      (Int.repr
        (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  in
  (match bop with
   | BPF_ARSH ->
     OKS
       (Coq_reg_Map.set dst (Int64.shr dv (Int64.repr (Int.unsigned sv))) rm)
   | _ -> OKN)

(** val eval_add64_imm_R10 :
    Int.int -> stack_state -> bool -> stack_state option **)

let eval_add64_imm_R10 i ss is_v1 =
  let sp = ss.stack_pointer in
  if negb is_v1
  then Some { call_depth = ss.call_depth; stack_pointer =
         (Int64.add sp (Int64.repr (Int.signed i))); call_frames =
         ss.call_frames }
  else None

(** val eval_alu64 :
    binop -> bpf_ireg -> snd_op -> reg_map -> bool -> reg_map option2 **)

let eval_alu64 bop dst sop rm is_v1 =
  match bop with
  | BPF_MUL -> if is_v1 then eval_alu64_aux1 bop dst sop rm is_v1 else OKN
  | BPF_DIV -> if is_v1 then eval_alu64_aux1 bop dst sop rm is_v1 else OKN
  | BPF_LSH -> eval_alu64_aux2 bop dst sop rm
  | BPF_RSH -> eval_alu64_aux2 bop dst sop rm
  | BPF_MOD -> if is_v1 then eval_alu64_aux1 bop dst sop rm is_v1 else OKN
  | BPF_ARSH -> eval_alu64_aux3 bop dst sop rm
  | _ -> eval_alu64_aux1 bop dst sop rm is_v1

(** val eval_neg32 : bpf_ireg -> reg_map -> bool -> reg_map option2 **)

let eval_neg32 dst rm = function
| true ->
  let dv = Int.repr (Int64.signed (eval_reg dst rm)) in
  OKS
  (Coq_reg_Map.set dst
    (Int64.coq_and (Int64.repr (Int.unsigned (Int.neg dv)))
      (Int64.repr Int.max_unsigned)) rm)
| false -> OKN

(** val eval_neg64 : bpf_ireg -> reg_map -> bool -> reg_map option2 **)

let eval_neg64 dst rm = function
| true ->
  let dv = eval_reg dst rm in OKS (Coq_reg_Map.set dst (Int64.neg dv) rm)
| false -> OKN

(** val eval_le :
    bpf_ireg -> Int.int -> reg_map -> bool -> reg_map option2 **)

let eval_le dst imm rm = function
| true ->
  let dv = eval_reg dst rm in
  if Int.eq imm
       (Int.repr
         (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))
  then (match word_of_byte_list
                (byte_list_of_word (Int16.repr (Int64.unsigned dv))) with
        | Some v ->
          OKS (Coq_reg_Map.set dst (Int64.repr (Int16.unsigned v)) rm)
        | None -> OKN)
  else if Int.eq imm
            (Int.repr
              (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                O))))))))))))))))))))))))))))))))))
       then (match int_of_byte_list
                     (byte_list_of_int (Int.repr (Int64.unsigned dv))) with
             | Some v ->
               OKS (Coq_reg_Map.set dst (Int64.repr (Int.unsigned v)) rm)
             | None -> OKN)
       else if Int.eq imm
                 (Int.repr
                   (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S
                     O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            then (match int64_of_byte_list (byte_list_of_int64 dv) with
                  | Some v -> OKS (Coq_reg_Map.set dst v rm)
                  | None -> OKN)
            else OKN
| false -> OKN

(** val eval_be :
    bpf_ireg -> Int.int -> reg_map -> bool -> reg_map option2 **)

let eval_be dst imm rm = function
| true ->
  let dv = eval_reg dst rm in
  if Int.eq imm
       (Int.repr
         (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))
  then (match word_of_byte_list
                (rev (byte_list_of_word (Int16.repr (Int64.unsigned dv)))) with
        | Some v ->
          OKS (Coq_reg_Map.set dst (Int64.repr (Int16.unsigned v)) rm)
        | None -> OKN)
  else if Int.eq imm
            (Int.repr
              (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                O))))))))))))))))))))))))))))))))))
       then (match int_of_byte_list
                     (rev (byte_list_of_int (Int.repr (Int64.unsigned dv)))) with
             | Some v ->
               OKS (Coq_reg_Map.set dst (Int64.repr (Int.unsigned v)) rm)
             | None -> OKN)
       else if Int.eq imm
                 (Int.repr
                   (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S
                     O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            then (match int64_of_byte_list (rev (byte_list_of_int64 dv)) with
                  | Some v -> OKS (Coq_reg_Map.set dst v rm)
                  | None -> OKN)
            else OKN
| false -> OKN

(** val eval_hor64 :
    bpf_ireg -> Int.int -> reg_map -> bool -> reg_map option2 **)

let eval_hor64 dst imm rm = function
| true -> OKN
| false ->
  let dv = eval_reg dst rm in
  let dv2 =
    Int64.coq_or dv
      (Int64.shl (Int64.repr (Int.unsigned imm))
        (Int64.repr
          (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))
  in
  OKS (Coq_reg_Map.set dst dv2 rm)

(** val eval_pqr32_aux1 :
    pqrop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2 **)

let eval_pqr32_aux1 pop dst sop rm =
  let dv = Int.repr (Int64.signed (eval_reg dst rm)) in
  let sv = eval_snd_op_i32 sop rm in
  (match pop with
   | BPF_LMUL ->
     OKS (Coq_reg_Map.set dst (Int64.repr (Int.unsigned (Int.mul dv sv))) rm)
   | BPF_SDIV ->
     if Z.eqb (Int.signed sv) Z0
     then (match sop with
           | SOImm _ -> NOK
           | SOReg _ -> OKN)
     else OKS
            (Coq_reg_Map.set dst (Int64.repr (Int.signed (Int.divs dv sv)))
              rm)
   | BPF_SREM ->
     if Z.eqb (Int.signed sv) Z0
     then (match sop with
           | SOImm _ -> NOK
           | SOReg _ -> OKN)
     else OKS
            (Coq_reg_Map.set dst (Int64.repr (Int.signed (Int.mods dv sv)))
              rm)
   | _ -> OKN)

(** val eval_pqr32_aux2 :
    pqrop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2 **)

let eval_pqr32_aux2 pop dst sop rm =
  let dv = Int.repr (Int64.unsigned (eval_reg dst rm)) in
  let sv = eval_snd_op_u32 sop rm in
  (match pop with
   | BPF_UDIV ->
     if Z.eqb (Int.signed sv) Z0
     then (match sop with
           | SOImm _ -> NOK
           | SOReg _ -> OKN)
     else OKS
            (Coq_reg_Map.set dst (Int64.repr (Int.unsigned (Int.divu dv sv)))
              rm)
   | BPF_UREM ->
     if Z.eqb (Int.signed sv) Z0
     then (match sop with
           | SOImm _ -> NOK
           | SOReg _ -> OKN)
     else OKS
            (Coq_reg_Map.set dst (Int64.repr (Int.unsigned (Int.modu dv sv)))
              rm)
   | _ -> OKN)

(** val eval_pqr32 :
    pqrop -> bpf_ireg -> snd_op -> reg_map -> bool -> reg_map option2 **)

let eval_pqr32 pop dst sop rm = function
| true -> OKN
| false ->
  (match pop with
   | BPF_UDIV -> eval_pqr32_aux2 pop dst sop rm
   | BPF_UREM -> eval_pqr32_aux2 pop dst sop rm
   | _ -> eval_pqr32_aux1 pop dst sop rm)

(** val eval_pqr64_aux1 :
    pqrop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2 **)

let eval_pqr64_aux1 pop dst sop rm =
  let dv = eval_reg dst rm in
  let sv = eval_snd_op_u64 sop rm in
  (match pop with
   | BPF_LMUL -> OKS (Coq_reg_Map.set dst (Int64.mul dv sv) rm)
   | BPF_UDIV ->
     if Z.eqb (Int64.signed sv) Z0
     then (match sop with
           | SOImm _ -> NOK
           | SOReg _ -> OKN)
     else OKS (Coq_reg_Map.set dst (Int64.divu dv sv) rm)
   | BPF_UREM ->
     if Z.eqb (Int64.signed sv) Z0
     then (match sop with
           | SOImm _ -> NOK
           | SOReg _ -> OKN)
     else OKS (Coq_reg_Map.set dst (Int64.modu dv sv) rm)
   | _ -> OKN)

(** val eval_pqr64_aux2 :
    pqrop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2 **)

let eval_pqr64_aux2 pop dst sop rm =
  let dv = eval_reg dst rm in
  let sv = eval_snd_op_i64 sop rm in
  (match pop with
   | BPF_SDIV ->
     if Z.eqb (Int64.signed sv) Z0
     then (match sop with
           | SOImm _ -> NOK
           | SOReg _ -> OKN)
     else OKS (Coq_reg_Map.set dst (Int64.divs dv sv) rm)
   | BPF_SREM ->
     if Z.eqb (Int64.signed sv) Z0
     then (match sop with
           | SOImm _ -> NOK
           | SOReg _ -> OKN)
     else OKS (Coq_reg_Map.set dst (Int64.mods dv sv) rm)
   | _ -> OKN)

(** val eval_pqr64 :
    pqrop -> bpf_ireg -> snd_op -> reg_map -> bool -> reg_map option2 **)

let eval_pqr64 pop dst sop rm = function
| true -> OKN
| false ->
  (match pop with
   | BPF_SDIV -> eval_pqr64_aux2 pop dst sop rm
   | BPF_SREM -> eval_pqr64_aux2 pop dst sop rm
   | _ -> eval_pqr64_aux1 pop dst sop rm)

(** val eval_pqr64_2 :
    pqrop2 -> bpf_ireg -> snd_op -> reg_map -> bool -> reg_map option2 **)

let eval_pqr64_2 pop2 dst sop rm = function
| true -> OKN
| false ->
  let dv = eval_reg dst rm in
  let sv = eval_snd_op_u64 sop rm in
  (match pop2 with
   | BPF_UHMUL -> OKS (Coq_reg_Map.set dst (Int64.mulhu dv sv) rm)
   | BPF_SHMUL -> OKS (Coq_reg_Map.set dst (Int64.mulhs dv sv) rm))

(** val concrete_addr_to_abstract_addr : Int64.int -> block -> val0 **)

let concrete_addr_to_abstract_addr addr b =
  Vptr (b, (Ptrofs.of_int64u addr))

(** val memory_chunk_value_of_int64 : memory_chunk -> Int64.int -> val0 **)

let memory_chunk_value_of_int64 mc v =
  match mc with
  | Mint8unsigned -> Vint (Int.repr (Int64.unsigned v))
  | Mint16unsigned -> Vint (Int.repr (Int64.unsigned v))
  | Mint32 -> Vint (Int.repr (Int64.unsigned v))
  | Mint64 -> Vlong v
  | _ -> Vundef

(** val eval_store :
    memory_chunk -> bpf_ireg -> snd_op -> off_ty -> reg_map -> Mem.mem ->
    block -> Mem.mem option **)

let eval_store chk dst sop off rm m b =
  let dv = eval_reg dst rm in
  let vm_addr = Int64.add dv (Int64.repr (Int16.signed off)) in
  let sv = eval_snd_op_u64 sop rm in
  Mem.storev chk m (concrete_addr_to_abstract_addr vm_addr b)
    (memory_chunk_value_of_int64 chk sv)

(** val eval_load :
    memory_chunk -> bpf_ireg -> bpf_ireg -> off_ty -> reg_map -> Mem.mem ->
    block -> reg_map option **)

let eval_load chk dst src off rm m b =
  let sv = eval_snd_op_u64 (SOReg src) rm in
  let vm_addr = Int64.add sv (Int64.repr (Int16.signed off)) in
  let v = Mem.loadv chk m (concrete_addr_to_abstract_addr vm_addr b) in
  (match v with
   | Some v0 ->
     (match v0 with
      | Vint v' ->
        Some (Coq_reg_Map.set dst (Int64.repr (Int.unsigned v')) rm)
      | Vlong v' -> Some (Coq_reg_Map.set dst v' rm)
      | _ -> None)
   | None -> None)

(** val eval_load_imm :
    bpf_ireg -> Int.int -> Int.int -> reg_map -> reg_map **)

let eval_load_imm dst imm1 imm2 rm =
  let v =
    Int64.coq_or
      (Int64.coq_and (Int64.repr (Int.unsigned imm1))
        (Int64.repr (Zpos (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI
          (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI
          (XI XH))))))))))))))))))))))))))))))))))
      (bit_left_shift_int64 (Int64.repr (Int.unsigned imm2)) (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S O)))))))))))))))))))))))))))))))))
  in
  Coq_reg_Map.set dst v rm

(** val eval_jmp : condition -> bpf_ireg -> snd_op -> reg_map -> bool **)

let eval_jmp cond dst sop rm =
  let udv = eval_reg dst rm in
  let usv = eval_snd_op_u64 sop rm in
  let sdv = eval_reg dst rm in
  let ssv = eval_snd_op_i64 sop rm in
  (match cond with
   | Eq0 -> Int64.eq udv usv
   | Gt0 -> Int64.cmpu Cgt udv usv
   | Ge -> Int64.cmpu Cge udv usv
   | Lt0 -> Int64.cmpu Clt udv usv
   | Le -> Int64.cmpu Cle udv usv
   | SEt -> negb ((||) (Int64.eq udv Int64.zero) (Int64.eq usv Int64.zero))
   | Ne -> negb (Int64.eq udv usv)
   | SGt -> Int64.cmp Cgt sdv ssv
   | SGe -> Int64.cmp Cge sdv ssv
   | SLt -> Int64.cmp Clt sdv ssv
   | SLe -> Int64.cmp Cle sdv ssv)

(** val list_update : 'a1 list -> nat -> 'a1 -> 'a1 list **)

let list_update l n0 x =
  app (firstn n0 l) (app (x::[]) (skipn (S n0) l))

(** val push_frame :
    reg_map -> stack_state -> bool -> Int64.int -> bool -> stack_state
    option * reg_map **)

let push_frame rm ss is_v1 pc enable_stack_frame_gaps =
  let npc = Int64.add pc (Int64.repr (Zpos XH)) in
  let fp = eval_reg BR10 rm in
  let caller =
    (eval_reg BR6 rm)::((eval_reg BR7 rm)::((eval_reg BR8 rm)::((eval_reg BR9
                                                                  rm)::[])))
  in
  let frame = { caller_saved_registers = caller; frame_pointer = fp;
    target_pc = npc }
  in
  let update1 = Int64.add ss.call_depth (Int64.repr (Zpos XH)) in
  if Int64.eq update1 max_call_depth
  then (None, rm)
  else let update2 =
         if is_v1
         then if enable_stack_frame_gaps
              then Int64.add ss.stack_pointer
                     (Int64.mul stack_frame_size (Int64.repr (Zpos (XO XH))))
              else Int64.add ss.stack_pointer stack_frame_size
         else ss.stack_pointer
       in
       let update3 =
         list_update ss.call_frames (Z.to_nat (Int64.unsigned ss.call_depth))
           frame
       in
       let new_stack_state = { call_depth = update1; stack_pointer = update2;
         call_frames = update3 }
       in
       let updated_reg_map = Coq_reg_Map.set BR10 update2 rm in
       ((Some new_stack_state), updated_reg_map)

(** val eval_call_reg :
    bpf_ireg -> Int.int -> reg_map -> stack_state -> bool -> Int64.int ->
    func_map -> bool -> Int64.int -> ((Int64.int * reg_map) * stack_state)
    option **)

let eval_call_reg src imm rm ss is_v1 pc _ enable_stack_frame_gaps program_vm_addr =
  match nat_to_bpf_ireg (Z.to_nat (Int.unsigned imm)) with
  | Some iv ->
    let pc1 = if is_v1 then eval_reg iv rm else eval_reg src rm in
    let (x, rm') = push_frame rm ss is_v1 pc enable_stack_frame_gaps in
    (match x with
     | Some ss' ->
       if Int64.lt pc1 program_vm_addr
       then None
       else let next_pc =
              Int64.divu (Int64.sub pc1 program_vm_addr)
                (Int64.repr (Z.of_nat iNSN_SIZE))
            in
            Some ((next_pc, rm'), ss')
     | None -> None)
  | None -> None

(** val eval_call_imm :
    Int64.int -> bpf_ireg -> Int.int -> reg_map -> stack_state -> bool ->
    func_map -> bool -> ((Int64.int * reg_map) * stack_state) option **)

let eval_call_imm pc src imm rm ss is_v1 fm enable_stack_frame_gaps =
  let pc_option =
    if reg_eq src BR0
    then get_function_registry imm fm
    else Some (Int64.repr (Int.signed imm))
  in
  (match pc_option with
   | Some npc ->
     let (x, rm') = push_frame rm ss is_v1 pc enable_stack_frame_gaps in
     (match x with
      | Some ss' -> Some ((npc, rm'), ss')
      | None -> None)
   | None -> None)

(** val eval_exit :
    reg_map -> stack_state -> bool -> (Int64.int * reg_map) * stack_state **)

let eval_exit rm ss is_v1 =
  let x = Int64.sub ss.call_depth Int64.one in
  (match nth_error ss.call_frames (Z.to_nat (Int64.unsigned x)) with
   | Some frame ->
     let rm' =
       Coq_reg_Map.set BR10 frame.frame_pointer
         (Coq_reg_Map.set BR9
           (nth (S (S (S O))) frame.caller_saved_registers Int64.zero)
           (Coq_reg_Map.set BR8
             (nth (S (S O)) frame.caller_saved_registers Int64.zero)
             (Coq_reg_Map.set BR7
               (nth (S O) frame.caller_saved_registers Int64.zero)
               (Coq_reg_Map.set BR6
                 (nth O frame.caller_saved_registers Int64.zero) rm))))
     in
     let y =
       if is_v1
       then Int64.sub ss.stack_pointer
              (Int64.mul (Int64.repr (Zpos (XO XH))) stack_frame_size)
       else ss.stack_pointer
     in
     let z0 = removelast ss.call_frames in
     let ss' = { call_depth = x; stack_pointer = y; call_frames = z0 } in
     let pc = frame.target_pc in ((pc, rm'), ss')
   | None -> ((Int64.zero, rm), ss))

(** val step :
    Int64.int -> bpf_instruction -> reg_map -> Mem.mem -> stack_state ->
    sBPFV -> func_map -> bool -> Int64.int -> Int64.int -> Int64.int -> block
    -> bpf_state **)

let step pc ins rm m ss sv fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu b =
  let is_v1 = match sv with
              | V1 -> true
              | V2 -> false in
  (match ins with
   | BPF_LD_IMM (dst, imm1, imm2) ->
     let rm' = eval_load_imm dst imm1 imm2 rm in
     BPF_OK ((Int64.add pc (Int64.repr (Zpos (XO XH)))), rm', m, ss, sv, fm,
     (Int64.add cur_cu Int64.one), remain_cu)
   | BPF_LDX (chk, dst, sop, off) ->
     (match eval_load chk dst sop off rm m b with
      | Some rm' ->
        BPF_OK ((Int64.add pc Int64.one), rm', m, ss, sv, fm,
          (Int64.add cur_cu Int64.one), remain_cu)
      | None -> BPF_Err)
   | BPF_ST (chk, dst, sop, off) ->
     (match eval_store chk dst sop off rm m b with
      | Some m' ->
        BPF_OK ((Int64.add pc Int64.one), rm, m', ss, sv, fm,
          (Int64.add cur_cu Int64.one), remain_cu)
      | None -> BPF_Err)
   | BPF_ADD_STK i ->
     (match eval_add64_imm_R10 i ss is_v1 with
      | Some _ ->
        BPF_OK ((Int64.add pc Int64.one), rm, m, ss, sv, fm,
          (Int64.add cur_cu Int64.one), remain_cu)
      | None -> BPF_Err)
   | BPF_ALU (bop, d, sop) ->
     (match eval_alu32 bop d sop rm is_v1 with
      | NOK -> BPF_Err
      | OKS rm' ->
        BPF_OK ((Int64.add pc Int64.one), rm', m, ss, sv, fm,
          (Int64.add cur_cu Int64.one), remain_cu)
      | OKN -> BPF_EFlag)
   | BPF_NEG32_REG dst ->
     (match eval_neg32 dst rm is_v1 with
      | NOK -> BPF_Err
      | OKS rm' ->
        BPF_OK ((Int64.add pc Int64.one), rm', m, ss, sv, fm,
          (Int64.add cur_cu Int64.one), remain_cu)
      | OKN -> BPF_EFlag)
   | BPF_LE (dst, imm) ->
     (match eval_le dst imm rm is_v1 with
      | NOK -> BPF_Err
      | OKS rm' ->
        BPF_OK ((Int64.add pc Int64.one), rm', m, ss, sv, fm,
          (Int64.add cur_cu Int64.one), remain_cu)
      | OKN -> BPF_EFlag)
   | BPF_BE (dst, imm) ->
     (match eval_be dst imm rm is_v1 with
      | NOK -> BPF_Err
      | OKS rm' ->
        BPF_OK ((Int64.add pc Int64.one), rm', m, ss, sv, fm,
          (Int64.add cur_cu Int64.one), remain_cu)
      | OKN -> BPF_EFlag)
   | BPF_ALU64 (bop, d, sop) ->
     (match eval_alu64 bop d sop rm is_v1 with
      | NOK -> BPF_Err
      | OKS rm' ->
        BPF_OK ((Int64.add pc Int64.one), rm', m, ss, sv, fm,
          (Int64.add cur_cu Int64.one), remain_cu)
      | OKN -> BPF_EFlag)
   | BPF_NEG64_REG dst ->
     (match eval_neg64 dst rm is_v1 with
      | NOK -> BPF_Err
      | OKS rm' ->
        BPF_OK ((Int64.add pc Int64.one), rm', m, ss, sv, fm,
          (Int64.add cur_cu Int64.one), remain_cu)
      | OKN -> BPF_EFlag)
   | BPF_HOR64_IMM (dst, imm) ->
     (match eval_hor64 dst imm rm is_v1 with
      | NOK -> BPF_Err
      | OKS rm' ->
        BPF_OK ((Int64.add pc Int64.one), rm', m, ss, sv, fm,
          (Int64.add cur_cu Int64.one), remain_cu)
      | OKN -> BPF_EFlag)
   | BPF_PQR (pop, dst, sop) ->
     (match eval_pqr32 pop dst sop rm is_v1 with
      | NOK -> BPF_Err
      | OKS rm' ->
        BPF_OK ((Int64.add pc Int64.one), rm', m, ss, sv, fm,
          (Int64.add cur_cu Int64.one), remain_cu)
      | OKN -> BPF_EFlag)
   | BPF_PQR64 (pop, dst, sop) ->
     (match eval_pqr64 pop dst sop rm is_v1 with
      | NOK -> BPF_Err
      | OKS rm' ->
        BPF_OK ((Int64.add pc Int64.one), rm', m, ss, sv, fm,
          (Int64.add cur_cu Int64.one), remain_cu)
      | OKN -> BPF_EFlag)
   | BPF_PQR2 (pop, dst, sop) ->
     (match eval_pqr64_2 pop dst sop rm is_v1 with
      | NOK -> BPF_Err
      | OKS rm' ->
        BPF_OK ((Int64.add pc Int64.one), rm', m, ss, sv, fm,
          (Int64.add cur_cu Int64.one), remain_cu)
      | OKN -> BPF_EFlag)
   | BPF_JA off ->
     BPF_OK
       ((Int64.add (Int64.add pc (Int64.repr (Int16.signed off))) Int64.one),
       rm, m, ss, sv, fm, (Int64.add cur_cu Int64.one), remain_cu)
   | BPF_JUMP (cond, bpf_ireg0, sop, off) ->
     if eval_jmp cond bpf_ireg0 sop rm
     then BPF_OK
            ((Int64.add (Int64.add pc (Int64.repr (Int16.signed off)))
               Int64.one), rm, m, ss, sv, fm, (Int64.add cur_cu Int64.one),
            remain_cu)
     else BPF_OK ((Int64.add pc Int64.one), rm, m, ss, sv, fm,
            (Int64.add cur_cu Int64.one), remain_cu)
   | BPF_CALL_REG (src, imm) ->
     (match eval_call_reg src imm rm ss is_v1 pc fm enable_stack_frame_gaps
              program_vm_addr with
      | Some p ->
        let (p0, ss') = p in
        let (pc', rm') = p0 in
        BPF_OK (pc', rm', m, ss', sv, fm, (Int64.add cur_cu Int64.one),
        remain_cu)
      | None -> BPF_EFlag)
   | BPF_CALL_IMM (src, imm) ->
     (match eval_call_imm pc src imm rm ss is_v1 fm enable_stack_frame_gaps with
      | Some p ->
        let (p0, _) = p in
        let (pc', rm') = p0 in
        BPF_OK (pc', rm', m, ss, sv, fm, (Int64.add cur_cu Int64.one),
        remain_cu)
      | None -> BPF_EFlag)
   | BPF_EXIT ->
     if Int64.eq ss.call_depth Int64.zero
     then if Int64.cmpu Cgt cur_cu remain_cu
          then BPF_EFlag
          else BPF_Success (rm BR0)
     else let result = eval_exit rm ss is_v1 in
          let (p, _) = result in
          let (pc', rm') = p in
          BPF_OK (pc', rm', m, ss, sv, fm, (Int64.add cur_cu Int64.one),
          remain_cu))

(** val bpf_interp :
    nat -> bpf_bin -> bpf_state -> bool -> Int64.int -> block -> bpf_state **)

let rec bpf_interp n0 prog st enable_stack_frame_gaps program_vm_addr b =
  match n0 with
  | O -> BPF_EFlag
  | S n' ->
    (match st with
     | BPF_OK (pc, rm, m, ss, sv, fm, cur_cu, remain_cu) ->
       if Int64.lt pc (Int64.repr (Z.of_nat (length prog)))
       then if Int64.cmp Cge cur_cu remain_cu
            then BPF_EFlag
            else (match rbpf_decoder (Z.to_nat (Int64.unsigned pc)) prog with
                  | Some ins ->
                    let st1 =
                      step pc ins rm m ss sv fm enable_stack_frame_gaps
                        program_vm_addr cur_cu remain_cu b
                    in
                    bpf_interp n' prog st1 enable_stack_frame_gaps
                      program_vm_addr b
                  | None -> BPF_EFlag)
       else BPF_EFlag
     | x -> x)

(** val z_to_byte_list : z list -> Byte.int list **)

let z_to_byte_list l =
  map Byte.repr l

(** val get_bytes : Byte.int list -> memval list **)

let rec get_bytes = function
| [] -> []
| h::t0 -> (Byte h)::(get_bytes t0)

(** val byte_list_to_mem :
    Byte.int list -> Mem.mem -> block -> z -> Mem.mem **)

let byte_list_to_mem l m b ofs =
  match Mem.storebytes m b ofs (get_bytes l) with
  | Some m' -> m'
  | None -> m

(** val z_to_int64_list : z list -> Int64.int list **)

let z_to_int64_list l =
  map Int64.repr l

(** val bpf_interp_test :
    z list -> z list -> z list -> z -> z -> z -> bool -> bool **)

let bpf_interp_test lp lm _ v fuel res is_ok =
  let st1 =
    bpf_interp
      (Z.to_nat (Int64.unsigned (Int64.add (Int64.repr fuel) Int64.one)))
      (z_to_int64_list lp)
      (init_bpf_state init_reg_map
        (byte_list_to_mem (z_to_byte_list lm) Mem.empty XH Z0)
        (Int64.add (Int64.repr fuel) Int64.one)
        (if Int64.eq (Int64.repr v) Int64.one then V1 else V2)) true
      (Int64.repr (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO XH)))))))))))))))))))))))))))))))))) XH
  in
  if is_ok
  then (match st1 with
        | BPF_Success v' -> Z.eqb (Int64.unsigned v') res
        | _ -> false)
  else (match st1 with
        | BPF_EFlag -> true
        | _ -> false)
