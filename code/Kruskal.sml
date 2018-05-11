(* Test that words can handle numbers between 0 and 31 *)
val _ = if 5 <= Word.wordSize then () else raise (Fail ("wordSize less than 5"));

structure Uint32 : sig
  val set_bit : Word32.word -> IntInf.int -> bool -> Word32.word
  val shiftl : Word32.word -> IntInf.int -> Word32.word
  val shiftr : Word32.word -> IntInf.int -> Word32.word
  val shiftr_signed : Word32.word -> IntInf.int -> Word32.word
  val test_bit : Word32.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word32.orb (x, mask)
     else Word32.andb (x, Word32.notb mask)
  end

fun shiftl x n =
  Word32.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word32.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word32.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word32.andb (x, Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word32.fromInt 0

end; (* struct Uint32 *)


   fun array_blit src si dst di len = (
      src=dst andalso raise Fail ("array_blit: Same arrays");
      ArraySlice.copy {
        di = IntInf.toInt di,
        src = ArraySlice.slice (src,IntInf.toInt si,SOME (IntInf.toInt len)),
        dst = dst})

    fun array_nth_oo v a i () = Array.sub(a,IntInf.toInt i) handle Subscript => v | Overflow => v
    fun array_upd_oo f i x a () = 
      (Array.update(a,IntInf.toInt i,x); a) handle Subscript => f () | Overflow => f ()

    

structure Bits_Integer : sig
  val set_bit : IntInf.int -> IntInf.int -> bool -> IntInf.int
  val shiftl : IntInf.int -> IntInf.int -> IntInf.int
  val shiftr : IntInf.int -> IntInf.int -> IntInf.int
  val test_bit : IntInf.int -> IntInf.int -> bool
end = struct

val maxWord = IntInf.pow (2, Word.wordSize);

fun set_bit x n b =
  if n < maxWord then
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n)))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))))
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

fun shiftl x n =
  if n < maxWord then IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

end; (*struct Bits_Integer*)

structure Kruskal : sig
  type int
  type nat
  val kruskal : (nat * (int * nat)) list -> (unit -> ((nat * (int * nat)) list))
end = struct

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun plus_inta k l =
  Int_of_integer (IntInf.+ (integer_of_int k, integer_of_int l));

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_int = {plus = plus_inta} : int plus;

val zero_inta : int = Int_of_integer (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_int = {zero = zero_inta} : int zero;

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

val ord_int = {less_eq = less_eq_int, less = less_int} : int ord;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

type 'a ordered_ab_semigroup_add =
  {ab_semigroup_add_ordered_ab_semigroup_add : 'a ab_semigroup_add,
    order_ordered_ab_semigroup_add : 'a order};
val ab_semigroup_add_ordered_ab_semigroup_add =
  #ab_semigroup_add_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a ab_semigroup_add;
val order_ordered_ab_semigroup_add = #order_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a order;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

type 'a weight =
  {comm_monoid_add_weight : 'a comm_monoid_add,
    ordered_ab_semigroup_add_weight : 'a ordered_ab_semigroup_add,
    linorder_weight : 'a linorder};
val comm_monoid_add_weight = #comm_monoid_add_weight :
  'a weight -> 'a comm_monoid_add;
val ordered_ab_semigroup_add_weight = #ordered_ab_semigroup_add_weight :
  'a weight -> 'a ordered_ab_semigroup_add;
val linorder_weight = #linorder_weight : 'a weight -> 'a linorder;

val semigroup_add_int = {plus_semigroup_add = plus_int} : int semigroup_add;

val ab_semigroup_add_int = {semigroup_add_ab_semigroup_add = semigroup_add_int}
  : int ab_semigroup_add;

val preorder_int = {ord_preorder = ord_int} : int preorder;

val order_int = {preorder_order = preorder_int} : int order;

val ordered_ab_semigroup_add_int =
  {ab_semigroup_add_ordered_ab_semigroup_add = ab_semigroup_add_int,
    order_ordered_ab_semigroup_add = order_int}
  : int ordered_ab_semigroup_add;

val monoid_add_int =
  {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_int} :
  int monoid_add;

val comm_monoid_add_int =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int,
    monoid_add_comm_monoid_add = monoid_add_int}
  : int comm_monoid_add;

val linorder_int = {order_linorder = order_int} : int linorder;

val weight_int =
  {comm_monoid_add_weight = comm_monoid_add_int,
    ordered_ab_semigroup_add_weight = ordered_ab_semigroup_add_int,
    linorder_weight = linorder_int}
  : int weight;

datatype typerepa = Typerep of string * typerepa list;

datatype num = One | Bit0 of num | Bit1 of num;

datatype char = Zero_char | Char of num;

datatype nat = Nat of IntInf.int;

datatype 'a itself = Type;

fun typerep_nata t = Typerep ("Nat.nat", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_nat = {} : nat countable;

val typerep_nat = {typerep = typerep_nata} : nat typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  nat heap;

val one_nata : nat = Nat (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = one_nata} : nat one;

fun integer_of_nat (Nat x) = x;

fun plus_nata m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val plus_nat = {plus = plus_nata} : nat plus;

val zero_nata : nat = Nat (0 : IntInf.int);

val zero_nat = {zero = zero_nata} : nat zero;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun suc n = plus_nata n one_nata;

fun upt i j = (if less_nat i j then i :: upt (suc i) j else []);

fun max A_ a b = (if less_eq A_ a b then b else a);

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun len A_ a =
  (fn () => let
              val i = (fn () => IntInf.fromInt (Array.length a)) ();
            in
              nat_of_integer i
            end);

fun new A_ =
  (fn a => fn b => (fn () => Array.array (IntInf.toInt a, b))) o integer_of_nat;

fun nth A_ a n = (fn () => Array.sub (a, IntInf.toInt (integer_of_nat n)));

fun upd A_ i x a =
  (fn () =>
    let
      val _ =
        (fn () => Array.update (a, IntInf.toInt (integer_of_nat i), x)) ();
    in
      a
    end);

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun imp_nfoldli (x :: ls) c f s =
  (fn () =>
    let
      val b = c s ();
    in
      (if b then (fn f_ => fn () => f_ ((f x s) ()) ()) (imp_nfoldli ls c f)
        else (fn () => s))
        ()
    end)
  | imp_nfoldli [] c f s = (fn () => s);

fun op_list_prepend x = (fn a => x :: a);

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

fun uf_rep_of p i =
  (fn () => let
              val n = nth heap_nat p i ();
            in
              (if equal_nat n i then (fn () => i) else uf_rep_of p n) ()
            end);

fun uf_union u i j =
  let
    val (s, p) = u;
  in
    (fn () =>
      let
        val ci = uf_rep_of p i ();
        val cj = uf_rep_of p j ();
      in
        (if equal_nat ci cj then (fn () => (s, p))
          else (fn f_ => fn () => f_ ((nth heap_nat s ci) ()) ())
                 (fn si =>
                   (fn f_ => fn () => f_ ((nth heap_nat s cj) ()) ())
                     (fn sj =>
                       (if less_nat si sj
                         then (fn f_ => fn () => f_ ((upd heap_nat ci cj p) ())
                                ())
                                (fn _ =>
                                  (fn f_ => fn () => f_
                                    ((upd heap_nat cj (plus_nata si sj) s) ())
                                    ())
                                    (fn _ => (fn () => (s, p))))
                         else (fn f_ => fn () => f_ ((upd heap_nat cj ci p) ())
                                ())
                                (fn _ =>
                                  (fn f_ => fn () => f_
                                    ((upd heap_nat ci (plus_nata si sj) s) ())
                                    ())
                                    (fn _ => (fn () => (s, p))))))))
          ()
      end)
  end;

fun uf_init n =
  (fn () => let
              val l = (fn () => Array.fromList (upt zero_nata n)) ();
              val szl = new heap_nat n one_nata ();
            in
              (szl, l)
            end);

fun snd (x1, x2) = x2;

fun fst (x1, x2) = x1;

fun edges_less_eq B_ a b =
  less_eq
    ((ord_preorder o preorder_order o order_linorder o linorder_weight) B_)
    (fst (snd a)) (fst (snd b));

fun partition_rev p (yes, no) [] = (yes, no)
  | partition_rev p (yes, no) (x :: xs) =
    partition_rev p (if p x then (x :: yes, no) else (yes, x :: no)) xs;

fun quicksort_by_rel r sl [] = sl
  | quicksort_by_rel r sl (x :: xs) =
    let
      val (xs_s, xs_b) = partition_rev (fn y => r y x) ([], []) xs;
    in
      quicksort_by_rel r (x :: quicksort_by_rel r sl xs_b) xs_s
    end;

fun sort_edges B_ = quicksort_by_rel (edges_less_eq B_) [];

fun uf_compress i ci p =
  (if equal_nat i ci then (fn () => ())
    else (fn () => let
                     val ni = nth heap_nat p i ();
                     val _ = uf_compress ni ci p ();
                     val _ = upd heap_nat i ci p ();
                   in
                     ()
                   end));

fun uf_rep_of_c p i = (fn () => let
                                  val ci = uf_rep_of p i ();
                                  val _ = uf_compress i ci p ();
                                in
                                  ci
                                end);

fun uf_cmp u i j =
  let
    val (_, p) = u;
  in
    (fn () =>
      let
        val n = len heap_nat p ();
      in
        (if less_eq_nat n i orelse less_eq_nat n j then (fn () => false)
          else (fn f_ => fn () => f_ ((uf_rep_of_c p i) ()) ())
                 (fn ci =>
                   (fn f_ => fn () => f_ ((uf_rep_of_c p j) ()) ())
                     (fn cj => (fn () => (equal_nat ci cj)))))
          ()
      end)
  end;

fun max_node (A1_, A2_, A3_, A4_) l =
  plus A2_
    (fold (fn (u, (_, w)) => fn x =>
            max ((ord_preorder o preorder_order o order_linorder) A4_) u
              (max ((ord_preorder o preorder_order o order_linorder) A4_) w x))
      l (zero A3_))
    (one A1_);

fun kruskal x =
  (fn xi => fn () =>
    let
      val xa =
        uf_init (max_node (one_nat, plus_nat, zero_nat, linorder_nat) xi) ();
      val a =
        imp_nfoldli (sort_edges weight_int xi) (fn _ => (fn () => true))
          (fn xe => fn sigma =>
            let
              val (a1, (a1a, a2a)) = xe;
              val (a1b, a2b) = sigma;
            in
              (fn f_ => fn () => f_ ((uf_cmp a1b a1 a2a) ()) ())
                (fn x_e =>
                  (if x_e then (fn () => (a1b, a2b))
                    else (fn f_ => fn () => f_ ((uf_union a1b a1 a2a) ()) ())
                           (fn x_f =>
                             (fn () =>
                               (x_f, op_list_prepend (a1, (a1a, a2a)) a2b)))))
            end)
          (xa, []) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

end; (*struct Kruskal*)
