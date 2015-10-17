(* Stringmap -- applicative string maps as Patricia trees *)
signature Stringmap =
sig
  eqtype 'a dict

  exception NotFound
  exception Extend

  val empty      : 'a dict
  val fromList   : (string * 'a) list -> 'a dict
  val extend     : 'a dict * string * 'a -> 'a dict
  val merge      : 'a dict * 'a dict -> 'a dict
  val insert     : 'a dict * string * 'a -> 'a dict
  val insertList : 'a dict * (string * 'a) list -> 'a dict
  val extendList : 'a dict * (string * 'a) list -> 'a dict
  val peekKey    : 'a dict * string -> (string * 'a) option
  val findKey    : 'a dict * string -> string * 'a
  val find       : 'a dict * string -> 'a
  val found      : 'a dict * string -> bool
  val peek       : 'a dict * string -> 'a option
  val remove     : 'a dict * string -> 'a dict * 'a
  val removeList : 'a dict * string list -> 'a dict
  val numItems   : 'a dict -> int
  val listItems  : 'a dict -> (string * 'a) list
  val sortItems  : ('a * 'a -> order) -> 'a dict -> (string * 'a) list
  val keys       : 'a dict -> string list
  val isEmpty    : 'a dict -> bool
  val map        : (string * 'a -> 'b) -> 'a dict -> 'b dict
  val transform  : ('a -> 'b) -> 'a dict -> 'b dict
  val all        : ('a -> bool) -> 'a dict -> bool
  val exists     : ('a -> bool) -> 'a dict -> bool

  val printer : int -> 'b -> 'a dict -> PolyML.pretty
end

(*
   ['a dict] is the type of applicative maps from domain type string
   to range type 'a.  They are implemented as Patricia trees.

   [empty] a new empty map.

   [fromList xs] returns a map that contains the (index, value)
   pairs in xs.  It is equivalent to insertList (empty, xs).

   [extend(m, i, v)] extends map m to map i to v.  If m already maps i then
   raises Extend.

   [insert(m, i, v)] extends (or modifies) map m to map i to v.

   [insertList(m, xs)] extends (or modifies) map m with the (index,
   value) pairs in xs.  (It is equivalent to foldl (fn ((i, v), m) =>
   insert (m, i, v)) m xs.)  Note that later list entries will
   overwrite earlier entries for the same index.

   [findKey (m, k)] returns (k, v) if m maps k to v;
   otherwise, raises NotFound.

   [find (m, k)] returns v if m maps k to v; otherwise raises NotFound.

   [peek(m, k)] returns SOME v if m maps k to v; otherwise returns NONE.

   [remove(m, k)] removes k from the domain of m and returns the
   modified map and the element v corresponding to k.  Raises NotFound
   if k is not in the domain of m.

   [numItems m] returns the number of entries in m (that is, the size
   of the domain of m).

   [listItems m] returns a list of the entries (k, v) of keys k and
   the corresponding values v in m, in order of increasing key values.

   [isEmpty m] returns true if the map m is empty, and false otherwise.

   [map f m] returns a new map whose entries have form (k, f(k,v)),
   where (k, v) is an entry in m.

   [transform f m] returns a new map whose entries have form (k, f v),
   where (k, v) is an entry in m.
*)

structure Stringmap :> Stringmap =
struct

datatype 'a ptree =
     Empty
   | Leaf of string * 'a
   | Branch of string * int * 'a ptree * 'a ptree

type 'a dict = 'a ptree * int

fun fst (x, _) = x
fun snd (_, x) = x

fun bitOfChar c n =
   Word8.andb
     (Word8.>> (Word8.fromInt (Char.ord c), Word.andb (Word.fromInt n, 0wx7)),
      0wx1) = 0wx1

fun bitOfString s n =
   if s = ""
      then raise Fail "bitOfString"
   else let
           val q = n div 8
        in
           q < String.size s andalso bitOfChar (String.sub (s, q)) n
        end

fun numItems ((_, n): 'a dict) = n

exception NotFound

fun findKey ((t, _): 'a dict, key) =
   let
      val key' = key ^ "\001"
      fun find Empty = raise NotFound
        | find (Leaf (k, d)) = if k = key' then (k, d) else raise NotFound
        | find (Branch (p, m, left, right)) =
             find (if bitOfString key' m then left else right)
   in
      find t
   end

fun peekKey x = SOME (findKey x) handle NotFound => NONE
fun find x = #2 (findKey x)
fun found x = (find x; true) handle NotFound => false
fun peek x = SOME (find x) handle NotFound => NONE

fun all P ((t, _): 'a dict) =
   let
      fun allP Empty = true
        | allP (Leaf (_, d)) = P d
        | allP (Branch (_, _, left, right)) = allP left andalso allP right
   in
      allP t
   end

fun exists P ((t, _): 'a dict) =
   let
      fun existsP Empty = false
        | existsP (Leaf (_, d)) = P d
        | existsP (Branch (_, _, left, right)) =
            existsP left orelse existsP right
   in
      existsP t
   end

local
   fun mask (c, mask) =
      (String.str o Char.chr o Word8.toInt o Word8.andb)
         (Word8.fromInt (Char.ord c), mask)

   fun masked (c, n) =
     case n mod 8 of
        0 => ""
      | 1 => mask (c, 0w1)
      | 2 => mask (c, 0w3)
      | 3 => mask (c, 0w7)
      | 4 => mask (c, 0w15)
      | 5 => mask (c, 0w31)
      | 6 => mask (c, 0w63)
      | 7 => mask (c, 0w127)
      | _ => raise Fail ""
in
   fun stringPrefix (s, n) =
      let
         val q = n div 8
      in
         if q < String.size s
            then String.substring (s, 0, q) ^ masked (String.sub (s, q), n)
         else s
      end
end

exception Extend

local
   fun seek P = let fun iter i = if P i then i else iter (i + 1) in iter 0 end

   fun branchingBit s1 s2 =
      if s1 = "" orelse s2 = "" orelse s1 = s2
         then raise Fail "branchingBit"
      else
         let
            val sz1 = String.size s1
            val sz2 = String.size s2
            val n = Int.min (sz1, sz2)
            val i = seek (fn i =>
                       n <= i orelse String.sub (s1, i) <> String.sub (s2, i))
            val c1 = if sz1 <= i then #"\000" else String.sub (s1, i)
            val c2 = if sz2 <= i then #"\000" else String.sub (s2, i)
            val j = seek (fn i => 7 < i orelse bitOfChar c1 i <> bitOfChar c2 i)
         in
            8 * i + j
         end

   fun join (p0, t0, p1, t1) =
      let
         val m = branchingBit p0 p1
         val p = stringPrefix (p0, m)
      in
         if bitOfString p0 m
            then Branch (p, m, t0, t1)
         else Branch (p, m, t1, t0)
      end

   fun ins ext ((tree, n): 'a dict, key, data) =
      let
         val added = ref true
         val key' = key ^ "\001"
         val new = Leaf (key', data)
         fun add Empty = new
           | add (t as Leaf (k, _)) =
                if k = key'
                   then (added := false; new)
                else join (key', new, k, t)
           | add (t as Branch (p, m, left, right)) =
                if p = stringPrefix (key', m)
                   then if bitOfString key' m
                           then Branch (p, m, add left, right)
                        else Branch (p, m, left, add right)
                else join (key', new, p, t)
      in
         (add tree, if !added then n + 1 else if ext then raise Extend else n)
      end
in
   fun insert x = ins false x
   fun extend x = ins true x
end

val empty = (Empty, 0): 'a dict

val isEmpty =
   fn (Empty, _): 'a dict => true
    | _ => false

fun insertList (m, xs) = List.foldl (fn ((i, v), m) => insert (m, i, v)) m xs
fun extendList (m, xs) = List.foldl (fn ((i, v), m) => extend (m, i, v)) m xs

fun fromList xs = insertList (empty, xs)

local
   val branch =
      fn (_, _, Empty, t) => t
       | (_, _, t, Empty) => t
       | (p, m, t0, t1) => Branch (p, m, t0, t1)
in
   fun remove ((tree, n): 'a dict, key) =
      let
         val key' = key ^ "\001"
         val found = ref (fn () => raise NotFound)
         fun del Empty = raise NotFound
           | del (Leaf (k, d)) = if k = key'
                                    then (found := (fn () => d); Empty)
                                 else raise NotFound
           | del (Branch (p, m, left, right)) =
                if p = stringPrefix (key', m)
                   then if bitOfString key' m
                           then branch (p, m, del left, right)
                        else branch (p, m, left, del right)
                else raise NotFound
      in
         ((del tree, n - 1), !found ())
      end
end

fun del (k, d) = fst (remove (d, k))

fun removeList (d, l) = List.foldl del d l

fun removeEndChar s =
   if s = ""
      then raise Fail "removeEndChar"
   else String.substring (s, 0, String.size s - 1)

fun map f ((tree, n): 'a dict) =
   let
      fun mapf Empty = Empty
        | mapf (Leaf (k, d)) = Leaf (k, f (removeEndChar k, d))
        | mapf (Branch (p, m, left, right)) =
            Branch (p, m, mapf left, mapf right)
   in
      (mapf tree, n): 'b dict
   end

fun transform f = map (fn (_, d) => f d)

local
   fun merge a =
      fn ([], r) => List.revAppend (a, r)
       | (r, []) => List.revAppend (a, r)
       | (l1 as h1::t1, l2 as h2::t2) =>
            if String.< (fst h1, fst h2)
               then merge (h1::a) (t1, l2)
            else merge (h2::a) (l1, t2)
in
   fun listItems ((tree, _): 'a dict) =
      let
         fun list Empty = []
           | list (Leaf (k, d)) = [(removeEndChar k, d)]
           | list (Branch (_, _, left, right)) =
                let
                   val l1 = list left
                   val l2 = list right
                in
                   merge [] (l1, l2)
                end
      in
         list tree
      end
end

fun keys t = List.map fst (listItems t)

fun merge (t1, t2) = extendList (t1, listItems t2)

local
   fun merge cmp =
      let
         fun mrg a =
            fn ([], r) => List.revAppend (a, r)
             | (r, []) => List.revAppend (a, r)
             | (l1 as h1::t1, l2 as h2::t2) =>
                  if cmp (snd h1, snd h2) = General.LESS
                     then mrg (h1::a) (t1, l2)
                  else mrg (h2::a) (l1, t2)
      in
         mrg []
      end
in
   fun sortItems cmp ((tree, _): 'a dict) =
      let
         fun list Empty = []
           | list (Leaf (k, d)) = [(removeEndChar k, d)]
           | list (Branch (_, _, left, right)) =
                let
                   val l1 = list left
                   val l2 = list right
                in
                   merge cmp (l1, l2)
                end
      in
         list tree
      end
end

fun printer (_: int) _ (d: 'a dict) =
   PolyML.PrettyString ("<dict(" ^ Int.toString (numItems d) ^ ")>")

end

val () = PolyML.addPrettyPrinter Stringmap.printer
