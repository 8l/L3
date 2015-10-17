(* -------------------------------------------------------------------------
   Primitives
   ------------------------------------------------------------------------- *)

infix 8 >> >>+ << #>> #<< >>^ >>+^ <<^ #>>^ #<<^
infix 7 &&
infix 6 || ??
infix 5 @@;

use "lib/IntExtra.sig";
use "lib/IntExtra.sml";
use "lib/Nat.sig";
use "lib/Nat.sml";
use "lib/Set.sig";
use "lib/Set.sml";
use "lib/L3.sig";
use "lib/L3.sml";
use "lib/Bitstring.sig";
use "lib/Bitstring.sml";
use "lib/BitsN.sig";
use "lib/BitsN.sml";
use "lib/FP64.sig";
use "lib/FP64.sml";

(* Extend Int *)
structure Int =
struct
   open Int
   open IntExtra
end (* structure Int *)

local
   fun printer (_: int) _ (BitsN.B (n, s)) =
      PolyML.PrettyString
         ("0x" ^ Int.fmt StringCvt.HEX n ^ "`" ^ Nat.toString s)
in
   val () = PolyML.addPrettyPrinter printer
end

(* -------------------------------------------------------------------------
   Helper functions
   ------------------------------------------------------------------------- *)

infix 9 ++
infix 8 >> >- >--
infix 6 ||
infix 3 ##
infix 0 |>

structure Lib =
struct

fun curry f x y = f (x,y)
val uncurry = L3.uncurry
val fst = L3.fst
val snd = L3.snd
val K = L3.K
val equal = L3.equal
fun I x = x
fun (f ## g) (x, y) = (f x, g y)
fun x |> f = f x
fun inc x = x := (!x) + 1
fun inc2 x = x := (!x) + 2
fun snoc x l = l @ [x]
fun mapl r = List.map (fn l => (l, r))
fun mapr l = List.map (fn r => (l, r))
val pp = PolyML.prettyPrint (print, 80)
(* PolyML.prettyRepresentation *)

fun singleton x = [x]

fun pair [a, b] = (a, b)
  | pair _ = raise Fail "pair"

fun addIndex l = ListPair.zip (l, List.tabulate (List.length l, I))

val pairCompare = L3.pairCompare
val listCompare = L3.listCompare

fun merge cmp =
   let
      fun mrg ([], a) = a
        | mrg (a, []) = a
        | mrg (A as (a::t1), B as (b::t2)) =
            if cmp (a, b) = General.LESS
               then a :: mrg(t1, B)
            else b :: mrg(A, t2)
   in
      mrg
   end

local
   fun loop (x::y::zs, xs, ys) = loop (zs, x :: xs, y :: ys)
     | loop (x::[], xs, ys) = (x::xs, ys)
     | loop ([], xs, ys) = (xs, ys)
   fun split ns = loop (List.rev ns, [], [])
in
   fun msort cmp xs =
      let
         val merge' = merge cmp
         fun ms [] = []
           | ms [x] = [x]
           | ms xs =
               let
                  val (left, right) = split xs
               in
                  merge' (ms left, ms right)
               end
      in
         ms xs
      end
end

fun total f x = SOME (f x) handle Fail _ => NONE
(* fun can f = Option.isSome o total f *)

fun takeUntil P =
   let
      fun iter a =
         fn [] => a
          | h :: t => if P h then h :: a else iter (h :: a) t
   in
      List.rev o iter []
   end

fun pluck P =
   let
      fun iter a =
         fn [] => NONE
          | h::t => if P h
                       then SOME (h, List.revAppend (a, t))
                    else iter (h :: a) t
   in
      iter []
   end

fun mapSeparate f sep =
   let
      val sep' = List.rev sep
      fun iter a =
         fn [] => List.rev a
          | [h] => List.rev a @ [f h]
          | h::t => iter (sep' @ f h :: a) t
   in
      iter []
   end

fun separate s f = String.concat o mapSeparate f [s]
fun commify f = separate ", " f

fun lastButlast l =
   let
      fun iter a =
         fn [] => raise Fail "lastButlast: empty"
          | [h] => (h, List.rev a)
          | h::l => iter (h::a) l
   in
      iter [] l
   end

fun memEq (eq:'a * 'a -> bool) i = List.exists (curry eq i)

fun insertEq eq =
   let
      val m = memEq eq
   in
      fn i => fn l => if m i l then l else i :: l
   end

fun mkSetEq eq =
   let
      val ins = insertEq eq
      fun mk [] = []
        | mk (a::rst) = ins a (mk rst)
   in
      mk
   end

fun diffEq eq =
   let
      val m = memEq eq
   in
      fn s1 => fn s2 => List.filter (fn x => not (m x s2)) s1
   end

fun setEqualEq eq =
   let
      val d = diffEq eq
   in
      fn s1 => fn s2 => List.null (d s1 s2) andalso List.null (d s2 s1)
   end

fun mem a s = Set.mem (a, s)
fun insert a s = Set.insert (a, s)
val mkSet = Set.mk
fun union s1 s2 = Set.union (s1, s2)

fun findDuplicate [] = NONE
  | findDuplicate (a::rst) = if mem a rst then SOME a else findDuplicate rst

fun nullIntersection eq =
   let
      val memeq = memEq eq
      fun nullI _ [] = true
        | nullI [] _ = true
        | nullI (h::rst) S = not (memeq h S) andalso nullI rst S
   in
      nullI
   end

fun contains c s = mem c (String.explode s)

fun removePrefix p s =
   if String.isPrefix p s
      then String.extract (s, String.size p, NONE)
   else s

(*
fun classes eq =
   let
      fun iter a =
         fn [] => List.rev a
          | h::t =>
               let
                  val (e, ne) = List.partition (curry eq h) t
               in
                  iter ((h::e)::a) ne
               end
   in
      iter []
   end
*)

fun safeLog2 x = IntInf.log2 x handle Domain => ~1

fun canFind P = Option.isSome o (List.find P)

fun findSome f =
   fn [] => NONE
    | h::t => case f h of x as SOME _ => x | NONE => findSome f t

local
   fun indexVary s =
      let
         val (nondigits, digits) =
            Substring.splitr Char.isDigit (Substring.full s)
         val n =
            if 0 < Substring.size digits
               then Option.valOf (Int.fromString (Substring.string digits)) + 1
            else 0
      in
         Substring.concat [nondigits, Substring.full (Int.toString n)]
     end

   fun variant f avoids =
      let
         fun iter s = if mem s avoids then iter (f s) else s
      in
         iter
      end
in
   val indexVariant = variant indexVary
end

fun stringToQuote s = [QUOTE (")" ^ s)]: string frag list

val quoteToString =
   let
      fun iter s =
         fn [] => s
          | QUOTE q :: t =>
              iter (s ^
                (q |> Substring.full
                   |> Substring.splitl (not o equal #")")
                   |> (fn (_, s) => Substring.slice (s, 1, NONE))
                   |> Substring.string)) t
          | ANTIQUOTE q :: t => iter (s ^ q) t
   in
      iter ""
   end

fun pickP P =
   let
      fun iter a =
         fn [] => a
          | h::t => iter (if P (h, a) then h else a) t
   in
      fn [] => raise Fail "pickP"
       | h::t => iter h t
   end

fun quote s = "\"" ^ s ^ "\""
fun printn s = print (s ^ "\n")
fun warn s = printn ("WARNING: " ^ s)

datatype ('a, 'b) choice = INL of 'a | INR of 'b

end (* structure Lib *)

open Lib

(* -------------------------------------------------------------------------
   Map
   ------------------------------------------------------------------------- *)

functor Map (type index val eq: index * index -> bool) =
struct
   exception Undefined

   type 'a map = (index * 'a) list * 'a option

   val undefined = ([], NONE) : 'a map
   fun all v = ([], SOME v) : 'a map

   fun update ((l, b) : 'a map, a, d) =
      let
         val l' = List.filter (fn (c, _) => not (eq (a, c))) l
      in
         case b of
            SOME c =>
               ((if PolyML.pointerEq (d, c) then l' else ((a, d) :: l')), b)
          | NONE => (((a, d) :: l'), b)
      end : 'a map

   fun updateList (m, l) = List.foldl (fn ((i, v), m) => update (m, i, v)) m l

   fun fromList l = updateList (undefined, l)
   fun mk (l, d) = updateList (all d, l)

   fun find (l, a) = List.find (fn (c, _) => eq (a, c)) l

   fun lookup ((l, b) : 'a map, a) =
      case find (l, a) of
         SOME (_, d) => d
       | NONE => (case b of SOME v => v | NONE => raise Undefined)

   fun peek ((l, b) : 'a map, a) =
      case find (l, a) of
         SOME (_, d) => SOME d
       | NONE => b

   fun diff eqd (m1 as (cs1, b1) : 'a map, m2 as (cs2, b2) : 'a map) =
      let
         fun eqo (SOME a, SOME b) = eqd (a, b)
           | eqo (NONE, NONE) = true
           | eqo _ = false
         fun partition1 (acc as (cng, ncng)) =
            fn [] => acc
             | (h as (a, b)) :: t =>
                 partition1
                    (case peek (m2, a) of
                        SOME v => if eqd (b, v)
                                     then (cng, a :: ncng)
                                  else (h :: cng, ncng)
                      | NONE => (h :: cng, ncng)) t
         fun partition2 (acc as (cng, ncng)) =
            fn [] => acc
             | (h as (a, b)) :: t =>
                 partition2
                   (if Option.isSome (find (cs1, a))
                       then acc
                    else if eqo (SOME b, b1)
                       then (cng, a :: ncng)
                    else ((a, b1)::cng, ncng)) t
         val (changed1, not_changed1) = partition1 ([], []) cs1
         val (changed2, not_changed2) = partition2 ([], []) cs2
         val changed = List.map (I ## SOME) changed1 @ changed2
      in
        (changed,
         if eqo (b1, b2)
            then NONE
         else SOME (not_changed1 @ not_changed2, b1))
      end

   fun printDiff (eqd, compare) =
      fn (title, pad: string -> string, aToS, dToS, lToS) =>
      fn maps =>
         case diff eqd maps of
            ([], NONE) => false
          | (cng, rst) =>
            let
               val d = fn SOME s => dToS s | NONE => "-"
               fun print1 (a, b) =
                  TextIO.print (pad (aToS a) ^ ": " ^ d b ^ "\n")
               val scng = Lib.msort (compare o (fst ## fst)) cng
            in
               (if title <> "" then TextIO.print (title ^ "\n") else ())
               ; List.app print1 scng
               ; case rst of
                    SOME (e, b) =>
                      TextIO.print
                        ((if List.null e
                             then if List.null scng then "all: " else "rest: "
                          else let
                                  val l = "{" ^ Lib.commify lToS e ^ "}: "
                               in
                                  if List.null scng
                                     then "index not in " ^ l
                                  else "index not above or in " ^ l
                               end) ^ d b ^ "\n")
                  | NONE => ()
               ; true
            end

end (* structure Map *)

(* -------------------------------------------------------------------------
   Parsing combinators
   ------------------------------------------------------------------------- *)

datatype loc = LastLine | Loc of int * int

signature Parse =
  sig
    type state
    eqtype token
    eqtype tok

    type parseerror = {loc: loc, message: string, tokens: token list}
    type parseinput = state * token list

    exception NoParse of parseerror

    val ++ :
       (parseinput -> 'a * parseinput) * (parseinput -> 'b * parseinput) ->
       parseinput -> ('a * 'b) * parseinput
    val >- :
       (state -> 'a) * ('a * token list -> 'b * parseinput) ->
       parseinput -> 'b * parseinput
    val >-- :
       (parseinput -> 'a * parseinput) * (state -> 'b) ->
       parseinput -> 'a * ('b * token list)
    val >> :
       (parseinput -> 'a * parseinput) * ('a -> 'b) ->
       parseinput -> 'b * parseinput
    val HighestError : parseerror -> exn
    val accept : 'a -> parseinput -> 'a * parseinput
    val clearHighestError : unit -> unit
    val fail : string -> parseinput -> 'a * parseinput
    val finished : parseinput -> unit * parseinput
    val getHighestError : unit -> parseerror option
    val many :
       (parseinput -> 'a * parseinput) -> parseinput -> 'a list * parseinput
    val opick :
       (tok -> (state * token list -> 'a * (state * token list)) option) ->
       parseinput -> 'a option * parseinput
    val option :
       (parseinput -> 'a * parseinput) -> parseinput -> 'a option * parseinput
    val osome : (tok -> bool) -> parseinput -> token option * parseinput
    val otoken : tok -> parseinput -> token option * parseinput
    val parseError : parseinput -> string -> 'a
    val pick :
       (token -> parseinput -> 'a * parseinput) -> parseinput -> 'a * parseinput
    val puresequence :
       (parseinput -> 'a * parseinput) ->
       (parseinput -> 'b * parseinput) -> parseinput -> 'a list * parseinput
    val repeat :
       (parseinput -> 'a * parseinput) -> parseinput -> 'a list * parseinput
    val sequence :
       (parseinput -> 'a * parseinput) ->
       (parseinput -> 'b * parseinput) ->
       (parseinput -> 'a * parseinput) option ->
       parseinput -> 'a list * parseinput
    val setHighestError : parseerror -> unit
    val some : (tok -> bool) -> parseinput -> token * parseinput
    val token : tok -> parseinput -> token * parseinput
    val || : (parseinput -> 'a) * (parseinput -> 'a) -> parseinput -> 'a
  end

functor Parse (type state
               eqtype token
               eqtype tok
               val numTokens: int
               val getLoc: state * token -> loc
               val getTok: token -> tok
               val nextState: state * token -> state) =
struct
   type state = state
   type token = token
   type tok = tok

   type parseinput = state * token list
   type parseerror = {loc: loc, message: string, tokens: token list}

   exception NoParse of parseerror

   local
      val highest_error = ref (NONE : parseerror option)
   in
      fun getHighestError () = !highest_error
      fun setHighestError e = highest_error := SOME e
      fun clearHighestError () = highest_error := NONE
      fun HighestError e =
         NoParse (Option.getOpt (!highest_error, e)) before
         (clearHighestError ())
   end

   val compareLoc =
      fn (LastLine, _) => General.GREATER
       | (_, LastLine) => General.LESS
       | (Loc (_, t1), Loc (_, t2)) => Int.compare (t1, t2)

   local
      fun takeTokens l = List.take (l, Int.min (numTokens, List.length l))
   in
      fun parseError ((s, l): parseinput) m =
         let
            val loc = if List.null l then LastLine else getLoc (s, hd l)
            val error = { loc = loc, message = m, tokens = takeTokens l }
         in
            case getHighestError () of
              NONE => (setHighestError error; raise NoParse error)
            | SOME { loc = hloc, ... } =>
                (if compareLoc (loc, hloc) = GREATER
                    orelse not (String.isPrefix "Syntax error" m)
                    then setHighestError error
                 else ()
                 ; raise NoParse error)
         end
   end

   fun accept v (input: parseinput) = (v, input)

   fun fail m input = parseError input m : 'a * parseinput

   fun op ++ (parser1, parser2) (input: parseinput) =
      let
         val (result1, rest1: parseinput) = parser1 input
         val (result2, rest2: parseinput) = parser2 rest1
      in
         ((result1, result2), rest2)
      end

   fun many parser (input: parseinput) =
      let
         val (result, next: parseinput) = parser input
         val (results, rest: parseinput) = many parser next
      in
         (result :: results, rest)
      end
      handle NoParse _ => ([], input)

   fun option parser (input: parseinput) =
      let
         val (result, rest: parseinput) = parser input
      in
         (SOME result, rest)
      end
      handle NoParse _ => (NONE, input)

   fun sequence parser1 parser2 oparser3 =
      let
         val a = ref []
         fun iter (input : parseinput) =
            let
               val ((result1, next1: parseinput), err) =
                      ((SOME ## I) (parser1 input), NONE)
                      handle NoParse e => ((NONE, input), SOME e)
            in
               case result1 of
                 SOME r1 =>
                   (let
                       val () = a := r1 :: !a
                       val next2 = snd (parser2 next1) : parseinput
                    in
                       iter next2
                    end
                    handle NoParse _ => (List.rev (!a), next1))
               | NONE =>
                    case oparser3 of
                       NONE => raise NoParse (Option.valOf err)
                     | SOME parser3 =>
                         let
                            val (result2, next2: parseinput) = parser3 next1
                         in
                            (List.rev (result2::(!a)), next2)
                         end
            end
      in
         iter
      end

   fun puresequence parser1 parser2 input = sequence parser1 parser2 NONE input

   fun op >> (parser, f) (input: parseinput) =
      let
         val (result, rest: parseinput) = parser input
      in
         (f result, rest)
      end

   fun op >- (f, parser) ((s, input): parseinput) =
      parser (f s, input): 'b * parseinput

   fun op >-- (parser, f) (input: parseinput) =
      let
         val (result, (s, rest): parseinput) = parser input
      in
         (result, (f s, rest))
      end

   fun op || (parser1, parser2) (input: parseinput) =
      parser1 input
      handle NoParse (e1 as {loc = loc1, ...}) =>
        parser2 input
        handle NoParse (e2 as {loc = loc2, ...}) =>
          raise NoParse (if compareLoc (loc1, loc2) = GREATER then e1 else e2)

   fun repeat parser = (parser ++ many parser) >> (op ::)

   val finished =
      fn (input as (_, [])): parseinput => ((), input: parseinput)
       | input => parseError input "Expecting EOF"

   fun some p =
      fn input as (_, []): parseinput => parseError input "Unexpected EOF"
       | input as (s, h::t) =>
          if p (getTok h)
             then (h, (nextState (s, h), t)): token * parseinput
          else parseError input "Syntax error."

   fun osome p =
      fn input as (_, []): parseinput => (NONE, input)
       | input as (s, h::t) =>
          if p (getTok h)
             then (SOME h, (nextState (s, h), t))
          else (NONE, input) : token option * parseinput

   fun token tok input = some (fn t => t = tok) input
   fun otoken tok input = osome (fn t => t = tok) input

   fun pick f =
      fn input as (_, []): parseinput => parseError input "Unexpected EOF"
       | input as (s, h::t) =>
          f h ((nextState (s, h), t) : parseinput) : 'a * parseinput

   fun opick f =
      fn input as (_, []): parseinput => (NONE, input)
       | input as (s, h::t) =>
          case f (getTok h) of
            SOME p => (SOME ## I) (p ((nextState (s, h), t)))
          | NONE => (NONE, input)

end
