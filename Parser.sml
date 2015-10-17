(* -------------------------------------------------------------------------
   ISA specification parser
   ------------------------------------------------------------------------- *)

PolyML.use "Eval.sml";
PolyML.use "lexer.lex.sml";

signature Parser =
sig
   type tok
   type token
   type parseinput
   type parsestate
   type statement
   type expression

   exception Error of {loc: int, message: string, value: string option}

   structure ParseToken: Parse where type state = parsestate

   val addRecord : string * (string * Type.ty) list -> unit
   val addVar : string * Type.ty -> unit
   val buildDatatype : string * (string * Type.ty option) list -> unit
   val buildExpression :
      Term.hint -> Env.env -> expression -> Type.typesubst list * Term.term
   val buildStatement :
      Term.hint -> Env.env -> statement -> Type.typesubst list * Term.term
   val definition : parseinput -> statement * parseinput
   val expression : parseinput -> expression * (parsestate * token list)
   val lex : string -> token list
   val lexF : string -> token list
   val lexQ : string frag list -> token list
   val load : string -> unit
   val loadF : string -> unit
   val loadQ : string frag list -> unit
   val printErrors : bool option -> bool
   val raiseErrors : bool option -> bool
   val reset : unit -> unit
   val save : unit -> unit
   val show :
      unit -> (string * Env.var) list * (string * Type.ty) list *
              (string * Types.typeconst) list * (string * Consts.const) list
   val spec :
      string -> (string * Env.var) list * (string * Type.ty) list *
                (string * Types.typeconst) list * (string * Consts.const) list
   val specF :
      string -> (string * Env.var) list * (string * Type.ty) list *
                (string * Types.typeconst) list * (string * Consts.const) list
   val specQ :
      string frag list ->
      (string * Env.var) list * (string * Type.ty) list *
      (string * Types.typeconst) list * (string * Consts.const) list
   val specification : Env.env -> parseinput -> unit * parseinput
   val statement : parseinput -> statement * parseinput
   val statementQ : string frag list -> Term.term
   val tryParse : (parseinput -> 'a) -> string -> 'a
   val tryParseQ : (parseinput -> 'a) -> string frag list -> 'a
   val undo : unit -> unit
   val verbose : bool -> unit

end (* sig Parser *)

structure Parser :> Parser =
struct

(* -------------------------------------------------------------------------
   Lexer
   ------------------------------------------------------------------------- *)

local
   fun lexer f s =
      let
         val strm = f s
         val lex = Lex.makeLexer (fn _ => TextIO.inputAll strm)
         fun iter a = case lex () of (~1, _) => List.rev a | t => iter (t :: a)
         val l = iter [] before TextIO.closeIn strm
      in
         if 0 < !Lex.UserDeclarations.comment_depth
            then raise Fail ("lex: unmatched comment bracket from line: " ^
                             Int.toString (!Lex.UserDeclarations.comment_line))
         else l
      end
in
   val lex = lexer TextIO.openString
   val lexF = lexer TextIO.openIn
   val lexQ = lex o quoteToString
end

(* -------------------------------------------------------------------------
   Token Parser
   ------------------------------------------------------------------------- *)

exception Error of {loc: int, message: string, value: string option}

type parsestate = int * int option (* (token_number, current_precedence) *)

structure ParseToken =
   Parse (type state = parsestate
          type token = Lex.UserDeclarations.lexresult
          type tok = Lex.UserDeclarations.tok
          val numTokens = 5
          fun nextState ((t, p), _) = (t + 1, p)
          val getTok = snd
          val getLoc = fn (_, (~1, _)) => LastLine
                        | ((t, _), (n, _)) => Loc (n, t))
  : Parse where type state = parsestate
                type token = Lex.UserDeclarations.lexresult
                type tok = Lex.UserDeclarations.tok

open Lex.UserDeclarations
open ParseToken

fun tryParse parser l = parser (((0, NONE), lex l): parseinput)
fun tryParseQ parser l = parser (((0, NONE), lexQ l): parseinput)

val tokname =
   fn Name s => s
    | EName s => s
    | Num s => s
    | String s => s
    | Reserved s => s
    | Symbol s => s
    | Other s => s

fun tokenname (loc, t) = (loc, tokname t)

val somechar =
   some (fn String s => String.size s = 2 andalso String.sub (s, 0) = #"#"
          | _ => false) >> tokenname

val somestring =
   some (fn String s => 1 < String.size s andalso String.sub (s, 0) = #"\""
          | _ => false) >> ((I ## Tag.remove) o tokenname)

val somename = some (fn Name _ => true | _ => false) >> tokenname
val somenum = some (fn Num _ => true | _ => false) >> tokenname

val varorconst =
   some (fn Name "unit" => false
          | Name "bool" => false
          | Name "int" => false
          | Name "nat" => false
          | Name "string" => false
          | Name "bits" => false
          | Name _ => true
          | _ => false) >> tokenname

local
   val num = Int.fromLit o Tag.remove
   fun nat "" = NONE
     | nat s = case String.sub (s, 0) of
                  #"n" => num s
                | #"?" => num s
                | _ => NONE
in
   fun number input =
      ( somenum
          >> (fn (loc, s) =>
                 case nat s of
                    SOME n => (loc, n)
                  | NONE => raise Error {loc = loc, message = "Bad number.",
                                         value = SOME s})
      ) input
end

(* -------------------------------------------------------------------------
   Type parser
   ------------------------------------------------------------------------- *)

local
   fun consttype input =
      ( token (Name "bits") ++
        token (Symbol "(") ++ bitstype ++ token (Symbol ")")
          >> (snd o fst)
     || somename
          >> (fn (loc, n) =>
                 if Types.isConst n andalso n <> "bits"
                    then Type.mkConstType n
                 else parseError input ("Bad type: " ^ n))
     || token (Symbol "(") ++ typeexpr ++ token (Symbol ")")
          >> (snd o fst)
      ) input
   and prodexpr input =
      ( consttype ++ param ++ opick (fn Symbol "*" => SOME prodexpr | _ => NONE)
          >> (fn ((cty, SOME f), SOME e) => f cty ** e
               | ((cty, NONE), SOME e) => cty ** e
               | ((cty, SOME f), NONE) => f cty
               | ((cty, NONE), NONE) => cty)
      ) input
   and typeexpr input =
      ( prodexpr ++ opick (fn Symbol "->" => SOME prodexpr | _ => NONE)
          >> (fn (cty, SOME e) => cty ---> e
               | (cty, NONE) => cty)
      ) input
   and bitstype input =
      ( varorconst
          >> (Type.constrainTy o snd)
     || number
          >> (fn (loc, n) =>
                if n <> 0
                   then Type.fixedTy n
                else raise Error {loc = loc, value = NONE,
                                  message = "0-bit values not allowed."})
      ) input
   and param input =
      opick (fn Reserved "list" => SOME (accept Type.listTy)
              | Name "option" => SOME (accept Type.optionTy)
              | Reserved "set" => SOME (accept Types.setType)
              | _ => NONE) input
in
   val bitstype = bitstype
   val typeexpr = typeexpr
   fun annotation input =
      pick (fn (_, Symbol "::") => typeexpr
             | (_, Symbol "`")  => bitstype
             | _ => parseError input "Syntax error.") input
   fun oannotation input =
      opick (fn Symbol "::" => SOME typeexpr
              | Symbol "`" => SOME bitstype
              | _ => NONE) input
end

(* -------------------------------------------------------------------------
   Statement and Expression parsers
   ------------------------------------------------------------------------- *)

datatype exp =
     BinOp of string * expression * expression
   | Cond of expression * expression * expression
   | Constrained of expression * Type.ty
   | Literal of string
   | MatchCases of expression * expression list
   | UnaryOp of string * expression
   | Apply of expression * expression
   | Variable of string
and stmt =
    AssignDecl of expression * expression
  | Conditional of expression * statement * statement
  | Expression of exp
  | For of expression * expression * expression * statement
  | Foreach of expression * expression * statement
  | MatchStatement of expression * (expression * statement) list
  | Sequence of statement list
  | When of expression * statement
withtype expression = { loc: int, exp: exp }
     and statement = {loc: int, stmt: stmt}

fun buildBinOps (l, []) = l
  | buildBinOps (l, r) =
      List.foldl
        (fn (((loc, binop), expr), e) =>
           {loc = loc, exp = BinOp (binop, e, expr)}) l r

fun fold_rev f l =
   let
      val (h, t) = case List.rev l of
                      [] => raise Fail "fold_rev"
                    | h :: t => (h, t)
   in
      List.foldl f h t
   end

fun buildBinOp f =
   fold_rev (fn (x, tm) => {loc = #loc x, exp = BinOp (f, x, tm)})

fun buildPairOp (loc, f) =
   fold_rev
      (fn (x, tm) =>
         {loc = loc, exp = UnaryOp (f, {loc = loc, exp = BinOp (",", x, tm)})})

val tupleToList =
   let
      fun iter a =
         fn {exp = BinOp (",", e1, e2), ...} => iter (e1 :: a) e2
          | t => List.rev (t :: a)
   in
      iter []
   end

val annotatePair =
   fn t as {loc, exp = BinOp (",", _, _)} =>
       {loc = loc,
        exp = Constrained (t, Type.freshTyVar () ** Type.freshTyVar ())}
    | t => t

val constrain =
  fn ({loc = loc, exp = Constrained (c, _)}, SOME t) =>
      {loc = loc, exp = Constrained (c, t)}: expression
   | (c, SOME t) => {loc = #loc c, exp = Constrained (c, t)}
   | (c, _) => c

fun binaryword ignore =
   some
     (fn Num s =>
         let
            val (l, r) = Substring.splitAt (Substring.full s, 2)
         in
            Substring.string l = "??" andalso not (Substring.isEmpty r) andalso
            Substring.isEmpty
              (Substring.dropl (fn #"1" => true | #"0" => true | _ => false) r)
         end
       | _ => false)
     >> (fn (loc, s) =>
            let
               val n = String.extract (tokname s, 2, NONE)
               val e = if ignore then Variable "_" else Literal ("wb" ^ n)
            in
               constrain
                  ({loc = loc, exp = e}, SOME (Type.fixedTy (String.size n)))
            end)

datatype precedence =
     LeftAssoc of int
   | RightAssoc of int
   | BadOp

fun setPrec p (n, _) = (n, SOME p)
fun wipePrec (n, _) = (n, NONE)
fun getPrec (_, p) = Option.getOpt (p, 0)

local
   val splitable =
      fn #"-" => true
       | #"~" => true
       | _    => false
   fun trysplit n s =
      let
         val c = String.sub (s, 0)
      in
         if splitable c andalso 1 < String.size s
            then let
                    fun sym r = (n, Lex.UserDeclarations.Symbol r)
                 in
                    SOME (sym (String.str c), sym (Tag.remove s))
                 end
         else NONE
      end
      handle Subscript => NONE
in
   fun unary _ (input as (_, [])) = parseError input "Unexpected EOF"
     | unary umap (input as (st, token :: rest)) =
        let
           val (loc, name) = tokenname token
        in
           case umap name of
             SOME n =>
                ((loc, name), (setPrec n st, rest)): (int * string) * parseinput
           | _ =>
                (case trysplit (fst token) name of
                   SOME (c, r) => unary umap (st, c :: r :: rest)
                 | NONE =>
                     parseError input
                       ("Syntax error: expecting unary op, got " ^ name))
        end
end

fun binary _ (input as (_, [])) = parseError input "Unexpected EOF"
  | binary bmap (input as (st, token :: rest)) =
     let
        val lname as (_, name) = tokenname token
        fun err () = parseError input
                       ("Syntax error: expecting binary op, got " ^ name)
        val n = getPrec st
     in
        case bmap name of
          LeftAssoc m =>
             if m >= n then
               (lname, (setPrec (1 + m) st, rest)): (int * string) * parseinput
             else err ()
        | RightAssoc m =>
             if m >= n then
               (lname, (setPrec m st, rest)): (int * string) * parseinput
             else err ()
        | _ => err ()
     end

(* -------------------------------------------------------------------------
   Bit pattern parser ' ...  '
   ------------------------------------------------------------------------- *)

local
   fun BitPatternLiteral (loc, s) =
      let
         val c = String.sub (s, 0)
         val b = String.sub (s, 1)
         val _ = c = #"?" orelse c = #"w" orelse
                 raise Error {loc = loc, value = SOME s,
                              message = "Bad literal in bit pattern."}
         val b = String.str (if String.sub (s, 1) = #"?" then #"b" else b)
         val t = String.extract (s, 2, NONE)
      in
         constrain
           ({loc = loc, exp = Literal ("w" ^ b ^ t)},
            case b of
               "b" => SOME (Type.fixedTy (String.size t))
             | "x" => SOME (Type.fixedTy (String.size t * 4))
             | _ => NONE)
      end
   fun bitpat input =
      ( token (Symbol "'") ++ pat ++ token (Symbol "'")
          >> (snd o fst)
      ) input
   and pat input =
      ( puresequence constrained (otoken (Symbol ":"))
          >> (buildBinOp ":")
      ) input
   and constrained input =
      ( clause ++ opick (fn Symbol "`" => SOME bitstype | _ => NONE)
          >> constrain
     || token (Symbol "(") ++ binaryword true ++ token (Symbol ")")
          >> (snd o fst)
      ) input
   and clause input =
      ( pick (fn (loc, Num s) => accept (BitPatternLiteral (loc, s))
               | (loc, Name s) => accept {loc = loc, exp = Variable s}
               | (loc, Symbol "_") => accept {loc = loc, exp = Variable "_"}
               | (loc, Reserved "true") =>
                    accept {loc = loc, exp = Literal "true"}
               | (loc, Reserved "false") =>
                    accept {loc = loc, exp = Literal "false"}
               | (loc, Reserved "UNKNOWN") =>
                    accept {loc = loc, exp = Literal "UNKNOWN"}
               | _ => parseError input "Syntax error.")
      ) input
in
   val bitpat = bitpat
end

(* -------------------------------------------------------------------------
   Pattern parser
   ------------------------------------------------------------------------- *)

local
   fun okayLHS e =
      case e of
         {exp = BinOp (",", e1, e2), ...} => okayLHS e1 andalso okayLHS e2
       | {exp = BinOp (":", e1, e2), ...} => okayLHS e1 andalso okayLHS e2
       | {exp = Constrained (e, _), ...} => okayLHS e
       | {exp = Variable _, ...} => true
       | _ => false

   val binaryop = binary
     (fn "," => RightAssoc 9   (* pair *)
       | "@" => RightAssoc 55  (* list cons *)
       | _ => BadOp)

   fun pat (input as (st, _)) =
      ( constrained ++ many ((setPrec (getPrec st) >- binaryop) ++ pat)
          >> buildBinOps
      ) input
   and constrained input =
      ( clause ++ oannotation
          >> constrain
      ) input
   and bpat input =
      ( token (Symbol ")")
          >> (fn (loc, _) => {loc = loc, exp = Literal "()"})
     || (setPrec 0 >- pat) ++ token (Symbol ")")
          >> (annotatePair o fst)
      ) input
   and clause input =
      ( varorconst ++ opick (fn Symbol "(" => SOME bpat | _ => NONE)
          >> (fn ((loc, v), SOME p) => {loc = loc, exp = UnaryOp (v, p)}
               | ((loc, v), NONE) => {loc = loc, exp = Variable v})
     || somestring ++ token (Symbol ":") ++ clause
          >> (fn (((loc, s), _), p) =>
                let
                   val l = String.explode s
                   val l =
                     List.map
                       (fn c =>
                         {loc = loc, exp = Literal ("#" ^ String.str c)}) l
                in
                   buildBinOp "@" (l @ [p])
                end)
     || someliteral
     || bitpat
     || token (Reserved "list") ++ token (Symbol "{") ++ list
          >> snd
     || token (Symbol "-") ++ somenum
          >> (fn ((loc1, _), (loc2, n)) =>
                {loc = loc1,
                 exp = UnaryOp ("-", {loc = loc2, exp = Literal n})})
     || token (Symbol "_")
           >> (fn (loc, _) => {loc = loc, exp = Variable "_"})
     || token (Symbol "(") ++ bpat
           >> snd
      ) input
   and someliteral input =
      pick (fn (loc, String s) => accept {loc = loc, exp = Literal s}
             | (loc, Num s) => accept {loc = loc, exp = Literal s}
             | (loc, Reserved "true") =>
                  accept {loc = loc, exp = Literal "true"}
             | (loc, Reserved "false") =>
                  accept {loc = loc, exp = Literal "false"}
             | (loc, Reserved "UNKNOWN") =>
                  accept {loc = loc, exp = Literal "UNKNOWN"}
             | _ => parseError input "Syntax error.") input
   and list input =
      ( token (Symbol "}")
          >> (fn (loc, _) => {loc = loc, exp = Variable "Nil"})
     || (setPrec 0 >- pat) ++ token (Symbol "}")
          >> (fn (e as {loc = loc1, ...}, (loc2, _)) =>
               buildPairOp (loc1, "Cons")
                  (snoc {loc = loc2, exp = Variable "Nil"} (tupleToList e)))
      ) input
in
   val pat =
      setPrec 0 >- pat >-- wipePrec: parseinput -> expression * parseinput
   fun lhs input =
      ( pat
        >> (fn e => if okayLHS e then e else parseError input "bad assignment")
      ) input
end

(* -------------------------------------------------------------------------
   Character predicate
   ------------------------------------------------------------------------- *)

local
   fun cvar loc = {loc = loc, exp = Variable "c"}: expression
   fun charpred loc s = accept {loc = loc, exp = UnaryOp (s, cvar loc)}
   fun mklit (loc, s) = {loc = loc, exp = Literal s}
   val binaryop = binary
     (fn "or"     => LeftAssoc 10    (* logical or *)
       | "and"    => LeftAssoc 20    (* logical and *)
       | _        => BadOp)
   fun charclass (input as (st, _)) =
      ( clause ++ many ((setPrec (getPrec st) >- binaryop) ++ charclass)
          >> buildBinOps
      ) input
   and clause input =
      pick
        (fn (loc, Reserved "not") =>
              (setPrec 30 >- charclass)
                 >> (fn c => {loc = loc, exp = UnaryOp ("not", c)})
          | (loc, Reserved "in") =>
              set
              >> (fn {exp = UnaryOp ("{..}", x as {exp = Literal _, ...}),
                      ...} => {loc = loc, exp = BinOp ("==", cvar loc, x)}
                   | s => {loc = loc, exp = BinOp ("in", cvar loc, s)})
          | (loc, Symbol "(") => bclass
          | (loc, Name (s as "alpha")) => charpred loc "IsAlpha"
          | (loc, Name (s as "alphanum")) => charpred loc "IsAlphaNum"
          | (loc, Name (s as "digit")) => charpred loc "IsDigit"
          | (loc, Name (s as "hexdigit")) => charpred loc "IsHexDigit"
          | (loc, Name (s as "lower")) => charpred loc "IsLower"
          | (loc, Name (s as "space")) => charpred loc "IsSpace"
          | (loc, Name (s as "upper")) => charpred loc "IsUpper"
          | _ => parseError input "Syntax error.")
        input
   and bclass input =
      ( (setPrec 0 >- charclass) ++ token (Symbol ")")
          >> fst
      ) input
   and set input =
      ( token (Reserved "set") ++ token (Symbol "{") ++
        puresequence somechar (token (Symbol ",")) ++ token (Symbol "}")
          >> (fn ((((loc, _), _), l), _) =>
                {loc = loc,
                 exp = UnaryOp ("{..}", buildBinOp "," (List.map mklit l))})
      ) input
in
   val charclass =
      setPrec 0 >- charclass >-- wipePrec: parseinput -> expression * parseinput
end

(* -------------------------------------------------------------------------
   Expression parser
   ------------------------------------------------------------------------- *)

local
   fun buildReference ([], _) = raise Fail "buildReference: empty"
     | buildReference (h :: t, i) =
      let
         fun iter a =
            fn [] => (case i of
                        SOME e => {loc = #loc e, exp = BinOp ("<..>", a, e)}
                      | NONE => a)
             | [{loc = loc1,
                 exp = UnaryOp ("&", {loc = loc2, exp = Variable b})}] =>
                  iter {loc = loc1,
                        exp =
                          UnaryOp ("&", {loc = loc2, exp = UnaryOp (b, a)})} []
             | [{loc = loc1,
                 exp = UnaryOp ("&", {loc = loc2, exp = UnaryOp (b, e)})}] =>
                  iter {loc = loc1,
                        exp =
                          UnaryOp
                             ("&", {loc = loc2,
                                    exp = Apply
                                            ({loc = loc2,
                                              exp = UnaryOp (b, a)}, e)})} []
             | {loc = loc, exp = Variable b} :: rst =>
                  iter {loc = loc, exp = UnaryOp (b, a)} rst
             | {loc = loc, exp = UnaryOp (b, e)} :: rst =>
                  iter {loc = loc,
                        exp = Apply ({loc = loc, exp = UnaryOp (b, a)}, e)} rst
             | _ => raise Fail "buildReference"
      in
         iter h t
      end

   val unaryop = unary
     (fn "not"  => SOME 30  (* logical negation *)
       | "!"    => SOME 90  (* logical negation *)
       | "-"    => SOME 90  (* unary negation *)
       | "~"    => SOME 90  (* bitwise complement *)
       | "FP64" => SOME 90  (* parse Real string to 64-bit word *)
       | _      => NONE)

   val binaryop = binary
     (fn ","      => RightAssoc 9    (* pair *)
       | "or"     => LeftAssoc 10    (* logical or *)
       | "and"    => LeftAssoc 20    (* logical and *)
       | "=="     => RightAssoc 30   (* equality *)
       | "!="     => RightAssoc 30   (* inequality *)
       | "<>"     => RightAssoc 30   (* inequality *)
       | "<"      => RightAssoc 40   (* signed less-than *)
       | "<+"     => RightAssoc 40   (* unsigned less-than *)
       | "<="     => RightAssoc 40   (* signed less-or-equal *)
       | "<=+"    => RightAssoc 40   (* unsigned less-or-equal *)
       | ">"      => RightAssoc 40   (* signed greater-than *)
       | ">+"     => RightAssoc 40   (* unsigned greater-than *)
       | ">="     => RightAssoc 40   (* signed greater-or-equal *)
       | ">=+"    => RightAssoc 40   (* unsigned greater-or-equal *)
       | "in"     => LeftAssoc 40    (* set membership *)
       | "notin"  => LeftAssoc 40    (* set non-membership *)
       | "insert" => RightAssoc 45   (* set insertion *)
       | ":"      => RightAssoc 50   (* concatenation *)
       | "@"      => RightAssoc 55   (* list cons *)
       | "-"      => LeftAssoc 60    (* subtraction *)
       | "+"      => LeftAssoc 60    (* addition *)
       | "||"     => LeftAssoc 60    (* bitwise or *)
       | "??"     => LeftAssoc 60    (* bitwise xor *)
       | "*"      => LeftAssoc 70    (* multiplication *)
       | "quot"   => LeftAssoc 70    (* signed division *)
       | "rem"    => LeftAssoc 70    (* signed remainder *)
       | "div"    => LeftAssoc 70    (* unsigned division *)
       | "mod"    => LeftAssoc 70    (* unsigned mod *)
       | "&&"     => LeftAssoc 70    (* bitwise and *)
       | "<<"     => LeftAssoc 80    (* left shift *)
       | ">>"     => LeftAssoc 80    (* signed right shift *)
       | ">>+"    => LeftAssoc 80    (* unsigned right shift *)
       | "#>>"    => LeftAssoc 80    (* rotate right *)
       | "#<<"    => LeftAssoc 80    (* rotate left *)
       | "^"      => RightAssoc 100  (* replicate *)
       | "**"     => RightAssoc 100  (* exponential *)
       | _        => BadOp)

   fun expr (input as (st, _)) =
      ( constrained ++ many ((setPrec (getPrec st) >- binaryop) ++ expr)
          >> buildBinOps
      ) input
   and constrained input =
      ( clause ++ oannotation
          >> constrain
      ) input
   and clause input =
      ( unaryop ++ expr
          >> (fn ((loc, s), e) => {loc = loc, exp = UnaryOp (s, e)})
     || reference
     || litexpr ++ option index
          >> (fn (x, SOME e) => {loc = #loc x, exp = BinOp ("<..>", x, e)}
               | (x, NONE) => x)
     || pick
         (fn (loc, EName e) =>
               option litexpr
                  >> (fn a =>
                        {loc = loc,
                         exp = case a of SOME b => UnaryOp (e, b)
                                       | _ => Variable e})
           | (loc, Reserved "if") =>
               (setPrec 0 >- expr) ++ token (Reserved "then") ++
               (setPrec 0 >- expr) ++ token (Reserved "else") ++
               (setPrec 0 >- expr)
                  >> (fn ((((b, _), t), _), e) =>
                        {loc = loc, exp = Cond (b, t, e)})
           | (loc, Reserved "match") =>
               (setPrec 0 >- expr) ++ token (Symbol "{") ++ repeat cases ++
               token (Symbol "}")
                  >> (fn (((e, _), cs), _) =>
                        {loc = loc, exp = MatchCases (e, List.concat cs)})
           | (loc, Reserved "list") =>
               token (Symbol "{") ++ list >> snd
           | (loc, Reserved "set") =>
               token (Symbol "{") ++ set >> snd
           | (loc, Reserved "splitl") => charexpr loc "splitl"
           | (loc, Reserved "splitr") => charexpr loc "splitr"
           | (loc, Reserved "fields") => charexpr loc "fields"
           | (loc, Reserved "tokens") => charexpr loc "tokens"
           | _ => parseError input "Syntax error.")
      ) input
   and charexpr loc s input =
      ( charclass ++ token (Symbol "(") ++ (setPrec 0 >- expr) ++
        token (Symbol ")")
          >> (fn (((c, _), e), _) => {loc = loc, exp = BinOp (s, c, e)})
      ) input
   and bexpr input =
      ( token (Symbol ")")
          >> (fn (loc, _) => {loc = loc, exp = Literal "()"})
     || (setPrec 0 >- expr) ++ token (Symbol ")")
          >> (annotatePair o fst)
      ) input
   and litexpr input =
      ( pick (fn (loc, Symbol "(") =>
                   bexpr
               | (loc, Symbol "[") =>
                   (setPrec 0 >- expr) ++ token (Symbol "]")
                      >> (fn (x, _) => {loc = loc, exp = UnaryOp ("[..]", x)})
               | (_, Symbol "'") =>
                   binaryword false ++ token (Symbol "'")
                      >> fst
               | (loc, String s) =>
                   accept {loc = loc, exp = Literal s}
               | (loc, Num s) =>
                   accept {loc = loc, exp = Literal s}
               | (loc, Reserved "true") =>
                   accept {loc = loc, exp = Literal "true"}
               | (loc, Reserved "false") =>
                   accept {loc = loc, exp = Literal "false"}
               | (loc, Reserved "UNKNOWN") =>
                   ( token (Symbol "(") ++ bexpr
                       >> (fn (_, e) =>
                             {loc = loc, exp = UnaryOp ("UNKNOWN", e)})
                  || accept {loc = loc, exp = Literal "UNKNOWN"})
               | _ => parseError input "Syntax error.")
      ) input
   and list input =
      ( token (Symbol "}")
          >> (fn (loc, _) => {loc = loc, exp = Variable "Nil"})
     || (setPrec 0 >- expr) ++ token (Symbol "}")
          >> (fn (e as {loc = loc1, ...}, (loc2, _)) =>
              buildPairOp (loc1, "Cons")
                 (snoc {loc = loc2, exp = Variable "Nil"} (tupleToList e)))
      ) input
   and set input =
      ( token (Symbol "}")
          >> (fn (loc, _) => {loc = loc, exp = Literal "{}"})
     || (setPrec 0 >- expr) ++ token (Symbol "}")
          >> (fn (x, (loc, _)) => {loc = loc, exp = UnaryOp ("{..}", x)})
      ) input
   and reference input =
     ( sequence unit (token (Symbol "."))
         (SOME (token (Symbol "&") ++ unit
                >> (fn ((loc, _), e) =>
                      {loc = loc, exp = UnaryOp ("&", e)}))) ++ option index
         >> buildReference
     ) input
   and unit input =
     ( varorconst ++ opick (fn Symbol "(" => SOME bexpr | _ => NONE)
         >> (fn ((loc, v), SOME e) => {loc = loc, exp = UnaryOp (v, e)}
              | ((loc, v), NONE) => {loc = loc, exp = Variable v})
     ) input
   and index input =
      ( token (Symbol "<") ++ (setPrec 50 >- expr) ++ token (Symbol ">")
          >> (snd o fst)
      ) input
   and cases input =
      ( token (Reserved "case") ++ patterns ++ token (Symbol "=>") ++
        (setPrec 0 >- expr)
          >> (fn ((((loc, _), ps), _), e) =>
                 List.map (fn p => {loc = loc, exp = BinOp ("case", p, e)}) ps)
      ) input
   and patterns input =
      ( pat ++ many (token (Reserved "or") ++ pat)
          >> (fn (p, l) => p :: (List.map snd l))
      ) input

in
   val reference = reference >-- wipePrec: parseinput -> expression * parseinput
   val litexpr = litexpr >-- wipePrec: parseinput -> expression * parseinput
   val expression =
      setPrec 0 >- expr >-- wipePrec: parseinput -> expression * parseinput
end

(* -------------------------------------------------------------------------
   Statement parser

   definition ::= statement {; expr}
                | expr

   statement ::= "{" statement "}"
               | "if" expr "then" statement "else" statement
               | "when" expr "do" statement
               | declare
               | statement ";" statement  (seq)
               | "match" expr "{" {"case" pat {or pat} "=>" statement}+ "}"
               | "for" v "in" expr .. expr "do" statement
               | nothing
               | exception

   declare ::= "var" v "=" expr  (extend state -- reduce at end of scope)
             | expr "<-" expr
             | lhs "=" expr      (let)

   ------------------------------------------------------------------------- *)

local
   fun processReturn allow s =
      case s of
        {loc = loc, stmt = Expression (UnaryOp ("return", e))} =>
          if allow
             then {loc = loc, stmt = Expression (#exp e)}
          else raise Fail "processReturn"
      | {loc = loc, stmt = Conditional (b, s1, s2)} =>
          {loc = loc,
           stmt = Conditional
                    (b, processReturn allow s1, processReturn allow s2)}
      | {loc = loc, stmt = MatchStatement (e, l)} =>
          {loc = loc,
           stmt = MatchStatement (e, List.map (I ## processReturn allow) l)}
      | {loc = loc, stmt = Sequence l} =>
          let
             val (h, t) = lastButlast l
          in
             {loc = loc,
              stmt =
                Sequence
                  (List.map (processReturn false) t @ [processReturn allow h])}
          end
      | _ => s

   fun returnCheck f (input: parseinput) =
      let
         val (s, rest) = f input
         val s' = processReturn true s
                  handle Fail "processReturn" =>
                     parseError rest "Syntax error: unexpected return."
      in
         (s', rest)
      end

   fun definition input =
      ( token (Symbol "{") ++
        sequence clause_or_call (token (Symbol ";")) (SOME return) ++
        token (Symbol "}")
          >> (fn ((_, [x]), _) => x
               | (((loc, _), l), _) => {loc = loc, stmt = Sequence l})
     || clause
     || return
      ) input
   and return input =
      ( otoken (Reserved "return") ++ expression
          >> (fn (SOME _, e) =>
                    {loc = #loc e, stmt = Expression (UnaryOp ("return", e))}
               | (NONE, {loc, exp = e}) =>
                    {loc = loc, stmt = Expression e})
      ) input
   and statement input =
      ( token (Symbol "{") ++
        puresequence clause_or_call (token (Symbol ";")) ++
        token (Symbol "}")
          >> (fn ((_, [x]), _) => x
               | (((loc, _), l), _) => {loc = loc, stmt = Sequence l})
     || clause_or_call
      ) input
   and clause_or_call input = ( clause || call ) input
   and clause input =
      ( declaration
     || pick
          (fn (loc, EName e) =>
              option litexpr
                >> (fn SOME a => {loc = loc, stmt = Expression (UnaryOp (e, a))}
                     | _ => {loc = loc, stmt = Expression (Variable e)})
            | (loc, Reserved "if") =>
              expression ++ token (Reserved "then") ++ definition ++
              token (Reserved "else") ++ definition
                >> (fn ((((e, _), s1), _), s2) =>
                       {loc = loc, stmt = Conditional (e, s1, s2)})
            | (loc, Reserved "when") =>
              expression ++ token (Reserved "do") ++ statement
                >> (fn ((e, _), s) => {loc = loc, stmt = When (e, s)})
            | (loc, Reserved "match") =>
              expression ++ token (Symbol "{") ++ repeat cases ++
              token (Symbol "}")
                >> (fn (((e, _), cs), _) =>
                       {loc = loc, stmt = MatchStatement (e, List.concat cs)})
            | (loc, Reserved "for") =>
              varorconst ++ token (Reserved "in") ++ expression ++
              token (Symbol "..") ++ expression ++ token (Reserved "do") ++
              statement
                >> (fn (((((((loc2, v), _), n1), _), n2), _), s) =>
                      {loc = loc,
                       stmt = For ({loc = loc2, exp = Variable v}, n1, n2, s)})
            | (loc, Reserved "foreach") =>
              varorconst ++ token (Reserved "in") ++ expression ++
              token (Reserved "do") ++ statement
                >> (fn (((((loc2, v), _), l), _), s) =>
                      {loc = loc,
                       stmt = Foreach ({loc = loc2, exp = Variable v}, l, s)})
            | (loc, Reserved "nothing") =>
              accept {loc = loc, stmt = Expression (Literal "()")}
            | (loc, Reserved "var") =>
              ann_varorconst ++
              opick (fn Symbol "=" => SOME expression | _ => NONE)
                >> (fn (((loc2, v), t), e) =>
                      let
                         val e =
                            constrain
                              (Option.getOpt
                                  (e, {loc = loc, exp = Literal "UNKNOWN"}), t)
                      in
                         {loc = loc,
                          stmt =
                            Expression
                               (BinOp
                                  ("var =", {loc = loc2, exp = Variable v}, e))}
                      end)
            | _ => parseError input "Syntax error.")
      ) input
   and ann_varorconst input =
      ( varorconst ++ oannotation
     || token (Symbol "(") ++ varorconst ++ oannotation ++
        token (Symbol ")") >> (fn (((_, v), a), _) => (v, a))
      ) input
   and call input =
      ( somename ++ option litexpr
          >> (fn ((loc, v), SOME a) =>
                     {loc = loc, stmt = Expression (UnaryOp (v, a))}
               | ((loc, v), NONE) =>
                     {loc = loc, stmt = Expression (Variable v)})
      ) input
   and cases input =
      ( token (Reserved "case") ++ patterns ++ token (Symbol "=>") ++ definition
          >> (fn (((_, ps), _), e) => mapl e ps)
      ) input
   and patterns input =
      ( pat ++ many (token (Reserved "or") ++ pat)
          >> (fn (a, l) => a :: List.map snd l)
      ) input
   and declaration input =
      ( lhs ++ token (Symbol "=") ++ expression
          >> (fn ((t, (loc, _)), e) =>
                {loc = loc, stmt = Expression (BinOp ("=", t, e))})
     || reference ++ token (Symbol "<-") ++ expression
          >> (fn ((v, (loc, _)), e) => {loc = loc, stmt = AssignDecl (v, e)})
      ) input

in
   val definition = returnCheck definition
   val statement = returnCheck statement
end

(* -------------------------------------------------------------------------
   Type checking and term building
   ------------------------------------------------------------------------- *)

fun patType (Term.Comb ("case", ty, [p])) =
      let
         val pty = Term.primTypeOf p
         val dty = Types.fstProd (Types.range pty)
                   handle Fail "range" => Types.fstProd pty
      in
         dty --> ty
      end
  | patType t = Term.primTypeOf t

fun badOperation loc v =
   raise Error {loc = loc, message = "Undeclared operation.", value = SOME v}

fun unify_term_to_type loc t ty =
   Types.unify (Term.primTypeOf t) ty
   handle Types.Unify s =>
     raise Term.TypeCheck
             {loc = loc, operation = "", valid_types = [ty], message = s,
              args = [t]}

fun typesubstTerm loc u tm =
   Term.termTypeSubst u tm
   handle Fail m =>
     raise Term.TypeCheck
             {loc = loc, operation = "", valid_types = [],
              message =
                 if m = "termTypeSubst" then "Bad type assignment." else m,
              args = [tm]}

(* ........................................................
   deriveBitSizes is used to infer/check bit-vector widths,
   e.g. for concatenation
   ........................................................ *)

local
   open Term

   infix <=! <!

   fun op <=! (a, b) = b = ~1 orelse a <= b
   fun op <!  (a, b) = b = ~1 orelse a < b

   fun op |=> (a, b) = SOME (Type.|=> (a, Type.FixedBits b))

   val i2s = Int.toString
   val isBoolTy = Types.equalTy Type.boolTy o primTypeOf
   val isBitstringTy = Types.equalTy Type.bitstringTy o primTypeOf

   fun evalNatTerm tm =
      SOME (Term.destNatLit (snd (Eval.eval Stack.empty tm)))
      handle Eval.Except _ => NONE
           | Fail _ => NONE

   datatype infbits = Fix of int | FromTo of string * int * int | NotBV

   fun bitsDest ty =
      case Types.dest ty of
        Type.Other _ => NotBV
      | Type.FixedBits i => Fix i
      | Type.VarBits (v, s) =>
          FromTo (v, PosIntSet.infimum s, PosIntSet.supremum s)

   val bitsDestTm = bitsDest o Term.primTypeOf

   fun bitsString ty =
      case Types.dest ty of
        Type.Other s => "<" ^ s ^ ">"
      | Type.FixedBits i => "`" ^ i2s i
      | Type.VarBits (v, s) => if PosIntSet.isuniv s
                                  then "?"
                               else "`(? in " ^ PosIntSet.toString s ^ ")"

   val bitsStringTm = bitsString o Term.primTypeOf

   fun err m v = raise Error {loc = ~1, message = m, value = SOME v}

   fun concatErr ty a b : Type.typesubst option =
      err "Concatenation has bad type."
          ("(" ^ Term.rawTermToString a ^ " : " ^ Term.rawTermToString b ^
           ") :: " ^ bitsStringTm a ^ " * " ^ bitsStringTm b ^ " -> " ^
           bitsString ty)

   fun repErr n ty a b : Type.typesubst option =
      err ("Repetition (^" ^ i2s n ^ ") has bad type.")
          (bitsStringTm a ^ " * nat -> " ^ bitsString ty)

   fun extendErr s ty a : Type.typesubst option =
      err (s ^ " has bad type.") (bitsStringTm a ^ " -> " ^ bitsString ty)

   fun extractErr h l ty a : Type.typesubst option =
      let
         val oints = fn SOME i => i2s i | _ => "?"
      in
         err "Bad extract."
             (bitsStringTm a ^ "<" ^ oints h ^ ":" ^ oints l ^ "> -> " ^
              bitsString ty)
      end

   fun conditionalSubst f v n l h =
      if l <= n andalso n <=! h then v |=> n else f ()

   fun cSubst ty a b   = conditionalSubst (fn () => concatErr ty a b)
   fun rSubst n ty a b = conditionalSubst (fn () => repErr n ty a b)

   fun extendCheck s ty a =
      let
         fun check x y = if x <=! y then NONE else extendErr s ty a
      in
         case (bitsDestTm a, bitsDest ty) of
           (Fix x, Fix y) => check x y
         | (Fix x, FromTo (_, _, y)) => check x y
         | (FromTo (_, x, _), Fix y) => check x y
         | (FromTo (_, x, _), FromTo (_, _, y)) => check x y
         | _ => NONE
      end

   fun bitCheck s n =
      let
         val m = PosIntSet.supremum s
      in
         if n <! m
            then NONE : Type.typesubst option
         else err "Bit-vector index too large."
                  ("bit " ^ i2s n ^ " of " ^ PosIntSet.toString s ^ "-bit word")
      end

   val bitSizeSubst =
     fn Comb ("[..]", ty, l) =>
         if isBoolTy (List.last l)
            then case Types.dest ty of
                   Type.VarBits (x, _) => x |=> 1
                 | _ => NONE
         else NONE
      | Comb (":", ty, [a, b]) =>
         (case (bitsDest ty, bitsDestTm a, bitsDestTm b) of
            (FromTo (v, x1, x2), Fix y, Fix z) => cSubst ty a b v (y + z) x1 x2
          | (Fix x, FromTo (v, y1, y2), Fix z) => cSubst ty a b v (x - z) y1 y2
          | (Fix x, Fix y, FromTo (v, z1, z2)) => cSubst ty a b v (x - y) z1 z2
          | (Fix x, Fix y, Fix z) =>
               if x = y + z then NONE else concatErr ty a b
          | _ => NONE)
      | Comb ("^", ty, [a, b]) =>
         (case evalNatTerm b of
            SOME 0 => err "Repetition (^) has bad argument." "0"
          | SOME n =>
               (case (bitsDest ty, bitsDestTm a) of
                  (Fix x, Fix y) => if x = y * n then NONE else repErr n ty a b
                | (FromTo (v, x1, x2), Fix y) =>
                     rSubst n ty a b v (y * n) x1 x2
                | (Fix x, FromTo (v, y1, y2)) =>
                     let
                        val (q, r) = IntInf.divMod (x, n)
                     in
                        if r = 0
                           then rSubst n ty a b v q y1 y2
                        else repErr n ty a b
                     end
                | (FromTo (v1, _, _), FromTo (v2, _, _)) =>
                     if n <> 1 andalso v1 = v2
                        then repErr n ty a b
                     else if n = 1 andalso v1 <> v2
                        then SOME (Type.|=> (v2, Types.dest ty))
                     else NONE
                | _ => NONE)
          | _ => NONE)
      | Comb (s as "SignExtend", ty, [a]) => extendCheck s ty a
      | Comb (s as "ZeroExtend", ty, [a]) => extendCheck s ty a
      | Comb ("<.>", _, [a, b]) =>
         (case evalNatTerm b of
            SOME n =>
               (case Term.dTypeOf a of
                  Type.FixedBits i => bitCheck (PosIntSet.singleton i) n
                | Type.VarBits (_, s) => bitCheck s n
                | _ => NONE)
          | NONE => NONE)
      | Comb ("bit-field-insert", ty, [a as Lit (Nat n), _, _, _]) =>
         (case Types.dest ty of
            Type.FixedBits i => bitCheck (PosIntSet.singleton i) (Nat.toInt n)
          | Type.VarBits (_, s) => bitCheck s (Nat.toInt n)
          | _ => NONE)
      | tm as Comb ("<..>", ty, [b, c, a]) =>
          if Types.equalTy Type.bitstringTy ty andalso isBitstringTy a
             then case (evalNatTerm b, evalNatTerm c) of
                    (SOME h, SOME l) =>
                      if l <= h
                         then NONE
                      else err "Bad extract."
                               ("bitstring<" ^ i2s h ^ ":" ^ i2s l ^
                                "> -> bitstring")
                  | _ => NONE
          else let
                  val oh = evalNatTerm b
                  val ol = evalNatTerm c
                  fun check p = if p then NONE else extractErr oh ol ty a
                  fun check2 (v, x1, x2) y l h =
                     if l <= h andalso h <! y
                        then conditionalSubst (fn () => extractErr oh ol ty a)
                                v (h + 1 - l) x1 x2
                     else extractErr oh ol ty a
               in
                  case (bitsDest ty, bitsDestTm a, oh, ol) of
                    (Fix x, Fix y, SOME h, SOME l) =>
                       check (l <= h andalso h < y andalso x = h + 1 - l)
                  | (Fix x, Fix y, SOME h, NONE) =>
                       check (x <= h + 1 andalso h < y)
                  | (Fix x, Fix y, NONE, SOME l) => check (l < y andalso x <= y)
                  | (Fix x, Fix y, NONE, NONE) => check (x <= y)
                  | (Fix x, FromTo (_, _, y), SOME h, SOME l) =>
                       check (l <= h andalso x = h + 1 - l andalso h <! y)
                  | (Fix x, FromTo (_, _, y), SOME h, NONE) =>
                       check (x <= h + 1 andalso h <! y)
                  | (FromTo (_, x, _), Fix y, SOME h, NONE) =>
                       check (h < y andalso x <= y)
                  | (FromTo (_, x, _), Fix y, NONE, SOME l) =>
                       check (l < y andalso x <= y)
                  | (FromTo x, Fix y, SOME h, SOME l) => check2 x y l h
                  | (FromTo x, FromTo (_, _, y), SOME h, SOME l) =>
                       check2 x y l h
                  | _ => NONE
               end
      | _ => NONE
in
   fun deriveBitSizes loc (u, tm) =
      let
         fun iter a t =
            case findMapTerm bitSizeSubst t of
              SOME s =>
                iter (Type.combineSubst [s] a) (typesubstTerm loc [s] t)
            | NONE => (a, t)
      in
         iter u tm
         handle Error {loc = ~1, message, value} =>
                   raise Error {loc = loc, message = message, value = value}
      end
end

(* .......................
   Expression term builder
   ....................... *)

local
   open Term
   fun unk ty = case Types.dest ty of Type.VarBits _ => true | _ => false
   fun simp tm =
      case tm of
        Comb (":", ty3, [Var ("_", ty1),
          t as Comb (":", _, [Var ("_", ty2), r])]) =>
          if unk ty1 andalso unk ty2
             then simp (Comb (":", ty3, [Var ("_", ty1), r]))
          else Comb (":", ty3, [Var ("_", ty1), simp t])
      | Comb ("-", ty, [Lit (Int v)]) => Term.mkIntLit (Int.~ v)
      | Comb ("-", ty, [Lit (Bits v)]) => Term.mkBitsLit (BitsN.neg v)
      | Comb (f, ty, l) => Comb (f, ty, List.map simp l)
      | Abs (vs, ty, b) => Abs (vs, ty, simp b)
      | _ => tm
in
   fun simpPattern loc tm = deriveBitSizes loc ([], simp tm)
   fun getPatternVariables eq allow_guess e =
      let
         fun fresh () = if eq then Type.freshEqTyVar () else Type.freshTyVar ()
         fun get guess vars =
            fn {exp = Variable "_", ...} => vars
             | {exp = Variable v, loc} =>
                  if Consts.isConstructor v
                     then vars
                  else let
                          val ty = if guess
                                      then case Patterns.lookupPattern v of
                                             SOME ty => ty
                                           | _ => fresh ()
                                   else fresh ()
                       in
                          Stringmap.extend (vars, v, ty)
                          handle Stringmap.Extend =>
                            raise Error
                               {loc = loc, value = SOME v,
                                message =
                                  "Variable occurs repeatedly in pattern."}
                       end
             | {exp = Constrained (e, y), ...} => get false vars e
             | {exp = UnaryOp ("'..'", e), ...} => get true vars e
             | {exp = UnaryOp ("-", {exp = Literal _, ...}), ...} => vars
             | {exp = UnaryOp (f, e), loc} =>
                  if Consts.isConstructor f
                     then get guess vars e
                  else raise Error
                         {loc = loc, value = SOME f,
                          message = "Operation not valid in pattern."}
             | {exp = BinOp (s, e1, e2), ...} =>
                  if s = ":" orelse s = "," orelse s = "@"
                     then get guess (get guess vars e1) e2
                  else vars
             | _ => vars
      in
         Stringmap.listItems (get allow_guess Stringmap.empty e)
      end
end

local
   open Type Term

   fun smartMkLet ((var as Term.Var (v, _), e), b) =
      let
         val freevars = List.map Term.Var (Term.freeVars b)
      in
         if not (List.exists (Term.equalTm var) freevars)
            then b
         else if Term.isVar e orelse Term.isLit e
            then Term.inst1 (v, e) b
         else Term.mkLet (var, e, b)
      end
     | smartMkLet _ = raise Fail "smartMkLet"

   fun fixed1 ty =
      if Types.equalTy Type.bitstringTy ty
         then Type.bitstringTy
      else Type.fixedTy 1

   fun update (u, loc, env) (a, b) =
      let
         fun err m v = raise Error {loc = loc, message = m, value = v}
         val (du, da, db) =
            case deriveBitSizes loc (u, Comb ("<-", Type.unitTy, [a, b])) of
               (u, Comb ("<-", _, [a, b])) => (u, a, b)
             | _ => raise Fail "update: deriveBitSizes"
         val fvs = (Term.freeVars da @ Term.freeVars db)
                     |> List.map fst |> Lib.mkSet
         fun getVars l =
            List.mapPartial (fn (Term.Var (v, _), _) => SOME v | _ => NONE) l
         fun newVar l (s, ty) =
            Term.Var (Lib.indexVariant (getVars l @ fvs) s, ty)
         fun access tm =
            case tm of
              Var (v, _) =>
                if Env.isMutableVariable (env, v)
                   then ([], tm, fn v => Comb ("<-", Type.unitTy, [tm, v]))
                else err "Not a mutable variable." (SOME v)
            | Comb ("<.>", ty, [a, b as Lit _]) =>
                let
                   val (rds, ra, wa) = access a
                   val aty = primTypeOf a
                   val va = newVar rds ("w", aty)
                in
                   ((va, ra) :: rds,
                    Comb ("<.>", ty, [va, b]),
                    fn v =>
                       wa (Comb ("bit-field-insert", aty,
                             [b, b, va, Comb ("[..]", fixed1 aty, [v])])))
                end
            | Comb ("<.>", ty, [a, b]) =>
                let
                   val (rds, ra, wa) = access a
                   val aty = primTypeOf a
                   val va = newVar rds ("w", aty)
                   val vb = newVar rds ("i", primTypeOf b)
                in
                   ((va, ra) :: (vb, b) :: rds,
                    Comb ("<.>", ty, [va, vb]),
                    fn v =>
                       wa (Comb ("bit-field-insert", aty,
                             [vb, vb, va, Comb ("[..]", fixed1 aty, [v])])))
                end
            | Comb ("<..>", ty, [h as Lit _, l as Lit _, a]) =>
                let
                   val (rds, ra, wa) = access a
                   val aty = primTypeOf a
                   val va = newVar rds ("w", aty)
                in
                   ((va, ra) :: rds,
                    Comb ("<..>", ty, [h, l, va]),
                    fn v => wa (Comb ("bit-field-insert", aty, [h, l, va, v])))
                end
            | Comb ("<..>", ty, [h, l, a]) =>
                let
                   val (rds, ra, wa) = access a
                   val aty = primTypeOf a
                   val va = newVar rds ("w", aty)
                   val vh = newVar rds ("h", primTypeOf h)
                   val vl = newVar rds ("l", primTypeOf l)
                in
                   ((va, ra) :: (vl, l) :: (vh, h) :: rds,
                    Comb ("<..>", ty, [vh, vl, va]),
                    fn v =>
                      wa (Comb ("bit-field-insert", aty, [vh, vl, va, v])))
                end
            | Comb ("abs-apply", ty, [a, b]) =>
                let
                   val (rds, ra, wa) = access a
                   val aty = primTypeOf a
                   val va = newVar rds ("f", aty)
                   val vb = newVar rds ("x", primTypeOf b)
                in
                   ((vb, b) :: (va, ra) :: rds,
                    Comb ("abs-apply", ty, [va, vb]),
                    fn v => wa (Comb ("update-map", aty, [va, vb, v])))
                end
            | Comb (f, ty, [a]) =>
                if Consts.isDestructor f
                   then let
                           val (rds, ra, wa) = access a
                           val aty = primTypeOf a
                           val va = newVar rds ("x", aty)
                        in
                          ((va, ra) :: rds,
                           Comb (f, ty, [va]),
                           fn v =>
                             wa (Comb (f, aty, [Term.mkPair (va, v)])))
                        end
                else if Consts.isAccessor f
                   then let
                           val va = newVar [] ("x", primTypeOf a)
                        in
                          ([(va, a)],
                           Comb (f, ty, [va]),
                           fn v => Comb (f, Type.unitTy, [Term.mkPair (v, va)]))
                        end
                else err "Bad update." (SOME f)
            | Comb (f, ty, []) =>
                if Consts.isAccessor f
                   then ([], tm, fn v => Comb (f, Type.unitTy, [v]))
                else err "Bad update." (SOME f)
            | _ => err "access" NONE
         val (rds, _, w) = access da
      in
         (du, List.foldr smartMkLet (w db) (List.rev rds))
      end

   fun argHint env =
      fn {exp = Constrained (_, ty), ...}: expression => ty
       | {exp = Literal s, ...} =>
          (case String.sub (s, 0) of
             #"i" => intTy
           | #"n" => natTy
           | #"s" => bitstringTy
           | #"w" => freshWordTy ()
           | #"#" => charTy
           | #"\"" => stringTy
           | _ => freshTyVar ())
       | {exp = Variable s, ...} =>
          (case Env.lookupVariable (env, s) of
             SOME { typ, ... } => Types.generalize typ
           | _ => freshTyVar ())
       | {exp = UnaryOp ("-", t), ...} => argHint env t
       | _ => freshTyVar ()

   fun refineHint ty =
      fn NoTypeHint => TypeHint (ty --> freshTyVar ())
       | TypeHint hty => TypeHint (ty --> hty)

   fun getHint l =
      fn NoTypeHint => (NoTypeHint, l)
       | hint as TypeHint hty =>
           let
              fun plucker f = Types.canUnify f hty
                              handle Fail "range" => false
           in
              case List.partition plucker l of
                ([ty], l') =>
                   (let
                       val u = Types.unify hty ty
                    in
                       (TypeHint (typeSubst u (Types.domain ty)), ty :: l')
                    end
                    handle Fail _ => (NoTypeHint, l))
              | _ => (NoTypeHint, l)
           end

   fun getBinHint l hint =
      case getHint l hint of
        (TypeHint ty, l') =>
          (let
              val (ty1, ty2) = Types.destProd ty
           in
              (TypeHint ty1, TypeHint ty2, l')
           end
           handle Fail "destProd" => (NoTypeHint, NoTypeHint, l))
      | _ => (NoTypeHint, NoTypeHint, l)

   fun pickHint hint ty =
      case hint of
        NoTypeHint => TypeHint ty
      | TypeHint ty2 => if Types.canMatch ty ty2 then hint else TypeHint ty

   fun lit s =
      let
         val c = String.sub (s, 0)
         val b = String.sub (s, 1)
         val b = if b = #"?" andalso c <> #"\"" andalso c <> #"#"
                    then if c = #"s" then #"b" else #"d"
                 else b
      in
         (c, b, String.str b ^ String.extract (s, 2, NONE))
      end
      handle General.Subscript => raise Fail "bad literal"

   val charenv = Env.addImmutableVariable (Env.empty, "c", Type.charTy)

   fun build hint env {loc, exp} =
     case exp of
        Literal "true"    => ([], mkBoolLit true)
      | Literal "false"   => ([], mkBoolLit false)
      | Literal "UNKNOWN" => ([], Term.unknown (freshTyVar ()))
      | Literal "\""      => ([], mkStringLit "")
      | Literal "()"      => ([], unitTm)
      | Literal "{}" =>
           ([], Lit (Other ("{}", Type.setTy (Type.freshEqTyVar ()))))
      | Literal s =>
          (let
              val (c, b, s') = lit s
           in
              ([],
               case c of
                 #"#"  => Term.mkCharLit (String.sub (s', 0))
               | #"\"" => Term.mkStringLit s'
               | #"?" => Lit (Other ("?" ^ s', freshTyVar ()))
               | #"n" => mkNumLit (Option.valOf (Nat.fromLit s'))
               | #"i" => mkIntLit (Option.valOf (Int.fromLit s'))
               | #"w" => Lit (Other ("?" ^ s', freshWordTy ()))
               | #"s" =>
                  Term.mkBitstringLit (Option.valOf (Bitstring.fromLit s'))
               | _ => raise Error {loc = loc, message = "Unknown literal.",
                                   value = SOME (String.str c ^ s')})
           end
           handle Option => raise Error {loc = loc, message = "Bad literal.",
                                         value = SOME s})
      | Variable "_" => ([], Var ("_", freshTyVar ()))
      | Variable v =>
          ([],
           case Env.lookupVariable (env, v) of
             SOME {typ, ...} => Var (v, typ)
           | NONE =>
               (case Consts.lookupConstant v of
                  SOME (ty as (ConstType s, _)) =>
                     (case Types.enum s v of
                         SOME n => Lit (Enum (n, s))
                       | NONE => Lit (Other (v, mkFresh ty)))
                | SOME ty => Lit (Other (v, mkFresh ty))
                | NONE =>
                    (case Consts.lookupDefinition v of
                       SOME (tm, _) =>
                          if Term.isAbs tm
                             then raise Error {loc = loc,
                                               message = "Missing body.",
                                               value = SOME v}
                          else Comb (v, mkFresh (Term.primTypeOf tm), [])
                     | _ =>
                         (case Consts.lookupException v of
                             SOME NONE => Comb (v, freshTyVar (), [])
                           | _ => raise Error {loc = loc,
                                               message = "Undeclared variable.",
                                               value = SOME v}))))
      | Cond (b, t, e) =>
           let
              val (u, ty, tms) =
                    typeCheck (loc, "if-then-else")
                       env primTypeOf (primTypeOf o List.last)
                       [boolTy ** alphaTy ** alphaTy --> alphaTy]
                       [(build boolHint, b), (build hint, t), (build hint, e)]
           in
              (u, Comb ("i-t-e", ty, tms))
           end
      | Constrained (e, ty) =>
           let
              val (u, eTm) = build (pickHint hint ty) env e
              val u1 = unify_term_to_type loc eTm ty
           in
              (combineSubst u1 u, typesubstTerm loc u1 eTm)
           end
      | BinOp ("<..>", e1, e2) =>
          (case e2 of
             {exp = BinOp (":", e3, e4), ...} =>
               let
                  val l = [natTy ** natTy ** wordTy "a" --> wordTy "b",
                           natTy ** natTy ** bitstringTy --> bitstringTy]
                  val (u, ty, tms) =
                        typeCheck (loc, "< : >")
                           env primTypeOf (K (freshTyVar ())) l
                           [(build natHint, e3), (build natHint, e4),
                            (build hint, e1)]
               in
                  (u, Comb ("<..>", ty, tms))
               end
           | _ => build hint env {loc = loc, exp = BinOp ("<.>", e1, e2)})
      | BinOp ("@", e1, e2) =>
           build hint env
             {loc = loc,
              exp =
                 UnaryOp ("Cons",
                          {loc = loc,
                           exp = Constrained
                                   ({loc = loc, exp = BinOp (",", e1, e2)},
                                    Type.alphaTy ** Type.listTy Type.alphaTy)})}
      | BinOp (s, e1, e2) =>
           if s = "!=" orelse s = "<>" orelse s = "notin"
              then let
                      val s' = if s = "notin" then "in" else "=="
                      val (u, tm) =
                         build hint env {loc = loc, exp = BinOp (s', e1, e2)}
                   in
                      (u, Comb ("not", boolTy, [tm]))
                   end
           else if Lib.mem s ["splitl", "splitr", "fields", "tokens"]
              then let
                       val tm1 = snd (build boolHint charenv e1)
                       val tm1 = Term.absList [("c", Type.charTy)] tm1
                       val (u, tm2) = build (TypeHint stringTy) env e2
                       val u2 = unify_term_to_type loc tm2 Type.stringTy
                       val tm2 = typesubstTerm loc u2 tm2
                       val ty = if s = "fields" orelse s = "tokens"
                                   then listTy stringTy
                                else stringTy ** stringTy
                   in
                      (combineSubst u2 u, Comb (s, ty, [tm1, tm2]))
                   end
           else
             (case Consts.lookupOperation s of
                SOME l =>
                  let
                     val hint' = refineHint
                                   (argHint env e1 ** argHint env e2) hint
                     val (llit, rlit, l) = getBinHint l hint'
                     val (u, ty, tms) =
                        typeCheck (loc, s) env primTypeOf (K (freshTyVar ()))
                           l [(build llit, e1), (build rlit, e2)]
                     val env' = Env.updateEnv u env
                  in
                     if s = "<-"
                        then update (u, loc, env') (Lib.pair tms)
                     else (u, Comb (s, ty, tms))
                  end
              | NONE => badOperation loc s)
      | UnaryOp ("{..}", e) =>
           let
              val hint' =
                 case hint of
                    TypeHint (ParamType (SetTy, ty), s) => TypeHint (ty, s)
                  | _ => NoTypeHint
              val l = tupleToList e
              val expect = listProd eqAlphaTy (tl l)
              val (u, ty, tms) =
                    typeCheck (loc, "{..}") env primTypeOf
                       (setTy o primTypeOf o hd)
                       [expect --> setTy eqAlphaTy] (mapr (build hint') l)
           in
              (u, Comb ("{..}", ty, tms))
           end
      | UnaryOp ("!", e) => build hint env {loc = loc, exp = UnaryOp ("not", e)}
      | UnaryOp ("UNKNOWN", e) =>
          let
             val (u, tm) = build NoTypeHint env e
          in
             (u,
              Term.mkApply
                 (Term.unknown (Term.typeOf tm --> freshTyVar ()), tm))
          end
      | UnaryOp ("FP64", {exp = Literal s, ...}) =>
          if String.sub (s, 0) = #"\""
             then case FP64.fromString (Tag.remove s) of
                     SOME r => ([], Term.Lit (Term.Bits r))
                   | _ => raise Error {loc = loc, message = "Bad float string.",
                                       value = SOME s}
          else raise Error {loc = loc, message = "Bad float literal.",
                            value = SOME s}
      | UnaryOp (s, e) =>
          let
             val env_typ = case Env.lookupVariable (env, s) of
                              SOME {typ, ...} => [typ]
                            | NONE => []
             val op_typ =
                if s = "-"  (* special case because binary & unary *)
                   then [wordTy "a" --> wordTy "a", intTy --> intTy]
                else if s = "[..]" (* general casting map *)
                   then Types.castTypes ()
                else case Consts.lookupOperation s of
                        SOME l => l
                      | NONE => []
             val l = env_typ @ op_typ
             val () = if List.null l then badOperation loc s else ()
             val (hint', l) = getHint l (refineHint (argHint env e) hint)
             val (u, ty, tm) =
                typeCheck (loc, s) env primTypeOf (K (freshTyVar ())) l
                   [(build hint', e)]
             val htm = hd tm
             val fty = primTypeOf htm --> ty
          in
             (u, if not (List.null env_typ)
                    andalso Types.canMatch (Type.typeSubst u (hd env_typ)) fty
                    then mkApply (Var (s, fty), htm)
                 else Comb (s, ty,
                            if s = "[..]" then mkIntLit loc :: tm else tm))
          end
      | MatchCases (e, ps) =>
           let
              val m = Type.freshMarker ()
              val (u1, tm) = build NoTypeHint env e
              val env1 = Env.updateEnv u1 env
              val aTy = Term.primTypeOf tm
              val expect = listProd (aTy --> betaTy) (tl ps)
              val (u2, ty, tms) =
                    typeCheck (loc, "match") env1 patType (primTypeOf o hd)
                       [expect --> betaTy] (mapr (buildCase aTy hint) ps)
              val tm = typesubstTerm loc u2 tm
              val u3 = Type.filterSubst m (combineSubst u2 u1)
           in
              (u3, Comb ("match-loc", ty, mkIntLit loc :: tm :: tms))
           end
      | Apply ({exp = Variable f, ...}, x) =>
           build hint env {loc = loc, exp = UnaryOp (f, x)}
      | Apply (f, x) =>
           let
              val expect = (alphaTy --> betaTy) ** alphaTy --> betaTy
              val (u, ty, tms) =
                    typeCheck (loc, "apply-fn")
                       env primTypeOf (Types.range o primTypeOf o hd)
                       [expect] [(build NoTypeHint, f), (build NoTypeHint, x)]
           in
              (u, mkApply (Lib.pair tms))
           end
   and buildCase aTy hint env {loc, exp = e} =
      case e of
         BinOp ("case", e1, e2) =>
           let
              val m = Type.freshMarker ()
              val vars = getPatternVariables true true e1
              val env1 = Env.addImmutableVariableList (env, vars)
              val (u1, tm1) = build (TypeHint aTy) env1 e1
              val (u2, tm1) = simpPattern loc tm1
              val u1 = combineSubst u2 u1
              val u2 = unify_term_to_type loc tm1 aTy
              val tm1 = typesubstTerm loc u2 tm1
              val u1 = combineSubst u2 u1
              val env1 = Env.updateEnv u1 env1
              val (u2, tm2) = build hint env1 e2
              val tm1 = typesubstTerm loc u2 tm1
              val u2 = Type.filterSubst m (combineSubst u2 u1)
           in
              (u2, Term.mkCase (tm1, tm2))
           end
       | _ => raise Fail "buildCase"

in
   fun buildExpression hint env (t as {loc, ...}) =
      deriveBitSizes loc (build hint env t)
end

(* ......................
   Statement term builder
   ...................... *)

local
   open Type Term

   fun buildS hint env ({loc, stmt}: statement) =
      let
         fun build h e = (buildS h, {loc = loc, stmt = Expression (#exp e)})
         val buildE = build hint
         val buildBE = build boolHint
         val buildNE = build natHint
      in
         case stmt of
            Expression (BinOp ("=", _, _)) =>
              raise Error {loc = loc, message = "Redundant value assignment.",
                           value = NONE}
          | Expression (BinOp ("var =", {exp = Variable _, ...}, _)) =>
              raise Error {loc = loc, message = "Redundant variable.",
                           value = NONE}
          | Expression (Constrained ({exp = BinOp ("=", _, _), ...}, _)) =>
              raise Error {loc = loc, message = "Redundant value assignment.",
                           value = NONE}
          | Expression
             (Constrained
               ({exp = BinOp ("var =", {exp = Variable _, ...}, _), ...}, _)) =>
              raise Error {loc = loc, message = "Redundant variable.",
                           value = NONE}
          | AssignDecl (e1, e2) =>
              buildExpression NoTypeHint env
                 {loc = loc, exp = BinOp ("<-", e1, e2)}
          | Expression e => buildExpression hint env {loc = loc, exp = e}
          | When (e, s) =>
              let
                 val (u, ty, tms) =
                       typeCheck (loc, "when") env primTypeOf (K unitTy)
                          [boolTy ** unitTy --> unitTy]
                          [buildBE e, (buildS unitHint, s)]
              in
                 (u, Comb ("i-t-e", ty, tms @ [Term.unitTm]))
              end
          | For (v as {exp = Variable i, ...}, n1, n2, s) =>
              let
                 val env1 = Env.addImmutableVariable (env, i, natTy)
                 val (u, ty, tms) =
                     typeCheck (loc, "for") env1 primTypeOf (K unitTy)
                        [natTy ** natTy ** natTy ** unitTy --> unitTy]
                        [buildNE v, buildNE n1, buildNE n2,
                         (buildS unitHint, s)]
                 val (tm, l) = lastButlast tms
              in
                 (u, Comb ("for", ty, tl l @ [Term.absList [(i, natTy)] tm]))
              end
          | Foreach (v as {exp = Variable i, ...}, t, s) =>
              let
                 val m = Type.freshMarker ()
                 val (u, tm) = buildExpression NoTypeHint env t
                 val env1 = Env.updateEnv u env
                 val aTy = case Lib.total (Types.destParam o Term.typeOf) tm of
                              SOME ty => ty
                            | NONE => Type.alphaTy
                 val env1 = Env.addImmutableVariable (env1, i, aTy)
                 val (u, ty, tms) =
                     typeCheck (loc, "foreach") env1 primTypeOf (K unitTy)
                        [aTy ** listTy aTy ** unitTy --> unitTy]
                        [build NoTypeHint v, build NoTypeHint t,
                         (buildS unitHint, s)]
                 val (tm, l) = lastButlast tms
                 val ity = Term.typeOf (hd l)
              in
                 (Type.filterSubst m u,
                  Comb ("foreach", ty, tl l @ [Term.absList [(i, ity)] tm]))
              end
          | Conditional (e, s1, s2) =>
              let
                 val (u, ty, tms) =
                       typeCheck (loc, "if-then-else")
                          env primTypeOf (primTypeOf o List.last)
                          [boolTy ** alphaTy ** alphaTy --> alphaTy]
                          [buildBE e, (buildS hint, s1), (buildS hint, s2)]
              in
                 (u, Comb ("i-t-e", ty, tms))
              end
          | MatchStatement (e, ps) =>
              let
                 val m = Type.freshMarker ()
                 val (u1, tm) = buildExpression NoTypeHint env e
                 val env1 = Env.updateEnv u1 env
                 val aTy = Term.primTypeOf tm
                 val expect = listProd (aTy --> betaTy) (tl ps)
                 val (u2, ty, tms) =
                        typeCheck (loc, "match") env1 patType (primTypeOf o hd)
                           [expect --> betaTy] (mapr (buildCase aTy hint) ps)
                 val tm = typesubstTerm loc u2 tm
                 val u3 = Type.filterSubst m (combineSubst u2 u1)
              in
                 (u3, Comb ("match-loc", ty, mkIntLit loc :: tm :: tms))
              end
          | Sequence [] => raise Fail "Empty sequence"
          | Sequence [s] => buildS hint env s
          | Sequence
               ({stmt = Expression (BinOp ("=", t, e)), loc = loc2} :: s2) =>
              let
                 val m = Type.freshMarker ()
                 val (u1, expr) = buildExpression NoTypeHint env e
                 val vars = getPatternVariables false false t
                 val env1 = Env.addImmutableVariableList (env, vars)
                 val (u2, pat) =
                    buildExpression NoTypeHint env1
                       {loc = loc2, exp = Constrained (t, Term.typeOf expr)}
                 val u2 = combineSubst u2 u1
                 val env2 = Env.updateEnv u2 env1
                 val (u3, body) =
                    buildS hint env2 {loc = loc, stmt = Sequence s2}
                 val u3 = combineSubst u3 u2
                 val pat = typesubstTerm loc u3 pat
                 val expr = typesubstTerm loc u3 expr
              in
                 (Type.filterSubst m u3, mkLet (pat, expr, body))
              end
          | Sequence
              ({stmt =
                 Expression
                   (BinOp ("var =", {exp = Variable s, ...}, e)), ...} :: s2) =>
              let
                 val m = Type.freshMarker ()
                 val (u1, tm1) = buildExpression NoTypeHint env e
                 val env' = Env.addMutableVariable
                              (Env.updateEnv u1 env, s, Term.primTypeOf tm1)
                 val (u2, tm2) =
                    buildS hint env' {loc = loc, stmt = Sequence s2}
                 val tm1 = typesubstTerm loc u2 tm1
                 val ty1 = Term.primTypeOf tm1
              in
                 (Type.filterSubst m (combineSubst u2 u1),
                  Comb ("var =", Term.primTypeOf tm2, [Var (s, ty1), tm1, tm2]))
              end
          | Sequence ({stmt = AssignDecl (e1, e2), loc = loc2} :: s2) =>
              let
                 val m = Type.freshMarker ()
                 val (u1, tm1) = buildExpression NoTypeHint env
                                   {loc = loc2, exp = BinOp ("<-", e1, e2)}
                 val env' = Env.updateEnv u1 env
                 val (u2, tm2) =
                    buildS hint env' {loc = loc, stmt = Sequence s2}
                 val tm1 = typesubstTerm loc u2 tm1
              in
                 (Type.filterSubst m (combineSubst u2 u1),
                  Comb (";", Term.primTypeOf tm2, [tm1, tm2]))
              end
          | Sequence (s1 :: s2) =>
              let
                 val (u, ty, tms) =
                       typeCheck (loc, ";") env primTypeOf
                          (primTypeOf o List.last)
                          [unitTy ** alphaTy --> alphaTy]
                          [(buildS unitHint, s1),
                           (buildS hint, {loc = loc, stmt = Sequence s2})]
              in
                 (u, Comb (";", ty, tms))
              end
          | _ => raise Fail "buildStatement"
      end
   and buildCase aTy hint env (e as {loc, ...}, s) =
        let
           val m = Type.freshMarker ()
           val vars = getPatternVariables true true e
           val env1 = Env.addImmutableVariableList (env, vars)
           val (u1, tm1) = buildExpression (TypeHint aTy) env1 e
           val (u2, tm1) = simpPattern loc tm1
           val u1 = combineSubst u2 u1
           val u2 = unify_term_to_type loc tm1 aTy
           val tm1 = typesubstTerm loc u2 tm1
           val u1 = combineSubst u2 u1
           val env1 = Env.updateEnv u1 env1
           val (u2, tm2) = buildS hint env1 s
           val tm1 = typesubstTerm loc u2 tm1
           val u2 = Type.filterSubst m (combineSubst u2 u1)
        in
           (u2, Term.mkCase (tm1, tm2))
        end
in
   fun buildStatement hint env (t as {loc, ...}) =
      deriveBitSizes loc (buildS hint env t)
end

(* -------------------------------------------------------------------------
   Function/procedure/component definition parser
   ------------------------------------------------------------------------- *)

local
   val verb = ref true
in
   fun pv s = if !verb then print (s ^ "\n") else ()
   fun pr s name = pv ("<" ^ s ^ "> " ^ name)
   fun withVerb b f x =
      let
         val saved = !verb
         val () = verb := b
         val r = f x handle e => (verb := saved; raise e)
         val () = verb := saved
      in
         r
      end
   fun verbose b = verb := b
end

local
   fun err loc =
      raise Error {loc = loc, message = "Bad bit-vector constraint.",
                   value = NONE}
   fun constraints input =
     ( token (Name "with") ++
       puresequence (varorconst ++ constrain) (token (Reserved "and"))
        >> (fn (_, l) =>
              let
                 val c = Constrain.fromList (List.map (snd ## I) l)
              in
                 Type.setConstraint c; c
              end)
     ) input
   and constraint input =
     ( token (Name "with") ++ varorconst ++ token (Reserved "in") ++
       puresequence number (token (Symbol ","))
        >> (fn (((_, (_, v)), _), l) =>
              let
                 val l = List.map snd l
                 val c = Constrain.singleton (v, PosIntSet.fromList l)
              in
                 Type.setConstraint c; c
              end)
     ) input
   and constrain input =
       pick
          (fn (_, Reserved "in") => posintset
            | (loc, Symbol ">=") =>
               number
                 >> (fn (_, n) => if n < 2 then err loc
                                  else PosIntSet.fromRangeList [(n, NONE)])
            | (loc, Symbol ">") =>
               number
                 >> (fn (_, n) => if n < 1 then err loc
                                  else PosIntSet.fromRangeList [(n + 1, NONE)])
            | (loc, Symbol "<") =>
               number
                 >> (fn (_, n) => if n < 3 then err loc
                                  else PosIntSet.fromRangeList
                                          [(1, SOME (n - 1))])
            | (loc, Symbol "<=") =>
               number
                 >> (fn (_, n) => if n < 2 then err loc
                                  else PosIntSet.fromRangeList [(1, SOME n)])
            | _ => parseError input "Syntax error.") input
   and posintset input =
     ( puresequence range (token (Symbol ","))
        >> (fn l => let
                       val s = PosIntSet.fromRangeList l
                    in
                       if PosIntSet.issingleton s
                          then parseError input "Syntax error: singleton set."
                       else s
                    end)
     ) input
   and range input =
     ( number ++ option ( token (Symbol "-") ++ number >> (snd o snd)
                       || token (Symbol "...") >> (K ~1))
          >> (fn ((_, i), SOME j) => (i, if j = ~1 then NONE else SOME j)
               | ((_, i), NONE) => (i, SOME i))
     ) input
in
   val constraints = constraints
   val singleconstraint = constraint
end

local
   fun validate e1 e2 vs =
      let
         fun typeOkay ty =
            (not (Type.hasFreshTypeVars ty) orelse raise Fail "infer")
            andalso
            (case List.find (fn s => not (Stringset.member (vs, s)))
                            (Stringset.listItems (Type.bitsTypeVars ty)) of
               SOME s => e1 s
             | NONE => true)
         fun check tm =
            case tm of
               Term.Lit (Term.Other (_, ty)) => typeOkay ty
             | Term.Lit _ => true
             | Term.BVar (_, ty) => typeOkay ty
             | Term.Var (_, ty) => typeOkay ty
             | Term.Comb (f, ty, l) =>
                  (List.all check l handle Fail "infer" => e2 tm) andalso
                  typeOkay ty
             | Term.Abs (_, ty, t) => check t andalso typeOkay ty
      in
         fn tm => check tm handle Fail "infer" => e2 tm
      end
in
   fun validateDefn name loc =
      let
         fun err m s =
            raise Error {loc = loc, message = m ^ " in " ^ name ^ ".",
                         value = SOME s}
      in
         validate
           (fn s => err "Bit width not constrained by type of operation" s)
           (fn tm => err "Unable to infer all types" (Term.rawTermToString tm))
      end
   val validateStatement =
      validate
         (fn s => raise Fail ("Unknown bit-vector width: " ^ s ^ "."))
         (fn _ => raise Fail ("Unable to infer all types.")) Stringset.empty
end

local
   fun mwarn loc s =
      warn ("Match pattern" ^ s ^ " in match from line " ^
            Int.toString loc ^ ".")
   fun castsAndMatches t =
      case t of
         Term.Comb ("[..]", ty, [Term.Lit (Term.Int loc), a]) =>
            if Types.goodCast ty
               then Term.Comb ("[..]", ty, [a])
            else raise
                   Term.TypeCheck
                     {loc = loc, operation = "[ .. ]", args = [a],
                      message = "Bad type cast.",
                      valid_types = List.map Types.domain (Types.castTypes ())}
       | Term.Comb ("match-loc", ty, Term.Lit (Term.Int loc) :: mcs) =>
           let
              val tm = Term.Comb ("match", ty, mcs)
              val (red, miss) = Term.checkMatch tm
           in
              case red of
                 [] => ()
               | [i] => mwarn loc (" " ^ Int.toString (i + 1) ^
                                   " redundant")
               | l => let
                         fun suc i = i + 1
                         val s = List.map (Int.toString o suc) l
                         val (h, r) = lastButlast s
                         val r = commify I r ^ " and " ^ h
                      in
                         mwarn loc ("s " ^ r ^ " redundant")
                      end
               ; if miss then mwarn loc "s not exhaustive" else ()
               ; tm
           end
       | _ => raise Term.NoConv
in
   val castsAndMatches = Term.depthconv castsAndMatches
end

local
   fun addConstraint ty =
      let
         fun iter s =
            case s of
               {loc = loc, stmt = Expression e} =>
                  {loc = loc,
                   stmt = Expression (Constrained ({loc = loc, exp = e}, ty))}
             | {loc = loc, stmt = Conditional (b, s1, s2)} =>
                  {loc = loc, stmt = Conditional (b, iter s1, iter s2)}
             | {loc = loc, stmt = MatchStatement (m, l)} =>
                  {loc = loc, stmt = MatchStatement (m, List.map (I ## iter) l)}
             | {loc = loc, stmt = Sequence l} =>
                 let
                    val (h, t) = lastButlast l
                 in
                    {loc = loc, stmt = Sequence (t @ [iter h])}
                 end
             | s => s
      in
         iter
      end

   fun getTyVars l =
      let open Stringset in
         big union (List.map Type.bitsTypeVars l)
      end

   val op |=> = Type.|=>

   fun mkDef (ast : bool) (((retty, (loc, name)), ((cons, m), args)), def) =
      let
         val () = ignore (name <> "Run" orelse
                          raise Fail "Run is a reserved name")
         val tys = List.map snd args
         val ty = Type.foldProdList tys
                  handle Fail "foldProdList: empty" => Type.unitTy
         val tyvars = getTyVars (retty :: tys)
         fun red v = not (Stringset.member (tyvars, v))
         val cvars = Constrain.toList cons
         val () = case List.find (red o fst) cvars of
                    SOME (v, _) =>
                      raise Error {loc = loc, message = "Redundant constraint.",
                                   value = SOME v}
                  | NONE => ()
         val subst =
            Type.typeSubst
               (List.map (fn (v, s) => v |=> Type.VarBits (v, s)) cvars)
         val args = List.map (I ## subst) args
         val retty = subst retty
         val ty = subst ty
         val tyvars = Stringset.listItems tyvars
      in
         case findDuplicate (name :: tyvars @ List.map fst args) of
           SOME v => raise Error {loc = loc, message = "Bad argument.",
                                  value = SOME v}
         | NONE =>
            { loc = loc,
              name = name,
              args = args,
              ast = ast,
              tyvars = tyvars,
              typ = if List.null args then retty else ty --> retty,
              retty = retty,
              def = addConstraint retty def,
              measure =
                Option.map
                   (fn (s: string, e) =>
                      (if s = "" then "" else OS.FileSys.fullPath s,
                       {loc = loc, exp = Constrained (e, Type.natTy)})) m }
      end

   val sizeMap = Stringmap.fromList o List.map (fn v => (v, Term.mkSize v))

   fun argsTy u (args : (string * Type.ty) list) =
      Type.typeSubst u (Type.foldProdList (List.map snd args))

   val badSubstVar =
      fn Type.SubstBits (v, _) => Type.isFreeVar v
       | Type.SubstType (v, _) => Type.isFreeVar v

   fun fix_rec_call0 (name, typ) tm =
      let
         val hasvar = ref false
         val ok = ref true
         fun loop tm =
            case tm of
               Term.Var (f, ty1) =>
                 if f = name andalso Types.equalTy typ ty1
                    then (ok := (!ok andalso !hasvar); Term.Comb (f, ty1, []))
                 else (hasvar := true; tm)
             | Term.Comb ("var =", ty, [Term.Var (a, aty), tm1, tm2]) =>
                 if a = name andalso Types.equalTy typ aty
                    then tm
                 else Term.Comb
                         ("var =", ty, [Term.Var (a, aty), loop tm1, loop tm2])
             | Term.Comb (f, ty, l) => Term.Comb (f, ty, List.map loop l)
             | Term.Abs (f, ty, b) => Term.Abs (f, ty, loop b)
             | _ => tm
         val ftm = loop tm
      in
         (!ok, ftm)
      end

   fun fix_rec_call (name, typ) =
      let
         fun loop tm =
            case tm of
               Term.Comb ("abs-apply", ty1, [Term.Var (f, ty2), a]) =>
                 if f = name andalso Types.equalTy typ ty2
                    then Term.Comb (f, ty1, [a])
                 else tm
             | Term.Comb ("var =", ty, [Term.Var (a, aty), tm1, tm2]) =>
                 if a = name andalso Types.equalTy typ aty
                    then tm
                 else Term.Comb
                         ("var =", ty, [Term.Var (a, aty), loop tm1, loop tm2])
             | Term.Comb (f, ty, l) => Term.Comb (f, ty, List.map loop l)
             | Term.Abs (f, ty, b) => Term.Abs (f, ty, loop b)
             | _ => tm
      in
         loop
      end

   fun getPosintset v =
      Option.getOpt
         (Constrain.lookup (snd (Type.constrainTy v), v), PosIntSet.univ)

   fun renameTyvars defn =
      List.foldl
         (fn (v, a) =>
            let
               val needsRename =
                  fn Term.Abs (l, _, _) =>
                       Option.isSome (List.find (fn (x, _) => x = v) l)
                   | _ => false
            in
               if Option.isSome (Term.findTerm needsRename defn)
                  then (v |=> Type.VarBits (v ^ "'", getPosintset v)) :: a
               else a
            end) []

   fun mkDefn env {loc, name, def, ast, typ, retty, args, tyvars, measure} =
      let
         val () = (* not sure if this check is strictly necessary? *)
            Env.checkFreeList env
               (fn s => raise Error {loc = loc, message = "Name already used.",
                                     value = SOME s})
               (List.map fst args @ tyvars)
         val vs = Lib.mapl Type.natTy tyvars
         val absArgs = Term.inst (sizeMap tyvars) o (Term.absList args)
         val env' = Env.addImmutableVariableList (env, (name, typ) :: vs @ args)
         val (u, defn) = buildStatement (Term.TypeHint retty) env' def
         val ty = Term.primTypeOf defn
         val (got, expect) =
            if List.null args
               then (ty, retty)
            else (argsTy u args --> ty, argsTy [] args --> retty)
         fun err () =
            raise Error
               {loc = loc, message = "Bad type in \"" ^ name ^ "\".",
                value = SOME (Type.typeToString expect ^ " expected but got " ^
                              Type.freshTypeString got)}
         val m = Types.match got expect handle Types.TypeMatch _ => err ()
         val () = ignore (not (Option.isSome (List.find badSubstVar m))
                          orelse err ())
         val defn = absArgs (typesubstTerm loc m defn)
         val defn =
            if List.null args
               then let
                       val (ok, d) = fix_rec_call0 (name, typ) defn
                    in
                       ok orelse raise Error {loc = loc, value = SOME name,
                                              message = "Unsafe recursive call"}
                       ; d
                    end
            else fix_rec_call (name, typ) defn
         val defn = castsAndMatches defn
         val _ = validateDefn name loc (Stringset.fromList tyvars) defn
         val mdef =
            Option.map
               (castsAndMatches o absArgs o snd o
                buildExpression (Term.TypeHint Type.natTy) env' o snd) measure
         val sbst = typesubstTerm loc (renameTyvars defn tyvars)
      in
         (if ast then (pr "DEF" name; Tag.mkAST name)
                 else (pr "FUN" name; name),
          sbst defn,
          Option.map (fn m => (fst (Option.valOf measure), sbst m)) mdef
            : Consts.measure)
      end

   fun specification env input =
      ( spec
          >> (fn l =>
               case l of
                 [] => (Consts.defineRun (); pr "DEF" "Run")
               | [d] => Consts.addDefinition (mkDefn env d)
               | [r, w] => let
                              val rd as (name, tm1, _) = mkDefn env r
                              val () = Consts.addDefinition rd
                              val (_, tm2, _) = withVerb false (mkDefn env) w
                              val () = Consts.delConst name
                           in
                              Consts.addAccessor (name, tm1, tm2)
                           end
               | _ => raise Fail "specification")
      ) input
   and spec input =
      ( token (Reserved "define") ++
           (token (Name "Run") >> (K []) || define) >> snd
     || token (Reserved "component") ++ component >> snd
     || function
      ) input
   and component input =
      ( varorconst ++
        farguments (accept (Constrain.empty, NONE)) "::" ++
        typeexpr ++ oconstraints ++ token (Symbol "{") ++
        token (Name "value") ++ token (Symbol "=") ++ definition ++
        token (Reserved "assign") ++ varorconst ++
        token (Symbol "=") ++ definition ++ token (Symbol "}")
          >> (fn (((((((((((((loc1, name), (_, a)), ret), cm), _), _), _),
                             def1), _), (loc2, d)), _), def2), _) =>
                 List.map (mkDef false)
                    [(((ret, (loc1, name)), (cm, a)), def1),
                     (((Type.unitTy, (loc2, "write'" ^ name)),
                       (cm, (d, ret) :: a)), def2)])
      ) input
   and define input =
      ( puresequence varorconst (token (Symbol ">")) ++
        farguments osingleconstraint "=" ++ definition
           >> (fn ((names, (cm, a)), d) =>
                 let
                    val loc = fst (hd names)
                    val names = List.map snd names
                    val name = List.last names
                    val _ =
                       not (Consts.runDefined ()) orelse
                       raise Error {loc = loc, value = SOME name,
                                    message = "Further definitions not allowed \
                                              \after Run is defined."}
                    val () = if Tag.contains Tag.ASTChar name
                                then raise Error
                                       {loc = loc, value = SOME name,
                                        message = "Bad definition name."}
                             else ()
                    val d as {typ, ...} =
                       mkDef true (((Type.unitTy, (loc, name)), (cm, a)), d)
                    val oty = if List.null a then NONE else SOME (Type.dom typ)
                    val () = Consts.augmentAST (names, fst cm, oty)
                 in
                    [d]
                 end)
      ) input
   and function input =
      ( typeexpr ++ varorconst ++ farguments oconstraints "=" ++ definition
           >> (Lib.singleton o mkDef false)
      ) input
   and farguments f s input =
      ( f ++ token (Symbol s)
           >> (I ## K [])
     || token (Symbol "(") ++ token (Symbol ")") ++ f ++ token (Symbol s)
           >> (fn ((_, c), _) => (c, [("_", Type.unitTy)]))
     || token (Symbol "(") ++ arguments ++ token (Symbol ")") ++ f ++
        token (Symbol s)
           >> (fn ((((_, a), _), c), _) => (c, a))
     ) input
   and arguments input =
      ( puresequence ((varorconst >> snd) ++ annotation) (token (Symbol ","))
      ) input
   and oconstraints input =
     ( option constraints ++
       option (option (token (Name "HOL") ++ somestring) ++
               token (Name "measure") ++ expression)
           >> (fn (c, e) => (Option.getOpt (c, Constrain.empty),
                             Option.map
                                (fn ((os, _), exp) =>
                                  (case os of
                                      SOME (_, (_, s)) => s
                                    | NONE => "", exp)) e))
     ) input
   and osingleconstraint input =
     ( option singleconstraint
          >> (fn c => (Option.getOpt (c, Constrain.empty), NONE))
     ) input
in
   val specification = specification
end

(* -------------------------------------------------------------------------
   Register specification parser
   ------------------------------------------------------------------------- *)

(*
  register TEST :: bits(16) {
     15:    N
     14:    RAO!
     13:    RAZ!
     12:    UNK!
     11-10: Z
     9-8:   RAO!
     7-6:   RAZ!
     5-4:   UNK!
  }
*)

val checkNoFreeVars = List.app (Type.checkConstraint Constrain.empty)

fun addRecord (name, l) =
   let
      val l = msort (String.compare o (fst ## fst)) l
      val tys = List.map snd l
      val () = checkNoFreeVars tys
      val isEq = List.all Types.isEqType tys
      val ty = Type.mkConstType name
      val cons = Tag.mkRecord name
      val arg = ("x", ty)
      val vs = List.map Term.Var l
      val pat = Term.Comb (cons, ty, vs)
   in
      Types.addConst (name, {eq = isEq, def = Types.Record l, ast = false})
      ; List.foldl (fn (v as (c, typ), (p, q)) =>
         let
            val tm1 = Term.absList [arg]
                         (Term.mkMatch (Term.Var arg, [(pat, Term.Var v)]))
            val arg2 = ("y", typ)
            val pat2 = Term.Comb (cons, ty, p @ (Term.Var arg2 :: tl q))
            val tm2 = Term.absList [arg, arg2]
                         (Term.mkMatch (Term.Var arg, [(pat, pat2)]))
         in
            Consts.addDestructor (c, tm1, tm2, false)
            ; case List.getItem q of
                 SOME (h, t) => (p @ [h], t)
               | NONE => (p, [])
         end) ([], vs) l
      ; Consts.addConstructor (cons, Type.foldProdList tys --> ty)
   end

local

(*

val name = "PSR"
val sz = 32
val fields =
   [
    ([(31,31)], Named "N"),
    ([(30,30)], Named "Z"),
    ([(29,29)], Named "C"),
    ([(28,28)], Named "V"),
    ([(27,27)], Named "Q"),
    ([(15,10), (26,25)], Named "IT"),
    ([(24,24)], UNK),
    ([(23,20)], RAZ),
    ([(19,16)], RAO),
    ([(9,9)], Named "E"),
    ([(8,8)], Named "A"),
    ([(7,7)], Named "I"),
    ([(6,6)], Named "F"),
    ([(5,5)], Named "T"),
    ([(4,0)], Named "M")
   ]

PolyML.print_depth 100

*)

   datatype field = RAZ | RAO | UNK | Named of string

   fun rangeErr m name (h, l) =
      raise Fail(m ^ ": " ^ name ^ ": " ^ Int.toString h ^ "-" ^ Int.toString l)

   fun szToType n = if n = 1 then Type.boolTy else Type.fixedTy n

   fun wsize w = Option.valOf (Type.bitsSize (Term.typeOf w))

   fun mkConcat (x, y) =
      Term.Comb (":", Type.fixedTy (wsize x + wsize y), [x, y])

   val mkCast =
      fn t as Term.Comb ("<..>", ty, [h, l, x]) =>
           if Types.equalTy ty (Type.fixedTy 1) andalso Term.equalTm h l
              then Term.Comb ("<.>", Type.boolTy, [x, h])
           else t
       | t => t

   val F = Term.mkBoolLit false
   val T = Term.mkBoolLit true
   val U = Term.unknown Type.boolTy

   fun bit s n ty =
      if Types.equalTy ty Type.boolTy
         then Term.Var (s, Type.boolTy)
      else Term.Comb ("<.>", Type.boolTy, [Term.Var (s, ty), Term.mkNatLit n])

   fun getField (name, tm1, msz) ((x as (h, l)) :: t, Named s) =
         let
            fun mkExtract (h, l) =
               Term.Comb ("<..>", Type.fixedTy (h + 1 - l),
                         [Term.mkNatLit h, Term.mkNatLit l, tm1])
            val (sz, tm2) =
               List.foldl
                  (fn (x as (h, l), (sz, tm2)) =>
                      if h < msz andalso l <= h then
                         (sz + h + 1 - l, mkConcat (mkExtract x, tm2))
                      else rangeErr "bad bit range" name x)
                  (h + 1 - l, mkExtract x) t
         in
            SOME (s, szToType sz, mkCast tm2)
         end
     | getField _ _ = NONE

   fun findField (name, i) (l, x) =
      case
         List.foldl
            (fn ((h, l), (pos, sz)) =>
               let
                  val w = h + 1 - l
               in
                  (case pos of
                     NONE =>
                       if l <= i andalso i <= h
                          then SOME (sz + i - l)
                       else pos
                   | SOME _ =>
                       if l <= i andalso i <= h
                          then rangeErr "overlapping bit range" name (h, l)
                       else pos, sz + w)
               end) (NONE, 0) l
      of (SOME n, sz) => SOME (case x of
                                 RAZ => F
                               | RAO => T
                               | UNK => U
                               | Named s => bit s n (szToType sz))
       | (NONE, _) => NONE

   val unnamed =
      fn (Term.Lit (Term.Other ("UNKNOWN", _)), i) => SOME i
       | (Term.Lit (Term.Bool _), i) => SOME i
       | _ => NONE

   fun compact l =
      let
         fun iter (a, l) =
            case (a, l) of
              (a, []) => a
            | ([], x :: t) => iter ([(x, x)], t)
            | (a as ((h, l) :: r), x :: t) =>
                iter (if h + 1 = x then (x, l) :: r else (x, x) :: a, t)
      in
         iter ([], l)
      end

   fun fst3 (a, _, _) = a

   fun split x =
      let
         fun iter (l, r, []) = (l, r)
           | iter (l, r, (a, b, c) :: t) = iter ((a, b) :: l, c :: r, t)
      in
         iter ([], [], List.rev x)
      end

   fun mergeOptionList a b =
      List.map (fn (_, SOME t) => t | (t, NONE) => t) (ListPair.zip (a, b))

   val w1 = Type.fixedTy 1
   val w2 = Type.fixedTy 2
   fun mk_w1 b = BitsN.B (if b then 1 else 0, 1)

   val bitToBits =
      fn Term.Comb ("<.>", _, [tm, i]) => Term.Comb ("<..>", w1, [i, i, tm])
       | t => t

   fun formConcats a =
      fn [] => a
       | (v as Term.Var _) :: d =>
           formConcats (Term.Comb ("[..]", w1, [v]) :: a) d
       | Term.Lit (Term.Bool b) :: d =>
           formConcats
              (case a of
                  Term.Lit (Term.Bits n) :: r =>
                     Term.mkBitsLit (BitsN.@@ (mk_w1 b, n)) :: r
                | _ => Term.mkBitsLit (mk_w1 b) :: a) d
       | (t as Term.Comb ("<.>", _, [tm1, Term.Lit (Term.Nat n1)])) :: d =>
           (case a of
               Term.Comb ("<..>", _,
                          [Term.Lit (Term.Nat n2),
                           Term.Lit (Term.Nat n3), tm2]) :: r =>
                  formConcats
                     (if n1 = n2 + 1 andalso Term.equalTm tm1 tm2
                         then let
                                 val ty = Type.fixedTy (n2 + 2 - n3)
                              in
                                 if n3 = 0 andalso
                                    Types.equalTy (Term.primTypeOf tm2) ty
                                    then tm2 :: r
                                 else Term.Comb
                                     ("<..>", ty,
                                      [Term.Lit (Term.Nat (n2 + 1)),
                                       Term.Lit (Term.Nat n3), tm2]) :: r
                              end
                      else bitToBits t :: a) d
             | _ => formConcats (bitToBits t :: a) d)
       | _ => raise Fail "formConcats"

   fun mkReg (pat, ty, d) =
      let
         val (a, b) = Lib.lastButlast (formConcats [] d)
         val f = List.foldr mkConcat a b
         val a = ("x", ty)
      in
         Term.absList [a] (Term.mkMatch (Term.Var a, [(pat, f)]))
      end

   fun addRegister (name, sz, fields) =
      let
         val wty = Type.fixedTy sz
         val v = ("x", wty)
         val ty = Type.mkConstType name
         val cons = Tag.mkRecord name
         val d = List.tabulate (sz, fn i =>
                    case List.mapPartial (findField (name, i)) fields of
                      [] => U
                    | [x] => x
                    | _ => raise Fail ("register not injective: " ^ name ^
                                       ": " ^ Int.toString i))
         val un = (compact (List.mapPartial unnamed (Lib.addIndex d)),
                   Named (String.map Char.toLower name ^ "'rst"))
         val d2 = List.tabulate (sz, fn i =>
                     case List.mapPartial (findField (name, i)) [un] of
                        [x] => SOME x
                      | _ => NONE)
         val d = mergeOptionList d d2
         val named = List.mapPartial
                       (getField (name, Term.Var v, sz)) (un :: fields)
         val named = msort (String.compare o (fst3 ## fst3)) named
         val (l, r) = split named
         val tm1 = Term.absList [v] (Term.Comb (cons, ty, r))
         val tm2 = Term.absList [("_", wty), ("x", ty)]
                     (Term.Comb ("&", wty, [Term.Var ("x", ty)]))
         val pat = Term.Comb (cons, ty, List.map Term.Var l)
         val tm3 = mkReg (pat, ty, d)
         val tm4 = Term.absList [("_", ty), ("x", wty)]
                     (Term.Comb (name, ty, [Term.Var ("x", wty)]))
      in
         pr "REG" name
         ; addRecord (name, l)
         ; Consts.addDestructor (name, tm1, tm2, true)
         ; Consts.addDestructor ("&", tm3, tm4, true)
      end

   fun findBadField sz fields =
      let
         val fs = List.concat (List.map fst fields)
      in
         List.find (fn (h, l) => h < l orelse sz <= h) fs
      end

   fun register input =
      ( varorconst ++ reg ++ token (Symbol "{") ++
        puresequence field (otoken (Symbol ",")) ++ token (Symbol "}")
          >> (fn (((((loc, name), sz), _), fields), _) =>
                let
                   val () =
                      case findBadField sz fields of
                          SOME (h, l) =>
                            raise Error {loc = loc, message =  "Bad bit range.",
                                         value = SOME (Int.toString h ^ "-" ^
                                                       Int.toString l)}
                        | NONE => ()
                in
                   addRegister (name, sz, fields)
                end)
      ) input
   and reg input =
      ( annotation
          >> (fn typ =>
                  case Types.dest typ of
                    Type.FixedBits s => s
                  | _ => parseError input "bad register type")
      ) input
   and field input =
      ( bitrange ++ token (Symbol ":") ++ fname
          >> (fn ((r, _), n) => (List.rev r, n))
      ) input
   and fname input =
      ( token (Reserved "UNK!") >> (K UNK)
     || token (Reserved "RAZ!") >> (K RAZ)
     || token (Reserved "RAO!") >> (K RAO)
     || varorconst >> (Named o snd)
      ) input
   and bitrange input =
      ( puresequence range (token (Symbol ","))
      ) input
   and range input =
      ( number ++ option (token (Symbol "-") ++ (number >> snd) >> snd)
          >> (fn ((_, i), j) => (i, Option.getOpt (j, i)))
      ) input
in
   val register = register
end

(* -------------------------------------------------------------------------
   Top-level specification parser
   ------------------------------------------------------------------------- *)

local
   val print_error = ref true
   val raise_error = ref false
in
   fun printErrors NONE = !print_error
     | printErrors (SOME b) = (print_error := b; b)
   fun raiseErrors NONE = !raise_error
     | raiseErrors (SOME b) = (raise_error := b; b)
end

local
   open Type

   fun tyReset () = (Type.resetName (); Type.resetConstraint ())

   fun top (env: Env.env) input =
      if List.null (snd input)
         then env
      else let
              val (env', rest) =
                 entity env input handle Fail m => raise parseError input m
           in
              tyReset (); top env' rest
           end
   and entity (env: Env.env) input =
      ( specification env >> (K env)
     || pick
          (fn (_, Reserved "type")      => typedef          >> (K env)
            | (_, Reserved "record")    => record           >> (K env)
            | (_, Reserved "register")  => register         >> (K env)
            | (loc, Reserved "pattern") => pattern loc      >> (K env)
            | (_, Reserved "exception") => declareexception >> (K env)
            | (loc, Reserved "declare") => declaration (loc, env)
            | (_, Reserved "construct") => construct env >> (K env)
            | (_, Reserved "clear") =>
                 ( token (Reserved "pattern") ++ clearpattern >> (K ())
                || token (Reserved "patterns")
                     >> (fn _ => Patterns.resetPatterns ()) )
                     >> (K env)
            | _ => parseError input "Syntax error.")
      ) input
   and typedef input =
      ( varorconst ++ token (Symbol "=") ++ typeexpr
          >> (fn (((loc, name), _), ty) =>
                 if hasTypeVars ty
                    then raise Error
                          {loc = loc, value = SOME name,
                           message = "Type variables not permitted for type."}
                 else ( pr "TYP" name
                      ; Types.addConst (name,
                          {eq = Types.isEqType ty, def = Types.Typedef ty,
                           ast = false}
                      )))
      ) input
   and record input =
      ( varorconst ++
        token (Symbol "{") ++ arguments ++ token (Symbol "}")
          >> (fn ((((_, name), _), l), _) =>
                 (pr "REC" name; addRecord (name, l)))
      ) input
   and construct env input =
      ( varorconst ++
        token (Symbol "{") ++ oarguments ++ token (Symbol "}")
          >> (fn ((((loc, name), _), l), _) =>
                 ( pr "CON" name
                 ; Consts.buildDatatype env
                     (fn s => raise Error {loc = loc, value = SOME s,
                                           message = "Name already used."})
                     (name, l)
                 ))
      ) input
   and declaration (loc, env) input =
      ( variables
          >> (fn l =>
                 let
                    val (names, tys) = ListPair.unzip l
                    fun err s = raise Error {loc = loc, value = SOME s,
                                             message = "Name already used."}
                 in
                    checkNoFreeVars tys
                    ; Env.checkFreeList env err names
                    ; List.app (pr "VAR") names
                    ; Env.addMutableVariableList (env, l)
                 end)
      ) input
   and variables input =
      ( (varorconst >> snd) ++ annotation
          >> Lib.singleton
     || token (Symbol "{") ++ arguments ++ token (Symbol "}")
          >> (snd o fst)
      ) input
   and pattern loc input =
      ( patterns
          >> (fn l =>
                 let
                    val (names, tys) = ListPair.unzip l
                 in
                    checkNoFreeVars tys
                    ; List.all Types.isEqType tys orelse
                      raise Error {loc = loc, value = NONE,
                                   message = "Pattern variables should be in \
                                             \equality type"}
                    ; List.app (pr "PAT") names
                    ; Patterns.addPatternList l
                 end)
      ) input
   and clearpattern input =
      ( puresequence (varorconst >> snd) (token (Symbol ","))
          >> Patterns.removePatternList
      ) input
   and patterns input =
      ( apattern
          >> (List.concat o Lib.singleton)
     || token (Symbol "{") ++ puresequence apattern (otoken (Symbol ",")) ++
        token (Symbol "}")
          >> (List.concat o snd o fst)
      ) input
   and apattern input =
      ( puresequence (varorconst >> snd) (otoken (Symbol ",")) ++ annotation
          >> (fn (vs, a) => mapl a vs)
      ) input
   and declareexception input =
      ( varorconst ++ oannotation
          >> (fn ((_, v), ty) => (pr "EXC" v; Consts.addException (v, ty)))
      ) input
   and arguments input =
      ( puresequence ((varorconst >> snd) ++ annotation) (otoken (Symbol ","))
      ) input
   and oarguments input =
      ( puresequence ((varorconst >> snd) ++ oannotation) (otoken (Symbol ","))
      ) input

   fun saveState () =
      ( Types.saveConsts ()
      ; Consts.saveConsts ()
      ; Patterns.savePatterns ()
      ; ParseToken.clearHighestError ()
      ; Lex.UserDeclarations.linenum := 1
      ; Env.save ()
      )

   fun undo () =
      ( Types.restoreConsts ()
      ; Types.updateCastTypes ()
      ; Consts.restoreConsts ()
      ; Patterns.restorePatterns ()
      ; Env.restore ()
      )

   local
      fun repeatChar c i = String.implode (List.tabulate (i, K c))
      val spaces = repeatChar #" "
   in
      val line = "\n" ^ repeatChar #"~" 74 ^ "\n"
      fun printi i s = printn (spaces i ^ s)
      fun is_or_are l = (if List.length l = 1 then " is" else "s are") ^ ":\n"
   end

   fun printError exc =
      case exc of
         ParseToken.NoParse {loc, message, tokens} =>
           let
              val pos = case loc of
                           Loc (n, _) => "line " ^ Int.toString n
                         | LastLine => "end-of-file"
           in
              printn (line ^
                      "\n  Parse error located from " ^ pos ^ ".\n\n    " ^
                      Lib.quote message)
              ; if List.null tokens
                   then ()
                else ( printn "\n  Token sequence is:\n"
                     ; List.app (printi 4 o PolyML.makestring o snd) tokens
                     ; printn "    ...")
              ; printn line
           end
       | Error {loc, message, value} =>
           ( printn (line ^ "\n  Error at (or somewhere after) line " ^
                     Int.toString loc ^ ".\n\n    " ^ Lib.quote message)
           ; (case value of
                 NONE => ()
               | SOME v => ( printn ""
                           ; printi 2 "Instance:\n"
                           ; printi 4 (PolyML.makestring v))
                           )
           ; printn line
           )
       | Term.TypeCheck {loc, message, operation, valid_types, args} =>
           ( printn (line ^ "\n  Type error detected at line " ^
                     Int.toString loc ^ ".\n\n    " ^ Lib.quote message)
           ; (if operation = "" then ()
              else ( printn ("\n  Checking operation:\n")
                   ; printi 4 (quote operation)
                   ))
           ; if List.null args
                then ()
             else ( printn ("\n  Argument" ^ is_or_are args)
                  ; List.app (printi 4 o PolyML.makestring) args
                  )
           ; if List.null valid_types
                then ()
             else ( printn ("\n  Valid type" ^ is_or_are valid_types)
                  ; List.app (printi 4 o PolyML.makestring) valid_types
                  )
           ; printn line
           )
       | Fail m => ( printn (line ^ "\n  Error.\n\n")
                   ; printi 4 (quote m ^ "\n" ^ line)
                   )
       | _ => ()

   fun processError exc =
      let
         val exc = case exc of ParseToken.NoParse e => HighestError e | _ => exc
      in
         if printErrors NONE then printError exc else ()
         ; raise exc
      end

   fun addSpec f s =
      let
         val () = saveState ()
         val () = Lex.UserDeclarations.comment_depth := 0
         val input = f s
      in
         (* pv "Parsing..."; *)
         Env.update (top (Env.get ()) ((0, NONE), input)); true
      end
      handle exc =>
         ( undo ()
         ; tyReset ()
         ; (processError exc
            handle e as IO.Io _ => raise e
                 | e => if raiseErrors NONE then raise e else false)
         )

in
   fun reset () =
      ( Consts.resetConsts ()
      ; Consts.resetAST ()
      ; Types.resetConsts ()
      ; Types.updateCastTypes ()
      ; Patterns.resetPatterns ()
      ; Env.reset ())

   fun show () =
      (Env.listVariables (Env.get ()),
       Patterns.listPatterns (),
       Types.listConsts (),
       Consts.listConsts ())

   fun addVar (s, ty) = Env.update (Env.addMutableVariable (Env.get (), s, ty))

   val buildDatatype =
      Consts.buildDatatype (Env.get ())
        (fn s => raise Fail ("Name already used: " ^ s))

   val save = saveState
   val undo = undo

   fun statementQ e =
     (( tyReset ()
      ; ParseToken.clearHighestError ()
      ; Lex.UserDeclarations.linenum := 1
      ; e)
      |> tryParseQ
           ( definition ++ finished
          || (expression
                >> (fn {exp, loc} => {loc = loc, stmt = Expression exp})) ++
             finished )
      |> (snd o buildStatement Term.NoTypeHint (Env.get ()) o fst o fst)
      |> (fn t => let val t = castsAndMatches t in validateStatement t; t end))
     handle e => processError e

   val load = General.ignore o addSpec lex
   val loadQ = General.ignore o addSpec lexQ

   fun loadF s =
      let
         val sep =
            fn #"," => true
             | #" " => true
             | #"\t" => true
             | _ => false
      in
         List.all (fn f =>
                      let
                         val cdir = OS.FileSys.getDir ()
                         val {file, dir} =
                            OS.Path.splitDirFile (OS.FileSys.fullPath f)
                      in
                         pv ("Loading... " ^ f)
                       ; OS.FileSys.chDir dir
                       ; addSpec lexF file before OS.FileSys.chDir cdir
                      end)
                  (String.tokens sep s)
         ; pv "Done."
      end

   fun spec s = (load s; show ())
   fun specQ q = (loadQ q; show ())
   fun specF q = (loadF q; show ())
end

end (* struct Parser *)

(* ------------------------------------------------------------------------- *)

signature Runtime =
sig
   val LoadF: string -> unit
   val LoadQ: string frag list -> unit
   val evalQ: string frag list -> Term.term
   val evalT: Term.term -> Term.term
   val loadF: string -> unit
   val loadQ: string frag list -> unit
   val reset: unit -> unit
   val resetAll: unit -> unit
   val show: unit -> Eval.term_stack
   val undo : unit -> unit
end

structure Runtime :> Runtime =
struct

open Eval

val env = ref (Stack.empty : Eval.term_stack)

fun reset () =
   env := (Env.listVariables (Env.get ())
            |> List.mapPartial
                  (fn (v, {typ, mutable = true}) =>
                         SOME (v, snd (Eval.eval Stack.empty (initialize typ)))
                    | _ => NONE)
            |> Stack.buildStack)

fun resetAll () = (Parser.reset (); reset ())

fun loadF q = (Parser.loadF q; reset ())
fun loadQ q = (Parser.loadQ q; reset ())

fun LoadF q = (Parser.reset (); Parser.loadF q; reset ())
fun LoadQ q = (Parser.reset (); Parser.loadQ q; reset ())

fun undo () = (Parser.undo (); reset ())

fun evalT t =
   let
      val (env', res) = eval (!env) t
      val _ = env := env'
   in
      res
   end

val evalQ = evalT o Parser.statementQ

fun show () = (!env)

end (* struct Runtime *)

val ld = Runtime.LoadF
val dc = Runtime.loadQ

(* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-==-=-=-=-=-=-=-=-=-==-=-=-=-=-=-=-=-=-= *)
