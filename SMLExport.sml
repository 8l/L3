(*
use "Export.sml";
*)

(* ------------------------------------------------------------------------
   Export L3 specifications to Standard ML
   ------------------------------------------------------------------------ *)

signature SMLExport =
sig
   val setFunctor: bool -> unit
   val spec: string * string -> unit
   val export: string -> unit
end

structure SMLExport :> SMLExport =
struct

local
   val reserved =
     Stringset.fromList
     ["abstype", "and", "andalso", "as", "case", "datatype", "do", "else",
      "end", "eqtype", "exception", "fn", "fun", "functor", "handle", "if",
      "in", "include", "infix", "infixr", "let", "local", "nonfix", "o",
      "of", "op", "open", "orelse", "raise", "rec", "sharing", "sig",
      "signature", "struct", "structure", "then", "type", "val", "where",
      "with", "withtype", "while"]
   fun rename checkCons s =
      if checkCons andalso Consts.isConstructor s orelse
         Stringset.member (reserved, s)
         then s ^ "'"
      else String.translate (fn #"@" => "''" (* polymorphic AST entries *)
                              | #"#" => "'"  (* exceptions *)
                              | c => String.str c) s
in
   val renameConsReserved = rename true
   val renameReserved = rename false
end

open PP

val ppR = ppS o renameConsReserved

fun mapSizeFn ((dty, _): Type.ty) =
   case dty of
      Type.ConstType "nat" => (~1, "")
    | Type.ConstType "bool" => (2, "IntExtra.fromBool")
    | Type.ConstType "char" => (256, "Char.ord")
    | Type.ConstType s =>
        (case Types.lookupConst s of
            SOME {def = Types.Constructors (Types.Enum d), ...} =>
               (Stringmap.numItems d, "Cast." ^ s ^ "ToNat")
          | _ => (0, ""))
    | Type.BV i => (IntInf.<< (1, Word.fromInt i), "BitsN.toNat")
    | _ => (0, "")

val mapSize = fst o mapSizeFn o Types.expand

fun hasMap ((bty, c): Type.ty) =
   let
      open Type
      fun hasM t =
         case t of
             Prod (t1, t2) => hasM t1 orelse hasM t2
           | Arrow (t1, t2) =>
               mapSize (t1, c) <> 0 orelse hasM t1 orelse hasM t2
           | ParamType (_, t) => hasM t
           | ConstType s =>
               (case Types.lookupConst s of
                   SOME {def = Types.Typedef (t, _), ...} => hasM t
                 | SOME {def = Types.Constructors (Types.Construct d), ...} =>
                     Stringmap.exists (fn SOME (t, _) => hasM t | _ => false) d
                 | SOME {def = Types.Record l, ...} =>
                     List.exists (hasM o fst o snd) l
                 | _ => false)
           | _ => false
   in
      hasM bty
   end

fun isMap (ty as (_, c): Type.ty) =
   case fst (Types.expand ty) of
      Type.Arrow (t1, t2) => mapSize (t1, c) <> 0 andalso not (hasMap (t2, c))
    | _ => false

local
   open Type
   val param =
      fn ListTy => "list"
       | OptionTy => "option"
       | SetTy => "list"
   fun pp dty =
      case dty of
         VarType s            => ppS ("'" ^ s)
       | ConstType "unit"     => ppS "unit"
       | ConstType "int"      => ppS "int"
       | ConstType "nat"      => ppS "Nat.nat"
       | ConstType "bool"     => ppS "bool"
       | ConstType "char"     => ppS "char"
       | ConstType "rounding" => ppS "IEEEReal.rounding_mode"
       | ConstType s          => ppS s
       | BV _                 => ppS "BitsN.nbit"
       | BVV _                => ppS "BitsN.nbit"
       | Prod (a, b)  => ppInfix (pp a, " *", pp b)
       | Arrow (a, b) =>
            if mapSize (a, Constrain.empty) = 0
               then ppInfix (pp a, " ->", pp b)
            else ppL (0, [ppBracket (pp b), ppB (1, 0), ppS "Map.map"])
       | ParamType (ListTy, ConstType "char") => ppS "string"
       | ParamType (p, t) =>
            ppL (0, [ppBracket (pp t), ppB (1, 0), ppS (param p)])
in
   fun ppType ty = pp (fst (Types.expand ty))
end

local
    fun ppTypeDecl b (name, p) =
       let
          val (s, n) = if b then ("datatype ", 2) else ("type ", 0)
       in
          SOME (PolyML.PrettyBlock
                  (2, false, [], [ppS (s ^ name ^ " ="), ppB (1, n), p]))
       end
   fun ppRec (n, t) = ppL (1, [ppS (n ^ ":"), ppB (1, 3), ppType t])
   fun ppCons first =
      let
         fun f n = ppS ((if first then "" else "| ") ^ renameReserved n)
      in
         fn (n, SOME ty) =>
              ppL (4, [f n, ppS " of", ppB (1, 0), ppType ty])
          | (n, NONE) => f n
      end
   fun ppTypeDefArg (name, d) =
      case d of
        Types.Constructors (Types.Enum m) =>
          let
             val l =
                m |> Stringmap.listItems
                  |> msort (Int.compare o (snd ## snd))
                  |> (fn (h, _) :: t =>
                         ppS h :: List.map (fn (s, _) => ppS ("| " ^ s)) t
                       | [] => raise Fail "ppTypeDefArg: empty")
                  |> mapSeparate I [ppB (1, 0)]
          in
             ppTypeDecl true (name, PolyML.PrettyBlock (0, false, [], l))
          end
      | Types.Constructors (Types.Construct m) =>
          let
             val l = m |> Stringmap.listItems
                       |> (fn h :: t =>
                               ppCons true h :: List.map (ppCons false) t
                            | [] => raise Fail "ppTypeDefArg: empty")
          in
             ppTypeDecl true (name, ppBL (0, 0, l))
          end
      | Types.Record l =>
          let
             val l = [ppS "{", ppB (1, 1)] @
                     mapSeparate I [ppS ",", ppB (1, 0)] (List.map ppRec l) @
                     [ppB (1, 0), ppS "}"]
          in
             ppTypeDecl false (name, ppL (2, l))
          end
      | _ => NONE
   fun ppTypeDef (name, d: Types.typeconst) = ppTypeDefArg (name, #def d)
in
   fun ppTypeDefs () = List.mapPartial ppTypeDef (Types.listConsts ())
end

(* - printing of enumated type maps and record update functions ----------- *)

local
   fun ppLine c b start x =
      ppS ((if start then "  " else "| ") ^ c x ^ " => " ^ b x)
   fun ppEnum (f, g, c, b, d) (name, []) = raise Fail "ppEnum: empty"
     | ppEnum (f, g, c, b, d) (name, h :: t) =
      PolyML.PrettyBlock (0, true, [],
         [ppS ("fun " ^ f name ^ " x ="), ppB (1, 2),
          ppS ("case " ^ g ^ "x of"), ppB (1, 3),
          PolyML.PrettyBlock (3, true, [],
             mapSeparate I [ppB (1, 0)]
               (ppLine c b true h :: List.map (ppLine c b false) t @
                (if d then [ppS ("| _ => raise Fail \"" ^ f name ^ "\"")]
                 else [])))])
   val ppNatTo =
      ppEnum
         (fn s => "natTo" ^ s, "Nat.toInt ", Int.toString o snd, fst, true)
   val ppToNat =
      ppEnum (fn s => s ^ "ToNat", "", fst, Int.toString o snd, false)
   fun ppToString x =
      ppEnum (fn s => s ^ "ToString", "", fst, quote o fst, false) x
   fun ppStringTo x =
      ppEnum (fn s => "stringTo" ^ s, "", quote o fst, fst, true) x
   val items = Lib.msort (fn ((_, x), (_, y)) => Int.compare (x, y)) o
               Stringmap.listItems
in
   fun ppTypeCasts () =
      let
         val l =
            List.mapPartial
              (fn (name, {def = Types.Constructors (Types.Enum m), ...}) =>
                 SOME (name, items m)
                | _ => NONE) (Types.listConsts ())
      in
         if List.null l
            then []
         else [PolyML.PrettyBlock (0, true, [],
                 [ppS "structure Cast =", ppB (1, 0), ppS "struct",
                  ppB (1, 0)] @
                 mapSeparate I [ppS "\n\n"]
                    (List.map ppNatTo l @ List.map ppToNat l @
                     List.map ppToString l @ List.map ppStringTo l) @
                 [ppB (1, 0), ppS "end"])]
      end
   fun ppTypeCastsSig () =
      let
         val l =
            List.mapPartial
              (fn (name, {def = Types.Constructors (Types.Enum _), ...}) =>
                 SOME name
                | _ => NONE) (Types.listConsts ())
      in
         if List.null l
            then []
         else [PolyML.PrettyBlock (0, true, [],
                 [ppS "structure Cast:", ppB (1, 0), ppS "sig",
                  ppB (1, 0)] @
                 List.concat
                    (List.map (fn s =>
                       [
                        ppS ("\nval natTo" ^ s ^ ":"),
                        ppS ("Nat.nat -> " ^ s),
                        ppS ("\nval " ^ s ^ "ToNat:"),
                        ppS (s ^ "-> Nat.nat"),
                        ppS ("\nval stringTo" ^ s ^ ":"),
                        ppS ("string -> " ^ s),
                        ppS ("\nval " ^ s ^ "ToString:"),
                        ppS (s ^ "-> string")
                       ]) l) @
                 [ppB (1, 0), ppS "\nend\n"])]
      end
end

local
   fun ppUpdate f =
      List.map (fn fld => ppL (2, [ppS fld, ppS " =", ppB (1, 0),
                                   ppS (if f = fld then "x'" else fld)]))
   val ppRec = ppParen ("{", [ppS ",", ppB (1, 0)], "}")
   fun ppRecordUpdateFun (name, l) =
      let
         val p = ppRec (List.map ppS l)
      in
         List.map (fn fld =>
           PolyML.PrettyBlock (2, false, [],
              [ppS ("fun " ^ name ^ "_" ^ fld ^ "_rupd ("), p, ppB (0, 0),
               ppS (": " ^ name ^ ", x') ="),
               ppB (1, 0), ppRec (ppUpdate fld l), ppB (0,0),
               ppS (": " ^ name)])) l
      end
   fun ppRecordUpdateFunSig (name, l) =
      List.map (fn (fld, ty) =>
        PolyML.PrettyBlock (2, false, [],
           [ppS ("val " ^ name ^ "_" ^ fld ^ "_rupd:"), ppB (1, 0),
            PolyML.PrettyBlock (0, false, [],
               [ppS name, ppB (1, 0), ppS "*", ppB (1, 0),
                ppBracket (ppType ty), ppB (1, 0), ppS "->", ppB (1, 0),
                ppS name])])) l
   fun recordUpdateFuns () =
      List.mapPartial
         (fn (name, {def = Types.Record l, ...}) => SOME (name, l)
           | _ => NONE) (Types.listConsts ())
in
   fun ppRecordUpdateFuns () =
      let
         val l = List.map (I ## List.map fst) (recordUpdateFuns ())
      in
         if List.null l then [] else List.concat (List.map ppRecordUpdateFun l)
      end
   fun ppRecordUpdateFunsSig () =
      let
         val l = recordUpdateFuns ()
      in
         if List.null l
            then []
         else List.concat (List.map ppRecordUpdateFunSig l)
      end
end

(* - printing of exceptions -------------------------------------------- *)

local
   fun ppExc (s, oty) =
      case oty of
         NONE => ppBL (0, 2, [ppS "exception", ppS s])
       | SOME ty => ppL (0, [ppS "exception", ppB (1, 2), ppS s, ppS " of",
                             ppB (1, 2), ppType ty])
in
   val ppExceptions = List.map ppExc o Consts.listExceptions
end

(* - printing of L3 expressions and statements ------------------------- *)

val convertRounding =
   fn "roundTiesToEven" => "IEEEReal.TO_NEAREST"
    | "roundTowardNegative" => "IEEEReal.TO_NEGINF"
    | "roundTowardPositive" => "IEEEReal.TO_POSINF"
    | "roundTowardZero" => "IEEEReal.TO_ZERO"
    | s => s

val ppLiteral =
   fn Term.Bits w =>
       let
          val sz = Nat.toInt (BitsN.size w)
       in
          if sz < 1 then raise Fail "ppLiteral: bits width < 1"
          else ppAppPair ("BitsN.B", ppS ("0x" ^ BitsN.toHexString w),
                          ppS (Int.toString sz))
       end
    | Term.Bitstring s => PolyML.prettyRepresentation (s, 1000000)
    | Term.Bool true => ppS "true"
    | Term.Bool false => ppS "false"
    | Term.Char c => ppS ("#" ^ quote (Char.toString c))
    | Term.Enum (n, s) =>
       (ppS (convertRounding (Option.valOf (Types.revenum s n)))
        handle Option =>
            raise Fail ("ppLiteral: Enum (" ^ Nat.toString n ^ ", " ^ s))
    | Term.Int i => ppS (Int.toString i)
    | Term.Nat n => if n < 0 then raise Fail "ppLiteral: negative nat"
                    else ppS (Nat.toString n)
    | Term.Other (s, ty) =>
        (case fst (Types.expand ty) of
            Type.BVV n =>
               let
                  val v =
                     Int.toHexString (Option.valOf (Int.fromLit (Tag.remove s)))
               in
                  ppAppPair ("BitsN.B", ppS ("0x" ^ v), ppS n)
               end
          | _ => (case s of
                     "{}" => ppS "[]"
                   | "Nil" => ppS (if Types.equalTy Type.stringTy ty
                                      then "\"\""
                                   else "[]")
                   | "None" => ppS "NONE"
                   | _ => ppS s))
    | Term.String s => ppQ s
    | Term.Unit => ppS "()"

fun lookupOperation s =
   case Consts.lookupConst s of
      Consts.Definition (_, _, ~1) => Consts.Primitive []
    | c as Consts.Constructor _ =>
        if s = "Some" then Consts.Primitive [] else c
    | c => c

val mopChar =
   Stringset.fromList
     ["IsAlpha", "IsAlphaNum", "IsDigit", "IsHexDigit", "IsLower", "IsSpace",
      "IsUpper"]

fun pick (x as (a, b, c)) ty =
   let
      val is = Types.equalTy ty
   in
      Option.valOf
        (if Option.isSome a andalso Type.isWordTy ty
            then a
         else if Option.isSome b andalso is Type.natTy
            then b
         else if Option.isSome c andalso is Type.intTy
            then c
         else raise Fail "pick")
   end

fun pickTy pty (a: string) b ty = if Types.equalTy pty ty then a else b

val bvShift       = pickTy Type.natTy "" "^"
val pickBitstring = pickTy Type.bitstringTy
val pickString    = pickTy Type.stringTy

fun bvSizeString ty =
   case ty of
      (Type.BV i, _) => Int.toString i
    | (Type.BVV n, _) => n
    | _ => raise Fail "bvSizeString"

val sTy = Type.sndTy o Types.expand

fun ppMop (f, ty, tty) =
   case f of
      "-"          => pick (SOME "BitsN.neg", NONE, SOME "Int.~") ty
    | "~"          => "BitsN.~"
    | "Abs"        => pick (SOME "BitsN.abs", NONE, SOME "Int.abs") ty
    | "Concat"     => pickString "String.concat" "List.concat" tty
    | "PadLeft"    => pickString "L3.padLeftString" "L3.padLeft" tty
    | "PadRight"   => pickString "L3.padRightString" "L3.padRight" tty
    | "FP32_Abs"   => "(fn _ => raise Fail \"FP32_Abs\")"
    | "FP32_Add"   => "(fn _ => raise Fail \"FP32_Add\")"
    | "FP32_Equal" => "(fn _ => raise Fail \"FP32_Equal\")"
    | "FP32_IsNaN" => "(fn _ => raise Fail \"FP32_IsNan\")"
    | "FP32_Mul"   => "(fn _ => raise Fail \"FP32_Mul\")"
    | "FP32_Neg"   => "(fn _ => raise Fail \"FP32_Neg\")"
    | "FP32_Sub"   => "(fn _ => raise Fail \"FP32_Sub\")"
    | "FP32_LessThan" => "(fn _ => raise Fail \"FP32_LessThan\")"
    | "FP64_Abs"   => "FP64.abs"
    | "FP64_Add"   => "FP64.add"
    | "FP64_Equal" => "FP64.equal"
    | "FP64_IsNaN" => "FP64.isNan"
    | "FP64_Mul"   => "FP64.mul"
    | "FP64_Neg"   => "FP64.neg"
    | "FP64_Sub"   => "FP64.sub"
    | "FP64_LessThan" => "FP64.lessThan"
    | "Fst"        => "L3.fst"
    | "FromBinString" => "Nat.fromBinString"
    | "FromDecString" => "Nat.fromString"
    | "FromHexString" => "Nat.fromHexString"
    | "Head"       => pickString "L3.strHd" "List.hd" ty
    | "IsSome"     => "Option.isSome"
    | "Length"     => pickString "String.size" "List.length" ty
    | "Log2"       => pick (SOME "BitsN.log2", SOME "Nat.log2", NONE) ty
    | "Max"        => pick (SOME "BitsN.max", SOME "Nat.max", SOME "Int.max")
                           (Type.fstTy ty)
    | "Min"        => pick (SOME "BitsN.min", SOME "Nat.min", SOME "Int.min")
                           (Type.fstTy ty)
    | "Msb"        => "BitsN.msb"
    | "QuotRem"    => "IntInf.quotRem"
    | "Reverse"    => if Type.isWordTy ty then "BitsN.reverse"
                      else pickString "L3.revString" "List.rev" ty
    | "RemoveDuplicates" => pickString "L3.removeDuplicatesString" "Set.mk" tty
    | "SetOfList"  => "Set.mk"
    | "SignExtend" => "BitsN.signExtend " ^ bvSizeString tty
    | "SignedMax"  => "BitsN.smax"
    | "SignedMin"  => "BitsN.smin"
    | "Size"       => "BitsN.size"
    | "Snd"        => "L3.snd"
    | "Some"       => "Option.SOME"
    | "Tail"       => pickString "L3.strTl" "List.tl" ty
    | "ToLower"    => "L3.lowercase"
    | "ToUpper"    => "L3.uppercase"
    | "ValOf"      => "Option.valOf"
    | "ZeroExtend" => "BitsN.zeroExtend " ^ bvSizeString tty
    | "not"        => "not"
    | "Difference" => "Set.diff"
    | "Union"      => "Set.union"
    | "Intersect"  => "Set.intersect"
    | "IsSubset"   => "Set.isSubset"
    | "IsMember"   => pickString "L3.memString" "Set.mem" (sTy ty)
    | "Cardinality"=> "List.length"
    | "RemoveExcept" => pickString "L3.removeExceptString" "Set.intersect" tty
    | "Take"       => pickString "L3.takeString" "L3.take" tty
    | "Drop"       => pickString "L3.dropString" "L3.drop" tty
    | "Update"     => pickString "L3.stringUpdate" "L3.listUpdate" tty
    | "Remove"     => pickString "L3.removeString" "L3.remove" tty
    | "Element"    => pickString "(String.sub o L3.swap)" "L3.element" (sTy ty)
    | "IndexOf"    => pickString "L3.indexOfString" "L3.indexOf" (sTy ty)
    | _ => if Stringset.member (mopChar, f)
              then "Char.i" ^ String.extract (f, 1, NONE)
           else raise Fail ("ppMop: " ^ f)

fun ppBop (f, ty1, ty2) =
   case f of
      ">>"   => "BitsN.>>" ^ bvShift ty2
    | "#<<"  => "BitsN.#<<" ^ bvShift ty2
    | "#>>"  => pickBitstring "Bitstring.#>>" ("BitsN.#>>" ^ bvShift ty2) ty1
    | ">>+"  => pickBitstring "Bitstring.>>+" ("BitsN.>>+" ^ bvShift ty2) ty1
    | "<<"   => pickBitstring "Bitstring.<<" ("BitsN.<<" ^ bvShift ty2) ty1
    | "&&"   => pickBitstring "Bitstring.&&" "BitsN.&&" ty1
    | "||"   => pickBitstring "Bitstring.||" "BitsN.||" ty1
    | "??"   => pickBitstring "Bitstring.??" "BitsN.??" ty1
    | "+"    => if Types.equalTy Type.bitstringTy ty1
                   then "Bitstring.+"
                else pick (SOME "BitsN.+", SOME "Nat.+", SOME "Int.+") ty1
    | "-"    => pick (SOME "BitsN.-", SOME "Nat.-", SOME "Int.-") ty1
    | "*"    => pick (SOME "BitsN.*", SOME "Nat.*", SOME "Int.*") ty1
    | "**"   => pick (NONE, SOME "Nat.pow", SOME "IntInf.pow") ty1
    | "<+"   => "BitsN.<+"
    | "<=+"  => "BitsN.<=+"
    | ">+"   => "BitsN.>+"
    | ">=+"  => "BitsN.>=+"
    | "<"    => pick (SOME "BitsN.<", SOME "Nat.<", SOME "Int.<") ty1
    | "<="   => pick (SOME "BitsN.<=", SOME "Nat.<=", SOME "Int.<=") ty1
    | ">"    => pick (SOME "BitsN.>", SOME "Nat.>", SOME "Int.>") ty1
    | ">="   => pick (SOME "BitsN.>=", SOME "Nat.>=", SOME "Int.>=") ty1
    | "<.>"  => pickBitstring "Bitstring.bit" "BitsN.bit" ty1
    | "in"     => "Set.mem"
    | "insert" => "Set.insert"
    | "bit-modify" => "BitsN.modify"
    | "div"  => pick (SOME "BitsN.div", SOME "Nat.div", SOME "Int.div") ty1
    | "mod"  => pick (SOME "BitsN.mod", SOME "Nat.mod", SOME "Int.mod") ty1
    | "quot" => pick (SOME "BitsN.quot", NONE, SOME "Int.quot") ty1
    | "rem"  => pick (SOME "BitsN.rem", NONE, SOME "Int.rem") ty1
    | "splitl" => "L3.splitl"
    | "splitr" => "L3.splitr"
    | "fields" => "L3.uncurry String.fields"
    | "tokens" => "L3.uncurry String.tokens"
    | f => raise Fail ("ppBop: " ^ f)

val listOfList =
   let
      fun iter a =
         fn tm as Term.Comb ("Cons", _, [t]) =>
              (case Lib.total Term.destPair t of
                  SOME (l, r) => iter (l::a) r
                | NONE => (a, SOME tm))
          | Term.Lit (Term.Other ("Nil", _)) => (a, NONE)
          | tm => (a, SOME tm)
   in
      (List.rev ## I) o iter []
   end

fun stringOfList [] = NONE
  | stringOfList l = SOME (String.implode (List.map Term.destCharLit l))
                     handle Fail _ => NONE

fun mkNatFromInt i = Int.toString i

datatype cast =
     Cast0
   | Cast1 of string
   | Cast2 of string * string
   | Cast3 of string * string * string

fun pickCast (ty1, ty2) =
   case (Types.dest ty1, Types.dest ty2) of
      (Type.Other "bool", Type.Other "bool") => Cast0
    | (Type.Other "char", Type.Other "char") => Cast0
    | (Type.Other "nat",  Type.Other "nat") => Cast0
    | (Type.Other "int",  Type.Other "int") => Cast0
    | (Type.Other "string", Type.Other "string") => Cast0
    | (Type.Other "bitstring", Type.Other "bitstring") => Cast0
    | (Type.Other "bool", Type.Other "char") =>
         Cast1 "(fn true => #\"t\" | false => #\"f\")"
    | (Type.Other "bool", Type.Other "string") =>
         Cast1 "(fn true => \"true\" | false => \"false\")"
    | (Type.Other "bool", Type.Other "nat") => Cast1 "Nat.fromBool"
    | (Type.Other "bool", Type.Other "int") => Cast1 "IntExtra.fromBool"
    | (Type.Other "bool", Type.Other "bitstring") => Cast1 "Bitstring.fromBool"
    | (Type.Other "bool", Type.FixedBits 1) => Cast1 "BitsN.fromBit"
    | (Type.Other "bool", Type.FixedBits i) =>
         Cast1 ("BitsN.fromBool " ^ mkNatFromInt i)
    | (Type.Other "bool", Type.VarBits (N, _)) => Cast1 ("BitsN.fromBool " ^ N)
    | (Type.Other "nat", Type.Other "bool") => Cast1 "(not o L3.equal Nat.zero)"
    | (Type.Other "nat", Type.Other "char") => Cast1 "Char.chr"
    | (Type.Other "nat", Type.Other "string") => Cast1 "Nat.toString"
    | (Type.Other "nat", Type.Other "int") => Cast1 "Nat.toInt"
    | (Type.Other "nat", Type.Other "bitstring") => Cast1 "Bitstring.fromNat"
    | (Type.Other "nat", Type.Other s) =>
         if Types.isEnumerated s
            then Cast1 ("Cast.natTo" ^ s)
         else raise Fail ("nat -> " ^ s)
    | (Type.Other "nat", Type.FixedBits i) =>
         Cast2 ("BitsN.fromNat", mkNatFromInt i)
    | (Type.Other "nat", Type.VarBits (N, _)) => Cast2 ("BitsN.fromNat", N)
    | (Type.Other "int", Type.Other "bool") => Cast1 "(not o L3.equal 0)"
    | (Type.Other "int", Type.Other "char") => Cast1 "Char.chr"
    | (Type.Other "int", Type.Other "string") => Cast1 "Int.toString"
    | (Type.Other "int", Type.Other "nat") => Cast1 "Nat.fromInt"
    | (Type.Other "int", Type.Other "bitstring") => Cast1 "Bitstring.fromInt"
    | (Type.Other "int", Type.Other s) =>
         if Types.isEnumerated s
            then Cast1 ("Cast.natTo" ^ s)
         else raise Fail ("int -> " ^ s)
    | (Type.Other "int", Type.FixedBits i) =>
         Cast2 ("BitsN.fromInt", mkNatFromInt i)
    | (Type.Other "int", Type.VarBits (N, _)) => Cast2 ("BitsN.fromInt", N)
    | (Type.Other "bitstring", Type.Other "bool") =>
         Cast1 "(not o L3.equal 0 o Bitstring.toInt)"
    | (Type.Other "bitstring", Type.Other "char") =>
         Cast1 "(Char.chr o Bitstring.toNat)"
    | (Type.Other "bitstring", Type.Other "string") =>
         Cast1 "Bitstring.toBinString"
    | (Type.Other "bitstring", Type.Other "nat") => Cast1 "Bitstring.toNat"
    | (Type.Other "bitstring", Type.Other "int") => Cast1 "Bitstring.toInt"
    | (Type.Other "bitstring", Type.Other s) =>
         if Types.isEnumerated s
            then Cast1 ("(Cast.natTo" ^ s ^ " o Bitstring.toNat)")
         else raise Fail ("bitstring -> " ^ s)
    | (Type.Other "bitstring", Type.FixedBits i) =>
         Cast2 ("BitsN.fromBitstring", mkNatFromInt i)
    | (Type.Other "bitstring", Type.VarBits (N, _)) =>
         Cast2 ("BitsN.fromBitstring", N)
    | (Type.Other "char", Type.Other "bool") => Cast1 "L3.equal #\"t\""
    | (Type.Other "char", Type.Other "string") => Cast1 "String.str"
    | (Type.Other "char", Type.Other "nat") => Cast1 "Char.ord"
    | (Type.Other "char", Type.Other "int") => Cast1 "Char.ord"
    | (Type.Other "char", Type.Other "bitstring") =>
         Cast1 "(Bitstring.fromNat o Char.ord)"
    | (Type.Other "char", Type.Other s) =>
         if Types.isEnumerated s
            then Cast1 ("(Cast.natTo" ^ s ^ " o Char.ord)")
         else raise Fail ("nat -> " ^ s)
    | (Type.Other "char", Type.FixedBits i) =>
         Cast3 ("BitsN.fromNat", "Char.ord", mkNatFromInt i)
    | (Type.Other "string", Type.Other "bool") =>
         Cast1 "(fn \"true\" => true | \"false\" => false | _ => raise Domain)"
    | (Type.Other "string", Type.Other "char") => Cast1 "L3.stringToChar"
    | (Type.Other "string", Type.Other "int") => Cast1 "IntExtra.fromString"
    | (Type.Other "string", Type.Other "nat") => Cast1 "Nat.fromString"
    | (Type.Other "string", Type.Other "bitstring") =>
         Cast1 "Bitstring.fromBinString"
    | (Type.Other "string", Type.Other s) =>
         if Types.isEnumerated s
            then Cast1 ("Cast.stringTo" ^ s)
         else raise Fail ("string -> " ^ s)
    | (Type.Other "string", Type.FixedBits i) =>
         Cast2 ("(Option.valOf o BitsN.fromHexString)", mkNatFromInt i)
    | (Type.Other "string", Type.VarBits (N, _)) =>
         Cast2 ("(Option.valOf o BitsN.fromHexString)", N)
    | (Type.Other s, Type.Other "char") =>
         if Types.isEnumerated s
            then Cast1 ("(Char.chr o Cast." ^ s ^ "ToNat)")
         else raise Fail (s ^ " -> nat")
    | (Type.Other s, Type.Other "string") =>
         if Types.isEnumerated s
            then Cast1 ("Cast." ^ s ^ "ToString")
         else raise Fail (s ^ " -> string")
    | (Type.Other s, Type.Other "nat") =>
         if Types.isEnumerated s
            then Cast1 ("Cast." ^ s ^ "ToNat")
         else raise Fail (s ^ " -> nat")
    | (Type.Other s, Type.Other "int") =>
         if Types.isEnumerated s
            then Cast1 ("Cast." ^ s ^ "ToNat")
         else raise Fail (s ^ " -> int")
    | (Type.Other s, Type.Other "bitstring") =>
         if Types.isEnumerated s
            then Cast1 ("(Bitstring.fromNat o Cast." ^ s ^ "ToNat)")
         else raise Fail (s ^ " -> bitstring")
    | (Type.Other s, Type.FixedBits i) =>
         if Types.isEnumerated s
            then Cast3 ("BitsN.fromNat", "Cast." ^ s ^ "ToNat", mkNatFromInt i)
         else raise Fail (s ^ " -> bits(" ^ Int.toString i ^ ")")
    | (Type.Other s, Type.VarBits (N, _)) =>
         if Types.isEnumerated s
            then Cast3 ("BitsN.fromNat", "Cast." ^ s ^ "ToNat", N)
         else raise Fail (s ^ " -> bits(" ^ N ^ ")")
    | (Type.Other s1, Type.Other s2) =>
         if Types.isEnumerated s1 andalso Types.isEnumerated s2
            then Cast1 ("(Cast.natTo" ^ s2 ^ " o " ^ "Cast." ^ s1 ^ "ToNat)")
         else if s1 = s2
            then Cast0
         else raise Fail (s1 ^ " -> " ^ s2)
    | (Type.FixedBits i, Type.Other "bool") =>
         Cast1 ("(not o L3.equal (BitsN.zero (" ^ mkNatFromInt i ^ ")))")
    | (Type.FixedBits _, Type.Other "char") => Cast1 "(Char.chr o BitsN.toNat)"
    | (Type.FixedBits _, Type.Other "string") => Cast1 "BitsN.toHexString"
    | (Type.FixedBits _, Type.Other "nat") => Cast1 "BitsN.toNat"
    | (Type.FixedBits _, Type.Other "int") => Cast1 "BitsN.toInt"
    | (Type.FixedBits _, Type.Other "bitstring") => Cast1 "BitsN.toBitstring"
    | (Type.FixedBits i, Type.Other s) =>
         if Types.isEnumerated s
            then Cast1 ("(Cast.natTo" ^ s ^ " o BitsN.toNat)")
         else raise Fail (" `" ^ Int.toString i ^ " -> " ^ s)
    | (Type.FixedBits _, Type.FixedBits j) =>
         Cast3 ("BitsN.fromNat", "BitsN.toNat", mkNatFromInt j)
    | (Type.FixedBits _, Type.VarBits (N, _)) =>
         Cast3 ("BitsN.fromNat", "BitsN.toNat", N)
    | (Type.VarBits (N, _), Type.Other "bool") =>
         Cast1 ("(not o L3.equal (BitsN.zero (" ^ N ^ ")))")
    | (Type.VarBits _, Type.Other "string") => Cast1 "BitsN.toHexString"
    | (Type.VarBits _, Type.Other "nat") => Cast1 "BitsN.toNat"
    | (Type.VarBits _, Type.Other "int") => Cast1 "BitsN.toInt"
    | (Type.VarBits _, Type.Other "bitstring") => Cast1 "BitsN.toBitstring"
    | (Type.VarBits (N, _), Type.Other s) =>
         if Types.isEnumerated s
            then Cast1 ("(Cast.natTo" ^ s ^ " o BitsN.toNat)")
         else raise Fail (" `" ^ N ^ " -> " ^ s)
    | (Type.VarBits _, Type.FixedBits j) =>
         Cast3 ("BitsN.fromNat", "BitsN.toNat", mkNatFromInt j)
    | (Type.VarBits _, Type.VarBits (N, _)) =>
         Cast3 ("BitsN.fromNat", "BitsN.toNat", N)
    (*
    | (t1, t2) =>
        ( pp (PolyML.prettyRepresentation (t1, 10))
        ; print "to "
        ; pp (PolyML.prettyRepresentation (t2, 10))
        ; raise Fail ("pickCast: Bad cast")
        )
    *)

fun ppVar (s, ty) =
   ppS (if Types.equalTy Type.unitTy ty then "()" else renameConsReserved s)

val isCond = fn Term.Comb ("i-t-e", _, [_, _, _]) => true
              | _ => false

val isMatch = fn Term.Comb ("match", _, _ :: _) => true
               | _ => false

local
   val destSeq =
      fn Term.Comb (";", _, [a, b]) => (a, b)
       | _ => raise Fail "destSeq"
in
   val destSequence =
      let
         fun iter a t =
            case Lib.total destSeq t of
               SOME (b, c) => iter (b :: a) c
             | NONE => List.rev (t :: a)
      in
         iter []
      end
end

val boolify = ref ([] : string list)
val safemap = ref true

fun expandASTName f = if Tag.isAST f then "dfn'" ^ Tag.remove f else f

fun reference a = String.extract (a, 2, SOME (String.size a - 3))

val bitsTypeVars = Stringset.listItems o Type.freeBitsTypeVars o Term.typeOf

fun maybeTuple l =
   case l of
      [] => []
    | [n] => [ppS n]
    | _ => [ppL (2, [ppTuple (List.map ppS l)])]

local
   fun getTypeInst m v =
      let
         val l =
            List.mapPartial
               (fn Type.SubstBits (q, x) =>
                     if q = v
                        then case x of
                                Type.FixedBits i => SOME (Int.toString i)
                              | Type.VarBits (s, _) => SOME s
                              | _ => NONE
                     else NONE
                 | _ => NONE) m
      in
         case l of
            [] => v
          | [r] => r
          | x => (printn (PolyML.makestring x); raise Fail "getTypeInst")
      end
in
   fun ppDefn name d a ty =
      let
         val s = renameReserved name
         val vs = bitsTypeVars d
      in
         if List.null vs
            then if List.null a then ppS s else ppApp (s, hd a)
         else let
                 val tyd = Term.primTypeOf d
                 val m = Types.match tyd ty
                         handle Types.TypeMatch _ =>
                            Types.match (Type.unitTy --> tyd) ty
                 val i = getTypeInst m
                 val x = maybeTuple (List.map i vs)
              in
                 ppL (2, [ppS s, ppB (1, 0)] @ x @
                         (if List.null a then [] else [ppB (1, 0)]) @ a)
              end
      end
end

fun ppExpression t =
   case t of
     Term.Lit (Term.Other ("UNKNOWN", ty)) => ppExpression (Term.genUnknown ty)
   | Term.Lit v => ppLiteral v
   | Term.Abs ([("_", ty)], _, d) =>
       let
          val sz = mapSize ty
          val de = ppExpression d
       in
          if sz = 0
             then ppApp ("L3.K", de)
          else ppAppPair ("Map.mkMap",
                          ppS (if sz = ~1 then "NONE"
                               else "SOME " ^ Int.toString sz), de)
       end
   | Term.Abs _ =>
       let
          val (v, b) = Term.destAbs t
       in
         ppL (2, [ppS "fn ", ppExpression v, ppS " =>", ppB (1, 0),
                             ppExpression b])
       end
   | Term.Var s_ty => ppVar s_ty
   | Term.Comb ("abs-apply", _, [Term.Abs ([_], _, _), _]) =>
       let
          val (l, b) = Term.destLets t
          val l =
             List.map (fn (v, e) =>
                ppL (4, [ppS "val ", ppExpression v, ppS " =", ppB (1, 0),
                         ppMapExpression e])) l
             |> mapSeparate I [ppB (1, 2)]
       in
          PolyML.PrettyBlock (0, true, [],
              [ppS "let",
               ppB (1, 2)] @ l @
              [ppB (1, 0),
               ppS "in",
               ppB (1, 2),
               ppL (2, [ppExpression b]),
               ppB (1, 0),
               ppS "end"])
       end
   | Term.Comb ("abs-apply", _, [f, x]) =>
       let
          val (sz, cst) = mapSizeFn (Types.domain (Term.typeOf f))
          val fe = ppExpression f
          val xe = ppExpression x
       in
          if sz = 0
             then ppL (2, [ppBracket fe, ppB (1, 0), ppBracket xe])
          else ppAppPair ("Map.lookup", fe,
                          if cst = "" then xe else ppApp (cst, xe))
       end
   | Term.Comb ("i-t-e", _, [a, b, c]) =>
       PolyML.PrettyBlock
           (0, true, [],
            [ppS "if ", ppL (3, [ppExpression a]), ppB (1, 2),
             ppS "then ", ppL (7, [ppExpression b]), ppB (1, 0),
             ppS "else "] @
            (if isCond c then [ppExpression c]
             else [ppL (5, [ppExpression c])]))
   | Term.Comb ("update-map", _, [m, i, e]) =>
       let
          val (sz, cst) = mapSizeFn (Types.domain (Term.typeOf m))
          val me = ppExpression m
          val ie = ppExpression i
          val ee = ppMapExpression e
       in
          if sz = 0
             then ppL (0, [ppS "L3.update", ppB (1, 2), ppBracket me,
                           ppB (1, 2), ppBracket ie, ppB (1, 2),
                           ppBracket ee])
          else ppAppTriple ("Map.update", me,
                            if cst = "" then ie else ppApp (cst, ie), ee)
       end
   | Term.Comb ("<..>", ty, [a, b, c]) =>
      ppBL (0, 2,
            [ppAppPair
               (if Types.equalTy Type.bitstringTy ty
                   then "Bitstring.bits"
                else "BitsN.bits", ppExpression a, ppExpression b),
             ppBracket (ppExpression c)])
   | Term.Comb ("bit-field-insert", ty, [h, l, a, b]) =>
      ppBL (0, 2,
            [ppAppPair
               (if Types.equalTy Type.bitstringTy ty
                   then "Bitstring.bitFieldInsert"
                else "BitsN.bitFieldInsert", ppExpression h, ppExpression l),
             ppPair (ppExpression a, ppExpression b)])
   | Term.Comb ("{..}", _, l) => ppList (List.map ppExpression l)
   | Term.Comb ("[..]", ty, [a]) =>
       (case pickCast (Term.primTypeOf a, ty) of
           Cast0 => ppExpression a
         | Cast1 f => ppApp (f, ppExpression a)
         | Cast2 (f, b) => ppAppPair (f, ppExpression a, ppS b)
         | Cast3 (f1, f2, b) =>
             ppAppPair (f1, ppApp (f2, ppExpression a), ppS b))
   | Term.Comb ("match", ty, m::l) =>
       ppMatch (m, l)
   | Term.Comb (f, ty, []) =>
        let
           val name = expandASTName f
        in
           case Consts.lookupConst f of
             Consts.Accessor (d, _, _) => ppDefn name d [] ty
           | Consts.Definition (d, _, _) => ppDefn name d [] ty
           | Consts.Exception NONE =>
               ppL (0, [ppS "raise ", ppS (Tag.remove f)])
           | _ => raise Fail ("ppExpression, 0-arg: " ^ f)
        end
   | Term.Comb ("&", ty, [a]) =>
        let
           val n = case Types.dest ty of
                     Type.Other s => "write'reg'" ^ s
                   | Type.FixedBits _ =>
                       (case Term.dTypeOf a of
                          Type.Other s => "reg'" ^ s
                        | _ => raise Fail "ppExpression: bad type for &")
                   | _ => raise Fail "ppExpression: bad type for &"
        in
           ppApp (n, ppExpression a)
        end
   | Term.Comb ("Cons", ty, [a]) =>
        let
           fun f l = ppList (List.map ppExpression l)
           fun g t = ppBracket (ppExpression t)
        in
           if Types.equalTy Type.stringTy ty
              then case listOfList t of
                      ([], _) => ppApp ("L3.prefix", ppExpression a)
                    | (l, NONE) =>
                        (case stringOfList l of
                            SOME s => ppQ s
                          | NONE => ppApp ("String.implode", f l))
                    | (l, SOME tm) =>
                         ppBL (0, 2, [ppApp ("String.implode", f l),
                                      ppS "^", g tm])
           else (case listOfList t of
                    ([], _) => ppApp ("(op ::)", ppExpression a)
                  | (l, NONE) => f l
                  | ([h], SOME tm) => ppBL (0, 2, [g h, ppS "::", g tm])
                  | (l, SOME tm) => ppBL (0, 2, [f l, ppS "@", g tm]))
        end
   | Term.Comb ("InitMap", ty, [a]) =>
       let
          val sz = mapSize (Types.domain (Types.expand ty))
          val ae = ppExpression a
       in
          if sz = 0
             then ppApp ("L3.K", ae)
          else ppAppPair ("Map.mkMap",
                          ppS (if sz = ~1 then "NONE"
                               else "SOME " ^ Int.toString sz), ae)
       end
   | Term.Comb (f, ty, [a]) =>
       (case lookupOperation f of
          Consts.Primitive _ =>
           ppApp (ppMop (f, Term.typeOf a, ty), ppExpression a)
        | Consts.Destructor _ =>
           let
              fun err () = raise Fail "Constructor has wrong form"
              val aty = Term.primTypeOf a
              fun pa x = ppApp (x, ppExpression a)
           in
              if Types.isRecordType aty
                 then pa ("(#" ^ f ^ ")")
              else if Types.isFixedBitsType aty andalso Types.isRecordType ty
                 then pa ("rec'" ^ f)
              else case Lib.total Types.destProd aty of
                     SOME (ty1, ty2) =>
                       if Types.equalTy ty1 ty
                          then if Types.isRecordType ty1
                                  then pa (Type.destConstType
                                             (Types.expand ty1) ^ "_" ^ f ^
                                           "_rupd")
                               else if Types.isFixedBitsType ty1 andalso
                                       Types.isRecordType ty2
                                  then pa ("write'rec'" ^ f)
                               else err ()
                       else err ()
                   | NONE => err ()
           end
        | Consts.Constructor _ =>
            (case ppRecord (f, ty, [a]) of
                SOME p => p
              | NONE => ppApp (renameReserved f, ppExpression a))
        | Consts.Accessor (rd, wr, _) =>
            let
               val aty = Term.primTypeOf a
               val rty = Term.primTypeOf rd
               val wty = Term.primTypeOf wr
               val fty = aty --> ty
               val (d, name) =
                  if Types.canMatch rty fty
                     then (rd, f)
                  else if Types.canMatch wty fty
                     then (wr, "write'" ^ f)
                  else if Types.canMatch (Type.unitTy --> rty) fty
                     then (rd, f) (* see makeImpureFunctional below *)
                  else ( Lib.pp (PolyML.prettyRepresentation (t, 10))
                       ; raise Fail "ppExpression: Accessor has bad type"
                       )
            in
               ppDefn name d [ppBracket (ppExpression a)] fty
            end
        | Consts.Definition (d, _, _) =>
            ppDefn (expandASTName f) d [ppBracket (ppExpression a)]
               (Term.primTypeOf a --> ty)
        | Consts.Exception _ =>
            ppL (2, [ppS "raise ", ppS (Tag.remove f), ppB (1, 0),
                     ppBracket (ppExpression a)])
        | Consts.Undefined =>
            if String.isPrefix "boolify'" f
               then ( boolify :=
                         Lib.insert (String.extract (f, 8, NONE)) (!boolify)
                    ; ppApp (f, ppExpression a))
            else if f = "String.explode" orelse f = "String.implode"
               then ppApp (f, ppExpression a)
            else raise Fail ("ppExpression, undefined 1-arg: " ^ f))
   | Term.Comb (",", _, [a, b]) => ppPair (ppExpression a, ppExpression b)
   | Term.Comb (";", _, [_, _]) =>
       let
          val l = destSequence t
       in
          PolyML.PrettyBlock (0, true, [],
             ppS "( " ::
             mapSeparate I [ppB (0, 0), ppS "; "]
                (List.map (fn x => ppL (2, [ppExpression x])) l) @
             [ppB (1, 0), ppS ")"])
       end
   | Term.Comb ("and", _, [a, b]) =>
       ppInfix (ppExpression a, " andalso", ppExpression b)
   | Term.Comb ("or", _, [a, b]) =>
       ppInfix (ppExpression a, " orelse", ppExpression b)
   | Term.Comb ("==", ty, [a, b]) =>
       if Type.isSetTy (Term.typeOf a)
          then ppAppPair ("Set.equal", ppExpression a, ppExpression b)
       else ppInfix (ppExpression a, " =", ppExpression b)
   | Term.Comb ("<-", _, [Term.Var (a, _), b]) =>
       let
          val selfupdate =
             case b of
                Term.Comb ("update-map", _, [Term.Var (m, _), _, _]) => m = a
              | Term.Comb (d, _, [Term.Comb (",", _, [Term.Var (m, _), _])]) =>
                   m = a andalso Consts.isDestructor d
              | Term.Comb ("InitMap", _, _) => true
              | Term.Var (m, _) => m = a
              | _ => false
          val be = if selfupdate then ppExpression b else ppMapExpression b
       in
          ppInfix (ppR (reference a), " :=", be)
       end
   | Term.Comb ("var =", _, [Term.Var (a, _), b, c]) =>
       PolyML.PrettyBlock (0, true, [],
           [ppS "let",
            ppB (1, 2),
            ppL (4, [ppS "val ", ppR (reference a), ppS " = ref ",
                     ppBracket (ppMapExpression b)]),
            ppB (1, 0),
            ppS "in",
            ppB (1, 2),
            ppL (2, [ppExpression c]),
            ppB (1, 0),
            ppS "end"])
   | Term.Comb ("for", _, [a, b, c]) =>
       ppAppTriple ("L3.for", ppExpression a, ppExpression b, ppExpression c)
   | Term.Comb ("foreach", _, [a, b]) =>
       ppAppPair ("L3.foreach", ppExpression a, ppExpression b)
   | Term.Comb (":", ty, [a, b]) =>
       (case Term.destConcats t of
           [x, y] =>
             if Type.isListTy (Types.expand ty)
                then ppBL (0, 2, [ppBracket (ppExpression a),
                                  ppS (if Types.equalTy Type.stringTy ty
                                          then "^"
                                       else "@"),
                                  ppBracket (ppExpression b)])
             else ppApp ("BitsN.@@", ppPair (ppExpression a, ppExpression b))
         | l => if Type.isListTy (Types.expand ty)
                   then ppExpression
                      (Term.Comb ("Concat", ty,
                                  [Term.mkList (Lib.I, Type.listTy ty) l]))
                else ppApp ("BitsN.concat", ppList (List.map ppExpression l)))
   | Term.Comb ("^", ty, l as [a, b]) =>
       let
          fun pp s = ppAppPair (s, ppExpression a, ppExpression b)
       in
          case Types.dest ty of
             Type.Other "bitstring" => pp "Bitstring.replicate"
           | Type.FixedBits i =>
                pp ("BitsN.resize_replicate " ^ Int.toString i)
           | Type.VarBits (s, _) => pp ("BitsN.resize_replicate " ^ s)
           | _ => raise Fail ("ppExpression: " ^ PolyML.makestring t)
       end
   | Term.Comb (f, ty, l as [a, b]) =>
      (case ppRecord (f, ty, l) of
         SOME p => p
       | _ => ppAppPair (ppBop (f, Term.typeOf a, Term.typeOf b),
                         ppExpression a, ppExpression b))
   | Term.Comb (f, ty, l) =>
      (Option.valOf (ppRecord (f, ty, l))
       handle Option.Option =>
                raise Fail ("ppExpression: " ^ PolyML.makestring t))
   | _ => (pp (PolyML.prettyRepresentation (t, 40))
           ; raise Fail "ppExpression: bad match")
and ppRecord (f, ty, l) =
   if Tag.isRecord f
      then let
              val name = Type.destConstType (Types.expand ty)
           in
              case Types.lookupConst name of
                 SOME {def = Types.Record r, ...} =>
                    let
                       val p =
                          List.map
                             (fn ((fld, _), e) =>
                                ppL (2, [ppS fld, ppS " =", ppB (1, 0),
                                         ppExpression e]))
                             (ListPair.zip (r, l))
                    in
                       SOME (ppParen ("{", [ppS ",", ppB (1, 0)], "}") p)
                    end
               | _ => raise Fail ("ppRecord: bad record type: " ^ f)
           end
   else NONE
and ppMatch (m, []) = raise Fail "ppMatch: empty cases"
  | ppMatch (m, [c]) =
   PolyML.PrettyBlock (0, true, [],
       [ppS "case ", ppExpression m, ppS " of",
        ppB (1, 3), ppCase "" c])
  | ppMatch (m, c :: cases) =
   PolyML.PrettyBlock (0, true, [],
       [ppS "case ", ppExpression m, ppS " of",
        ppB (1, 3), ppCase "" c, ppB (1, 1)] @
        mapSeparate I [ppB (1, 1)]
           (List.map (ppCase "| ") cases @
            (if Type.isFixedTy (Term.typeOf m) andalso not (List.null cases)
                andalso Term.isLit (fst (Term.destCase (List.last cases)))
               then [ppS "| _ => raise General.Bind"]
             else [])))
and ppCase s t =
   case t of
      Term.Comb ("case", _,
         [a as Term.Abs (_, _, Term.Comb (",", _, [_, _]))]) =>
         (case Term.destAbs a of
            (_, Term.Comb (",", _, [pat, c])) =>
               ppL (0, [ppS s, ppL (3, [ppPattern pat]),
                        ppS " =>", ppB (1, 4),
                        ppL (4, [(if isMatch c orelse isCond c
                                    then ppBracket
                                  else I) (ppExpression c)])])
          | _ => raise Fail "ppCase: abs")
    | Term.Comb ("case", _, [Term.Comb (",", _, [pat, c])]) =>
         ppL (2, [ppS s, ppL (3, [ppPattern pat]), ppS " =>",
                  ppB (1, 4), ppL (4, [(if isMatch c then ppBracket else I)
                                          (ppExpression c)])])
    | _ => raise Fail "ppCase"
and ppPattern t =
   case t of
      Term.Lit (Term.Other ("Nil", _)) => ppS "[]"
    | Term.Lit v => ppLiteral v
    | Term.Var s_ty => ppVar s_ty
    | Term.Comb (",", _, [a, b]) => ppPair (ppPattern a, ppPattern b)
    | Term.Comb ("Cons", _, [_]) =>
        (case listOfList t of
            ([], _) => ( pp (PolyML.prettyRepresentation (t, 40))
                       ; raise Fail "ppPattern: Cons pat"
                       )
          | (l, NONE) => ppList (List.map ppPattern l)
          | (l, SOME tm) =>
              List.foldr (fn (h, t) => ppInfix (ppPattern h, " ::", t))
                 (ppPattern tm) l)
    | Term.Comb (x as (f, ty, [a])) =>
        (case lookupOperation f of
            Consts.Constructor _ =>
              (case ppRecord x of
                  SOME p => p
                | NONE => ppApp (renameReserved f, ppExpression a))
          | Consts.Primitive _ =>
              ppApp (ppMop (f, Term.typeOf a, ty), ppPattern a)
          | _ => raise Fail ("ppPattern 1-arg: " ^ f))
    | Term.Comb (f, ty, l) =>
       (Option.valOf (ppRecord (f, ty, l))
        handle Option.Option => raise Fail ("ppPattern: " ^ f))
    | _ => (pp (PolyML.prettyRepresentation (t, 40))
            ; raise Fail "ppPattern: bad match")
and ppMapExpression t =
  (case t of
      Term.Lit _ => ppExpression t
    | Term.Abs _ => ppExpression t
    | Term.Comb ("InitMap", _, [_]) => ppExpression t
    | _ =>
      let
         val ty = Term.typeOf t
         val te = ppExpression t
      in
         if !safemap andalso hasMap ty
            then if isMap ty then ppApp ("Map.copy", te)
                 else (safemap := false
                      ; warn ("Reverting to PureMap.\n" ^ PolyML.makestring t)
                      ; te)
         else te
      end)

(* - printing of global variables (state) and definitions -------------- *)

local
   fun ppGlobal (s, ty) =
      let
         val unk = ppExpression (Term.genUnknown (Types.expand ty))
      in
         ppL (0, [ppS "val", ppB (1, 2), ppR s, ppS " = ref", ppB (1, 2),
                  ppL (2, [ppL (1, [ppS "(", unk, ppS ")"])]), ppB (0, 2),
                  ppS ": ", ppBracket (ppType ty), ppS " ref"])
      end
in
   val ppGlobals =
      List.map (ppGlobal o (I ## (#typ))) o Env.listVariables o Env.get
end

local
   fun ppGlobalSig (s, ty) =
      ppL (0, [ppS "val", ppB (1, 2), ppR s, ppS ":",
               ppB (1, 2), ppBracket (ppType ty), ppS " ref"])
in
   val ppGlobalsSig =
      List.map (ppGlobalSig o (I ## (#typ))) o Env.listVariables o Env.get
end

local
   fun v i = ppS ("t" ^ Int.toString i)
   fun ppTupleN name n =
      let
         val l = List.tabulate (n, v)
         val (x, y) = Lib.lastButlast l
         val p = List.foldr ppPair x y
         val z = String.size name + 3
      in
         ppL (4, [ppS ("fun " ^ name ^ " "), ppL (z, [ppList l]), ppS " =",
                  ppB (1, 2), ppL (2, [p]), ppB (1, 0),
                  ppS ("| " ^ name ^ " (_: bool list) = raise Fail \"" ^
                       name ^ "\"")])
      end
in
   fun ppBoolifyN n =
      let
         val ns = Int.toString n
         val tuple = "tuple'" ^ ns
         val name = "boolify'" ^ ns
      in
         PolyML.PrettyBlock (0, true, [],
            [ppS "local", ppB (1, 2), ppTupleN tuple n, ppB (1, 0), ppS "in",
             ppB (1, 2),
             ppS ("val " ^ name ^ " = " ^ tuple ^ " o BitsN.toList"),
             ppB (1, 0), ppS "end"])
      end
   fun ppBoolifyNSig n =
      let
         val name = "boolify'" ^ (Int.toString n)
         val ty = Type.foldProdList (List.tabulate (n, fn _ => Type.boolTy))
      in
         PolyML.PrettyBlock (2, true, [],
            [ppS ("val " ^ name ^ ":"), ppB (1, 0),
             PolyML.PrettyBlock (0, false, [],
                [ppType (Type.fixedTy n), ppB (1, 0), ppS "->", ppB (1, 0),
                 ppType ty])])
      end
end

local
   fun f (s: string, ty) = (s, Term.Var ("(!" ^ renameConsReserved s ^ ")", ty))
   fun dereference t =
      let
         val vs = List.filter (fn (v, _) => v <> "_") (Term.freeVars t)
         val s = List.map f vs
      in
         Term.inst (Stringmap.fromList s) t
      end
in
   val conv = Convert.mergeAnonConv o dereference o
              Matches.stringExplodeMatches o Matches.boolifyMatches
end

val impure = ref Stringset.empty

val isImpure =
   Option.isSome o
   Term.findTerm
      (fn Term.Var _ => true
        | Term.Comb (f, _, _) =>
           Tag.isException f orelse Stringset.member (!impure, expandASTName f)
        | _ => false)

val makeImpureFunctional =
   Term.depthconv
      (fn t as Term.Comb (f, ty, []) =>
            if Stringset.member (!impure, expandASTName f)
               then Term.Comb (f, ty, [Term.unitTm])
            else t
        | _ => raise Term.NoConv)

fun ppDefinition (s, t) =
   let
      val vs = maybeTuple (bitsTypeVars t)
   in
      case t of
        Term.Abs _ =>
          let
             val (v, b) = Term.destAbs t
          in
             ppL (2, [ppS ("fun " ^ s), ppB (1, 0)] @ vs @
                     (if List.null vs then [] else [ppB (1, 0)]) @
                     [ppL (2, [ppPattern v]), ppS " =",
                      ppB (1, 0), ppMapExpression b, ppS ";"])
          end
      | _ =>
         if List.null vs
            then ppL (2, [ppS ("val " ^ s ^ " ="), ppB (1, 0),
                          ppMapExpression t])
         else ppL (2, [ppS ("fun " ^ s), ppB (1, 0)] @ vs @
                      [ppS " =", ppB (1, 0), ppMapExpression t, ppS ";"])
   end

fun ppDefinitions () =
   let
      val l =
         List.map
             (fn {name, def, ...} =>
                 let
                    val d = conv def
                    val is_impure = isImpure d
                    val () =
                       if is_impure
                          then impure := Stringset.add (!impure, name)
                       else ()
                    val d = makeImpureFunctional d
                    val d = if is_impure andalso not (Term.isAbs d)
                               then Term.absList [("_", Type.unitTy)] d
                            else d
                 in
                    ppDefinition (renameReserved name, d)
                 end)
            ( safemap := true
            ; boolify := []
            ; impure := Stringset.empty
            ; Consts.listDefinitions ()
            )
      val bs = List.mapPartial Int.fromString (!boolify)
   in
      List.map ppBoolifyN bs @ l
   end

fun ppDefinitionSig (s, t) =
   let
      val ty = case t of
                  Term.Abs (_, ty, _) =>
                    let
                       val (t1, t2) = Types.domainRange ty
                    in
                       ppInfix (ppType t1, " ->", ppType t2)
                    end
                | _ => ppType (Term.typeOf t)
      val vs = List.map (K Type.natTy) (bitsTypeVars t)
   in
      if List.null vs
         then ppL (2, [ppS ("val " ^ s ^ ":"), ppB (1, 0), ty])
      else ppL (2, [ppS ("val " ^ s ^ ":"), ppType (Type.foldProdList vs),
                    ppS "->", ppB (1, 0), ty])
   end

fun ppDefinitionsSig () =
   let
      val l =
         List.map
            (fn {name, def = d, ...} =>
                 let
                    val is_impure =
                       Stringset.member (!impure, expandASTName name)
                    val d = if is_impure andalso not (Term.isAbs d)
                               then Term.absList [("_", Type.unitTy)] d
                            else d
                 in
                    ppDefinitionSig (renameReserved name, d)
                 end)
            (Consts.listDefinitions ())
      val bs = List.mapPartial Int.fromString (!boolify)
   in
      List.map ppBoolifyNSig bs @ l
   end

local
   val exportFunctor = ref false
   val sep = Lib.mapSeparate I [PP.ppS "\n"]
   val line = String.implode (List.tabulate (73, fn _ => #"-"))
   val scomm = "\n(* " ^ line ^ "\n   "
   val fcomm = "\n   " ^ line ^ " *)\n\n"
   fun commentBlock s = if s = "" then [] else [ppS (scomm ^ s ^ fcomm)]
   fun block f s =
      let
         val l = f ()
      in
         if List.null l then [] else commentBlock s @ sep l
      end
   fun struct_functor name =
      if !exportFunctor then "functor " ^ name ^ " ()" else "structure " ^ name
   fun insertSafeMap x l =
      List.take (l, 3) @
      [ppS ("\nstructure Map" ^ x ^
            (if !safemap then "MutableMap" else "PureMap") ^ "\n")] @
      List.drop (l, 3)
in
   fun setFunctor b = exportFunctor := b
   fun ppStructure (name, date)  =
      [ppS ("(* " ^ name ^ " - generated by L3 - " ^ date ^ " *)\n\n"),
       ppS (struct_functor name ^ " :> " ^ name ^ " =\n"),
       ppS "struct\n"] @
      block ppTypeDefs "Type declarations" @
      block ppTypeCasts "Casting maps (for enumerated types)" @
      block ppRecordUpdateFuns "Record update functions" @
      block ppExceptions "Exceptions" @
      block ppGlobals "Global variables (state)" @
      block ppDefinitions "Main specification" @
      [ppS "\nend"]
      |> insertSafeMap " = "
   fun ppSignature (name, date)  =
      [ppS ("(* " ^ name ^ " - generated by L3 - " ^ date ^ " *)\n\n"),
       ppS ("signature " ^ name ^ " =\n"),
       ppS "sig\n"] @
      block ppTypeDefs "Types" @
      block ppExceptions "Exceptions" @
      commentBlock "Functions" @
      ppTypeCastsSig () @
      ppGlobalsSig () @
      ppRecordUpdateFunsSig () @
      ppDefinitionsSig () @
      [ppS "\nend"]
      |> insertSafeMap ": "
end

fun export s =
   let
      val {dir, file} = OS.Path.splitDirFile s
      val smlFile =
         OS.Path.joinDirFile
            {dir = dir,
             file = OS.Path.joinBaseExt {base = file, ext = SOME "sml"}}
      val sigFile =
         OS.Path.joinDirFile
            {dir = dir,
             file = OS.Path.joinBaseExt {base = file, ext = SOME "sig"}}
      val name_date = (file, Date.toString (Date.fromTimeLocal (Time.now ())))
   in
      savePP smlFile (ppStructure name_date)
    ; savePP sigFile (ppSignature name_date)
   end

fun spec (specfiles, path) = (Runtime.LoadF specfiles; export path)

end (* SMLExport *)

(* ------------------------------------------------------------------------ *)

(* Testing...

val () = SMLExport.spec ("examples/Thacker/tiny.spec", "sml/tiny")
val () = SMLExport.spec ("examples/mips/mips.spec", "sml/mips")
val () = SMLExport.spec ("examples/x86/x64.spec", "sml/x64")

val () =
   SMLExport.spec
     ("examples/arm7/arm-base.spec, examples/arm7/arm-vfp.spec,\
      \examples/arm7/arm-iset.spec, examples/arm7/arm-run.spec", "sml/arm")

val () =
   SMLExport.spec
     ("examples/arm7/arm-base.spec, examples/arm7/arm-vfp.spec,\
      \examples/arm7/arm-iset.spec, examples/arm7/arm-run.spec,\
      \examples/arm7/arm-encode.spec", "sml/arm")

val () =
   SMLExport.spec
      ("examples/6m/arm-base.spec, examples/6m/arm-iset.spec,\
       \examples/6m/arm-run.spec", "sml/m0")

val () = SMLExport.export "sml/test.sml"

*)
