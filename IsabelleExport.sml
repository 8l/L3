(*
use "Export.sml";
*)

(* ------------------------------------------------------------------------
   Pretty-print Isabelle/HOL code for types, terms and definitions
   ------------------------------------------------------------------------ *)

signature IsaPP =
sig
   val ppBoolifyList : unit -> PolyML.pretty list
   val ppDefinitions :
     (Consts.defn -> (string * bool * Term.term) option) ->
     (string * PolyML.pretty) list
   val ppTypeCasts : string -> PolyML.pretty list
   val ppTypeDefs : unit -> PolyML.pretty list
end

structure IsaPP :> IsaPP =
struct
   local
      (* probably incomplete *)
      val reserved =
         Stringset.fromList
            [
             "ML", "ML_prf", "ML_val", "SML_file", "SML_import",
             "abbreviation", "also", "apply", "apply_end", "assume", "assumes",
             "attach", "attribute_setup", "axiomatization", "back", "begin",
             "binder", "bundle", "by", "case", "class", "class_deps",
             "code_datatype", "constrains", "consts", "context", "corollary",
             "declaration", "declare", "def", "default_sort", "defer",
             "defines", "definition", "defs", "display_drafts", "done", "end",
             "experiment", "extract", "extract_type", "finally", "find_consts",
             "find_theorems", "fix", "fixes", "for", "from", "full_prf", "fun",
             "function", "guess", "have", "help", "hence", "hide_class",
             "hide_const", "hide_fact", "hide_type", "identifier", "if",
             "imports", "in", "include", "includes", "including", "infix",
             "infixl", "infixr", "instance", "instantiation", "interpret",
             "is", "judgment", "lemma", "lemmas", "let", "local_setup",
             "locale", "locale_deps", "method_setup", "moreover",
             "named_theorems", "next", "no_notation", "no_syntax",
             "no_translations", "no_type_notation", "nonterminal", "notation",
             "note", "notepad", "notes", "obtain", "obtains", "oops", "open",
             "oracle", "output", "overloaded", "overloading",
             "parse_ast_translation", "parse_translation", "pervasive",
             "prefer", "presume", "prf", "primrec", "print_ML_antiquotations",
             "print_abbrevs", "print_antiquotations", "print_ast_translation",
             "print_attributes", "print_bundles", "print_cases",
             "print_classes", "print_codesetup", "print_commands",
             "print_context", "print_defn_rules", "print_dependencies",
             "print_facts", "print_interps", "print_locale", "print_locales",
             "print_methods", "print_options", "print_rules", "print_simpset",
             "print_state", "print_statement", "print_syntax",
             "print_term_bindings", "print_theorems", "print_theory",
             "print_trans_rules", "print_translation", "private", "proof",
             "prop", "qed", "qed_script", "qualified", "realizability",
             "realizers", "schematic_corollary", "schematic_lemma",
             "schematic_theorem", "setup", "shows", "simproc_setup",
             "structure", "subclass", "sublocale", "syntax",
             "syntax_declaration", "term", "termination", "text", "text_raw",
             "then", "theorem", "theorems", "theory", "thm", "thm_deps",
             "thus", "thy_deps", "translations", "txt", "typ", "type_decl",
             "type_notation", "type_synonym", "typed_print_translation",
             "ultimately", "unchecked", "unfolding", "unused_thms", "using",
             "value", "welcome", "where", "with"
             ]
   in
      fun isReserved s = Stringset.member (reserved, s)
      fun quoteReserved s = if isReserved s then Lib.quote s else s
   end

   open PP

   local
      open Type
      val param =
         fn ListTy => "list"
          | OptionTy => "option"
          | SetTy => "set"
      fun pp dty =
         case dty of
            VarType s            => ppS ("'" ^ s)
          | ConstType "unit"     => ppS "unit"
          | ConstType "int"      => ppS "int"
          | ConstType "nat"      => ppS "nat"
          | ConstType "bool"     => ppS "bool"
          | ConstType "char"     => ppS "char"
          | ConstType "rounding" => ppS "L3_Lib.rounding"
          | BV i => ppS (Int.toString i ^ " word")
          | BVV s => ppS ("'" ^ s ^ "::len word")
          | Prod (a, b)  =>
              let
                 val ppb = pp b
                 val ppb = case b of Arrow _ => ppBracket ppb | _ => ppb
              in
                 ppL (0, [ppBracket (pp a), ppS " \\<times>", ppB (1, 0), ppb])
              end
          | Arrow (a, b) => ppInfix (pp a, " \\<Rightarrow>", pp b)
          | ParamType (ListTy, ConstType "char") => ppS "string"
          | ParamType (ListTy, ConstType "bool") => ppS "bool list"
          | ParamType (p, t) => ppBL (1, 2, [ppBracket (pp t), ppS (param p)])
          | ConstType s => ppS s
   in
      fun ppType ty = pp (fst (Types.expand ty))
   end

   val rename = String.translate (fn #"@" => "''" | c => String.str c)

   local
      fun ppQTy ty =
         ppB (1,0) ::
         (case ppType ty of
             pp as PolyML.PrettyString s =>
               if String.isSubstring " " s orelse isReserved s
                  then [ppS "\"", pp, ppS "\""]
               else [pp]
           | pp => [ppParen ("\"", [ppS ""], "\"") [pp]])
      val ppOTy = fn SOME ty => ppQTy ty | NONE => []
      fun ppDatatype name =
         [ppS ("datatype " ^ quoteReserved name ^ " ="), ppB (1, 2)]
      fun ppTypeDef (name, d: Types.typeconst) =
         case #def d of
           Types.Constructors (Types.Enum m) =>
             let
                val l = m |> Stringmap.listItems
                          |> msort (Int.compare o (snd ## snd))
                          |> List.map (fn (n, _) => ppS (quoteReserved n))
                          |> Lib.mapSeparate Lib.I [ppS " |", ppB (1, 0)]
             in
                SOME (ppL (2, ppDatatype name @ l))
             end
         | Types.Constructors (Types.Construct m) =>
             let
                val l =
                   m |> Stringmap.listItems
                     |> List.map
                          (fn (n, oty) =>
                             ppL
                               (4, ppS (quoteReserved (rename n)) :: ppOTy oty))
                     |> Lib.mapSeparate Lib.I [ppB (1, 0), ppS "| "]
             in
                SOME (PolyML.PrettyBlock (2, true, [], ppDatatype name @ l))
             end
         | Types.Record r =>
             let
                val l =
                   r |> List.map
                          (fn (n, ty) =>
                             ppL (2, ppS (quoteReserved n ^ " ::") :: ppQTy ty))
                val h = [ppS ("record " ^ quoteReserved name ^ " =")]
             in
                SOME (PolyML.PrettyBlock
                        (2, true, [], h @ [ppB (1, 0), ppBL (0, 0, l)]))
             end
         | _ => NONE
   in
      fun ppTyAnti ty =
         case fst (Types.expand ty) of
            Type.ConstType "unit" => ppS "HOLogic.unitT"
          | Type.ConstType "bool" => ppS "HOLogic.boolT"
          | Type.ConstType "char" => ppS "HOLogic.charT"
          | Type.ConstType "nat" => ppS "HOLogic.natT"
          | Type.ConstType "int" => ppS "HOLogic.intT"
          | Type.ConstType s =>
               if (s = Monad.state () handle Option.Option => false)
                  then ppS "qTy"
               else let
                       val s = if s = "rounding" then "L3_Lib.rounding" else s
                    in
                       ppS ("@{typ " ^ quoteReserved s ^ "}")
                    end
          | Type.BV i =>
              let
                 val s = Int.toString i
              in
                 if Lib.mem i [1,4,8,16,32,64]
                    then ppS ("w" ^ s)
                 else ppS ("(Word_Lib.mk_wordT " ^ s ^ ")")
              end
          | _ => ppL (0, ppS "@{typ" :: ppQTy ty @ [ppS "}"])
      fun ppTypeDefs () = List.mapPartial ppTypeDef (Types.listConsts ())
   end

   local
      fun ppLine (thy_name, b) start x =
         ppS ((if start then "  " else "| ") ^ thy_name ^ "." ^ fst x ^
              " => " ^ b x)
      fun ppEnum _ (_, []) = raise Fail "ppEnum: empty"
        | ppEnum (f, pp_line) (name, h :: t) =
         let
            val fname = name ^ "_to_" ^ f
         in
            PolyML.PrettyBlock (0, true, [],
               [ppS ("fun " ^ fname ^ " :: \"" ^ name ^ " \\<Rightarrow> " ^
                     f ^ "\" where"), ppB (1, 2),
                ppS ("\"" ^ fname ^ " x ="), ppB (1, 3),
                ppS ("(case x of"), ppB (1, 5),
                PolyML.PrettyBlock (5, true, [],
                   mapSeparate I [ppB (1, 0)]
                     (pp_line true h :: List.map (pp_line false) t)),
                ppS ")\""])
         end
      fun qt s = "''" ^ s ^ "''"
      fun ppToNat thy = ppEnum ("nat", ppLine (thy, Int.toString o snd))
      fun ppToString thy = ppEnum ("string", ppLine (thy, qt o fst))
      fun ppLine (thy_name, b) start x =
         ppS ((if start then "" else "else ") ^ "if x = " ^ b x ^ " then " ^
              thy_name ^ "." ^ fst x)
      fun ppEnum _ (_, []) = raise Fail "ppEnum: empty"
        | ppEnum (f, pp_line) (name, h :: t) =
         let
            val fname = f ^ "_to_" ^ name
         in
            PolyML.PrettyBlock (0, true, [],
               [ppS ("fun " ^ fname ^ " :: \"" ^ f ^ " \\<Rightarrow> " ^
                     name ^ "\" where"), ppB (1, 2),
                ppS ("\"" ^ fname ^ " x ="), ppB (1, 3), ppS "(",
                PolyML.PrettyBlock (4, true, [],
                   mapSeparate I [ppB (1, 0)]
                     (pp_line true h :: List.map (pp_line false) t)),
                ppB (1, 4), ppS "else HOL.undefined)\""])
         end
      fun ppNatTo thy = ppEnum ("nat", ppLine (thy, Int.toString o snd))
      fun ppStringTo thy = ppEnum ("string", ppLine (thy, qt o fst))
      val items = Lib.msort (fn ((_, x), (_, y)) => Int.compare (x, y)) o
                  Stringmap.listItems
   in
      fun ppTypeCasts thy_name =
         let
            val l =
               List.mapPartial
                 (fn (name, {def = Types.Constructors (Types.Enum m), ...}) =>
                    SOME (name, items m)
                   | _ => NONE) (Types.listConsts ())
         in
            if List.null l
               then []
            else [ppS "\n"] @
                 mapSeparate I [ppS "\n"]
                   (List.map (ppNatTo thy_name) l @
                    List.map (ppToNat thy_name) l @
                    List.map (ppToString thy_name) l @
                    List.map (ppStringTo thy_name) l)
         end
   end

   (* --------------------------------------------------------------------- *)

   local
      fun ppChar c = ppS ("#\"" ^ Char.toString c ^ "\"")
      fun ppInt i = ppS (Int.toString i)
      val ppNat = ppInt o Nat.toInt
   in
      val ppLiteral =
         fn Term.Bits w =>
               ppAppPair ("lw", ppNat (BitsN.toNat w), ppNat (BitsN.size w))
          | Term.Bitstring s =>
               ppL (1, [ppS "lv", ppQ (Bitstring.toBinString s)])
          | Term.Bool true => ppS "lt"
          | Term.Bool false => ppS "lf"
          | Term.Char c => ppL (1, [ppS "lsc", ppB (1, 0), ppChar c])
          | Term.Enum (0, "rounding") => ppS "@{term roundTiesToEven}"
          | Term.Enum (1, "rounding") => ppS "@{term roundTowardPositive}"
          | Term.Enum (2, "rounding") => ppS "@{term roundTowardNegative}"
          | Term.Enum (3, "rounding") => ppS "@{term roundTowardZero}"
          | Term.Enum (n, s) =>
              (let
                  val e = Option.valOf (Types.revenum s n)
               in
                  ppAppTriple ("lc", ppQ e, ppQ s, ppS "@{theory}")
               end
               handle Option =>
                  raise Fail ("ppLiteral: Enum (" ^ Nat.toString n ^ ", " ^ s))
          | Term.Int i => ppL (1, [ppS "li", ppB (1, 0), ppInt i])
          | Term.Nat n => ppL (1, [ppS "ln", ppB (1, 0), ppNat n])
          | Term.Other ("UNKNOWN", ty) => ppApp ("lx", ppTyAnti ty)
          | Term.Other (s, ty) =>
              (case fst (Types.expand ty) of
                  Type.BVV n =>
                    (ppAppPair
                        ("ly",
                         ppInt (Option.valOf (Int.fromLit (Tag.remove s))),
                         ppQ n)
                     handle Option => raise Fail ("ppLiteral: BVV " ^ s))
                | _ =>
                    (case s of
                        "{}" => ppApp ("le", ppTyAnti (Types.destParam ty))
                      | "Nil" => ppApp ("lnl", ppTyAnti (Types.destParam ty))
                      | "None" => ppApp ("lo", ppTyAnti (Types.destParam ty))
                      | _ => ppAppPair
                               ("Term.Const",
                                ppL (0, [ppS "@{const_name", ppB (1, 0), ppQ s,
                                         ppS "}"]), ppTyAnti ty)))
          | Term.String s => ppL (1, [ppS "ls", ppB (0, 0), ppQ s])
          | Term.Unit => ppS "lu"
      end

   fun lookupOperation s =
      case Consts.lookupConst s of
         Consts.Definition (_, _, ~1) => Consts.Primitive []
       | c as Consts.Constructor _ =>
           if s = "Some" then Consts.Primitive [] else c
       | c => c

   val mopId =
      Stringset.fromList
        ["Cardinality", "IsAlpha", "IsSpace", "RemoveExcept", "Size", "Abs",
         "Difference", "Drop", "Element", "Fst", "Head", "IndexOf",
         "Intersect", "IsAlphaNum", "IsDigit", "IsHexDigit", "IsLower",
         "IsMember", "IsSome", "IsSubset", "IsUpper", "Length", "Max", "Min",
         "Msb", "QuotRem", "Remove", "RemoveDuplicates", "Snd", "Some", "Tail",
         "Take", "ToLower", "ToUpper", "Union", "Update", "ValOf"]

   val fpOp =
      Stringset.fromList ["Abs", "Add", "Equal", "IsNaN", "Mul", "Neg", "Sub"]

   fun fp s =
      let
         val b = if String.isPrefix "FP32_" s then "false"
                 else if String.isPrefix "FP64_" s then "true"
                 else raise Fail ("ppMop: " ^ s)
         val r = String.extract (s, 5, NONE)
         val r = if r = "LessThan"
                    then "Less"
                 else if Stringset.member (fpOp, r)
                    then r
                 else raise Fail ("ppMop: " ^ s)
      in
         ppS ("FP" ^ r ^ " " ^ b)
      end

   fun ppMop (f, ty) =
      case f of
        "-" => ppS "Neg"
      | "~" => ppS "BNot"
      | "PadLeft" => ppS "PadLeft"
      | "PadRight" => ppS "PadRight"
      | "Concat" => ppS "Flat"
      | "FromBinString" => ppS "Bin"
      | "FromDecString" => ppS "Dec"
      | "FromHexString" => ppS "Hex"
      | "InitMap" => ppApp ("K1", ppTyAnti (Types.domain ty))
      | "Log2" => ppS "Log"
      | "Reverse" => ppS "Rev"
      | "SetOfList" => ppS "SofL"
      | "SignExtend" => ppApp ("SE", ppTyAnti ty)
      | "SignedMax" => ppS "SMax"
      | "SignedMin" => ppS "SMin"
      | "ZeroExtend" => ppApp ("Cast", ppTyAnti ty)
      | "not" => ppS "Not"
      | _ => if Stringset.member (mopId, f) then ppS f else fp f

   val ppBop =
      fn "#<<"        => "Rol"
       | "#>>"        => "Ror"
       | "&&"         => "BAnd"
       | "*"          => "Mul"
       | "**"         => "Exp"
       | "+"          => "Add"
       | "-"          => "Sub"
       | "<"          => "Lt"
       | "<+"         => "Ult"
       | "<.>"        => "Bit"
       | "<<"         => "Lsl"
       | "<="         => "Le"
       | "<=+"        => "Ule"
       | ">"          => "Gt"
       | ">+"         => "Ugt"
       | ">="         => "Ge"
       | ">=+"        => "Uge"
       | ">>"         => "Asr"
       | ">>+"        => "Lsr"
       | "??"         => "BXor"
       | "and"        => "And"
       | "bit-modify" => "Mdfy"
       | "div"        => "Div"
       | "in"         => "In"
       | "insert"     => "Insert"
       | "mod"        => "Mod"
       | "or"         => "Or"
       | "quot"       => "Quot"
       | "rem"        => "Rem"
       | "splitl"     => "Splitl"
       | "splitr"     => "Splitr"
       | "fields"     => "Fld"
       | "tokens"     => "Tok"
       | "||"         => "BOr"
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

   val listOfTuple =
      let
         fun iter a =
            fn Term.Comb (",", _, [l, r]) => iter (l::a) r
             | tm => tm::a
      in
         List.rev o iter []
      end

   fun qualify ty = Type.destConstType (Types.expand ty) ^ "."

   local
      val boolify = ref ([]: int list)
      fun ppBoolify1 i =
         let
            val name = "boolify'" ^ Int.toString i
            val l = List.tabulate (i, fn _ => Type.boolTy)
            val ty = Type.fixedTy i --> Type.foldProdList l
            val l = List.tabulate (i, fn j => ppS ("b" ^ Int.toString j))
         in
            PolyML.PrettyBlock
              (2, true, [],
               [ppS ("\nfun " ^ name ^ " :: \""), ppType ty, ppS "\" where",
                ppB (1, 0),
                ppS ("\"" ^ name ^ " w ="), ppB (1, 1),
                ppS "(case to_bl w of", ppB (1, 3),
                ppList l, ppS " \\<Rightarrow>", ppB (1, 3),
                ppTuple l, ppS ")\""])
         end
   in
      fun boolifyInsert i =
         boolify := Set.insert (Option.valOf (Int.fromString i), !boolify)
      fun ppBoolifyList () =
         List.map ppBoolify1 (msort Int.compare (!boolify) before boolify := [])
   end

   val currentDefinition = ref ""

   fun ppExpression t =
      case t of
        Term.Lit v => ppLiteral v
      | Term.Abs _ =>
          let
             val (v, b) = Term.destAbs t
          in
             ppAppPair ("close", ppExpression v, ppExpression b)
          end
      | Term.Var ("_", ty) => ppApp ("var_a", ppTyAnti ty)
      | Term.Var (s, ty) =>
         (case Types.dest ty of
            Type.Other "unit" => ppS ("var_u" ^ quote s)
          | Type.Other "bool" => ppS ("var_b" ^ quote s)
          | Type.Other "nat" => ppS ("var_n" ^ quote s)
          | Type.Other "int" => ppS ("var_i" ^ quote s)
          | Type.Other "string" => ppS ("var_s" ^ quote s)
          | Type.Other "bitstring" => ppS ("var_v" ^ quote s)
          | Type.FixedBits i =>
               ppS ("var_w(" ^ quote s ^ "," ^ Int.toString i ^ ")")
          | _ => ppAppPair ("var", ppQ s, ppTyAnti ty))
      | Term.Comb ("abs-apply", _, [b1 as Term.Abs ([q], _, b2), e]) =>
          let
             val (v, b) =
                case b2 of
                  Term.Comb ("match", _, [Term.BVar (0, _), _]) =>
                     hd (snd (Term.destMatch b2))
                | _ => let val v = Term.Var q in (v, Term.apply b1 v) end
          in
             ppAppTriple ("let'", ppExpression v, ppExpression e,
                          ppExpression b)
          end
      | Term.Comb ("abs-apply", _, [f, x]) =>
          ppAppPair ("apply", ppExpression f, ppExpression x)
      | Term.Comb ("i-t-e", _, [_, _, _]) =>
          (case Term.destIfThens t of
              ([(a, b)], c) =>
                ppAppTriple
                  ("ite", ppExpression a, ppExpression b, ppExpression c)
            | (l, e) =>
                let
                   val its =
                      List.map (ppPair o (ppExpression ## ppExpression)) l
                in
                   ppAppPair ("itb", ppList its, ppExpression e)
                end)
      | Term.Comb ("update-map", _, [a, b, c]) =>
          ppAppTriple ("fupd", ppExpression a, ppExpression b, ppExpression c)
      | Term.Comb ("<..>", ty, [h, l, a]) =>
          ppAppQuad ("ex", ppExpression a, ppExpression h, ppExpression l,
                     ppTyAnti ty)
      | Term.Comb ("bit-field-insert", _, [h, l, a, b]) =>
          ppAppQuad ("bfi", ppExpression h, ppExpression l, ppExpression b,
                     ppExpression a)
      | Term.Comb ("{..}", _, l) =>
          ppL (2, [ppS "sl", ppList (List.map ppExpression l)])
      | Term.Comb ("[..]", ty, [a]) =>
          ppAppPair ("mop", ppApp ("Cast", ppTyAnti ty), ppExpression a)
      | Term.Comb ("match", ty, m::l) =>
          ppMatch (m, l)
      | Term.Comb (f, ty, []) =>
           let
              val name = if Tag.isAST f then "dfn'" ^ Tag.remove f else f
              fun c () =
                 ppAppTriple ("const", ppQ name, ppTyAnti ty, ppS "@{theory}")
           in
              case Consts.lookupConst f of
                 Consts.Accessor _ => c ()
               | Consts.Definition _ => c ()
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
              ppAppQuad
                 ("call", ppQ n, ppTyAnti ty, ppExpression a, ppS "@{theory}")
           end
      | Term.Comb ("m'const", _, [a]) =>
          ppAppPair ("mu", ppExpression a, ppTyAnti (Monad.stateOf t))
      | Term.Comb ("m'read", _, [a])    => ppApp ("mr", ppExpression a)
      | Term.Comb ("m'write", _, [a])   => ppApp ("mw", ppExpression a)
      | Term.Comb ("m'for", _, [a])     => ppApp ("forloop", ppExpression a)
      | Term.Comb ("m'foreach", _, [a]) => ppApp ("foreach", ppExpression a)
      | Term.Comb ("m'bind", _, [a]) =>
          let
             val (l, r) = Term.destPair a
          in
             ppAppPair ("mb", ppExpression l, ppExpression r)
          end
      | Term.Comb ("m'extend", _, [a]) =>
          let
             val (l, r) = Term.destPair a
          in
             ppAppPair ("mn", ppExpression l, ppExpression r)
          end
      | Term.Comb ("m'unextend", ty, [a]) =>
          let
             val ety = fst (Types.destProd (snd (Monad.destMonadTy ty)))
          in
             ppAppPair ("md", ppExpression a, ppTyAnti ety)
          end
      | Term.Comb ("Cons", _, [a]) =>
          (case listOfList t of
              ([], _) => ppAppPair ("llc", ppS "[]", ppExpression a)
            | (l, NONE) =>
                (case stringOfList l of
                    SOME s => ppL (1, [ppS "ls", ppB (0, 0), ppQ s])
                  | NONE =>
                      ppL (2, [ppS "ll", ppList (List.map ppExpression l)]))
            | (l, SOME tm) =>
                 ppAppPair ("llc", ppList (List.map ppExpression l),
                            ppExpression tm))
      | Term.Comb (f, ty, [a]) =>
          (case lookupOperation f of
             Consts.Primitive _ =>
               ppAppPair ("mop", ppMop (f, ty), ppExpression a)
           | Consts.Destructor _ =>
              let
                 fun err () = raise Fail "Constructor has wrong form"
                 val aty = Term.primTypeOf a
                 val pa = ppExpression a
                 fun pt (x, y) =
                    ppAppQuad (x, ppQ (y ^ f), ppTyAnti ty, pa, ppS "@{theory}")
              in
                 if Types.isRecordType aty
                    then pt ("call", qualify aty)
                 else if Types.isFixedBitsType aty andalso Types.isRecordType ty
                    then pt ("call", "rec'")
                 else case Lib.total Types.destProd aty of
                        SOME (ty1, ty2) =>
                          if Types.equalTy ty1 ty
                             then if Types.isRecordType ty1
                                     then ppAppTriple
                                           ("rupd", ppQ (qualify ty1 ^ f), pa,
                                            ppS "@{theory}")
                                  else if Types.isFixedBitsType ty1 andalso
                                          Types.isRecordType ty2
                                     then pt ("call", "write'rec'")
                                  else err ()
                          else err ()
                      | NONE => err ()
              end
           | Consts.Constructor _ =>
               (case ppRecord (f, ty, [a]) of
                  SOME p => p
                | NONE =>
                    ppAppQuad ("call", ppQ (qualify ty ^ rename f),
                               ppTyAnti ty, ppExpression a, ppS "@{theory}"))
           | Consts.Accessor (rd, wr, _) =>
               let
                  val aty = Term.primTypeOf a
                  val rty = Term.primTypeOf rd
                  val wty = Term.primTypeOf wr
                  fun name fty = if Types.canMatch rty fty
                                    then f
                                 else if Types.canMatch wty fty
                                    then "write'" ^ f
                                 else raise Fail "Accessor has bad type"
                  val n = name (aty --> ty)
                          handle Fail _ =>
                            name (aty --> fst (Monad.destMonadTy ty))
               in
                  ppAppQuad ("call", ppQ n, ppTyAnti ty, ppExpression a,
                             ppS "@{theory}")
               end
           | Consts.Definition _ =>
               let
                  val name = if Tag.isAST f then "dfn'" ^ Tag.remove f else f
               in
                  if name = !currentDefinition
                     then ppAppPair
                            ("apply",
                             ppExpression
                                (Term.Var (name, Term.typeOf a --> ty)),
                             ppExpression a)
                  else
                     ppAppQuad ("call", ppQ name, ppTyAnti ty, ppExpression a,
                                ppS "@{theory}")
               end
           | Consts.Undefined =>
               if String.isPrefix "boolify'" f
                  then ( boolifyInsert (String.extract (f, 8, NONE))
                       ; ppAppQuad ("call", ppQ f, ppTyAnti ty, ppExpression a,
                                    ppS "@{theory}")
                       )
               else raise Fail ("ppExpression, undefined 1-arg: " ^ f)
           | _ =>  raise Fail ("ppExpression, 1-arg: " ^ f))
      | Term.Comb ("==", _, [a, b]) =>
          ppAppPair ("eq", ppExpression a, ppExpression b)
      | Term.Comb (",", _, [_, _]) =>
          ppApp ("tp", ppList (List.map ppExpression (listOfTuple t)))
      | Term.Comb (":", _, [_, _]) =>
          ppL (2,
               [ppS "cc", ppList (List.map ppExpression (Term.destConcats t))])
      | Term.Comb ("^", ty, [a, b]) =>
         (case Types.dest ty of
             Type.Other "bitstring" =>
               ppAppTriple ("bop", ppS "Rep", ppExpression b, ppExpression a)
           | _ =>
               ppAppTriple ("rep", ppExpression a, ppExpression b, ppTyAnti ty))
      | Term.Comb (f, ty, l as [a, b]) =>
         (case ppRecord (f, ty, l) of
            SOME p => p
          | _ => ppAppTriple ("bop", ppS (ppBop f), ppExpression a,
                              ppExpression b))
      | Term.Comb (f, ty, l) =>
         (Option.valOf (ppRecord (f, ty, l))
          handle Option.Option => raise Fail ("ppExpression: " ^ f))
      | _ => (pp (PolyML.prettyRepresentation (t, 40))
              ; raise Fail "ppExpression: bad match")
   and ppMatch (m, cases) =
      ppAppTriple ("cs", ppExpression m, ppList (List.map ppCase cases),
                   ppS "@{context}")
   and ppCase t =
      case t of
        Term.Comb ("case", _,
           [a as Term.Abs (_, _, Term.Comb (",", _, [_, _]))]) =>
           (case Term.destAbs a of
              (_, Term.Comb (",", _, [pat, c])) =>
                 ppPair (ppExpression pat, ppExpression c)
            | _ => raise Fail "ppCase: abs")
      | Term.Comb ("case", _, [Term.Comb (",", _, [pat, c])]) =>
          ppPair (ppExpression pat, ppExpression c)
      | _ => raise Fail "ppCase"
   and ppRecord (f, ty, l) =
      if Tag.isRecord f
         then SOME (ppAppTriple
                      ("record", ppQ (Type.destConstType (Types.expand ty)),
                       ppList (List.map ppExpression l), ppS "@{theory}"))
      else NONE

   fun ppDefinition (s, recursive, t) =
      let
         fun ppName c = if PP.isSExp() then c else "val () = " ^ c
         val () = currentDefinition := s
      in
         if recursive then
            let
               val (v, b) = Term.destAbs t
            in
               (s,
                ppAppTriple (ppName "function", ppQ s, ppExpression v,
                             ppExpression b))
            end
         else ("", ppAppPair (ppName "def", ppQ s, ppExpression t))
      end

   fun ppDefinitions conv =
      List.mapPartial (Option.compose (ppDefinition, conv))
         (Consts.listDefinitions ())

end (* HolPP *)

(* ------------------------------------------------------------------------
   Export L3 specifications to HOL4
   ------------------------------------------------------------------------ *)

signature IsabelleExport =
sig
   val spec : string * string -> unit
   val monadicExport : bool -> unit
   val export : string -> unit
end

structure IsabelleExport :> IsabelleExport =
struct

local
   val monadic_export = ref false
in
   fun monadicExport b = monadic_export := b
   fun isMonadicExport () = !monadic_export
end

local
   fun noFreeVars tm =
      List.null (List.filter (not o Lib.equal "_" o fst) (Term.freeVars tm))
   val monadTerm =
      fn Term.Comb ("m'const", _, [_]) => true
       | Term.Comb ("m'bind", _, [_]) => true
       | Term.Comb ("m'read", _, [_]) => true
       | Term.Comb ("m'write", _, [_]) => true
       | Term.Comb ("m'extend", _, [_]) => true
       | Term.Comb ("m'unextend", _, [_]) => true
       | Term.Var ("_", _) => false
       | Term.Var _ => true
       | _ => false
   fun isOkay tm =
      if isMonadicExport ()
         then noFreeVars tm
      else case Term.findTerm monadTerm tm of
             SOME t => (print "\n"
                        ; Lib.pp (PolyML.prettyRepresentation (t, 10))
                        ; false)
           | NONE => true
   val sConv = Convert.simpConv o Convert.recordMatchConv o
               Convert.numericMatchConv o Convert.boolMatchConv o
               Matches.boolifyMatches
   fun popt c b a = print (if b then a else c)
   val popt0 = popt ""
in
   fun conv () =
      let
         val width = 44
         val (mutable, s) = Monad.init ()
         val sty = Type.mkConstType s
         val mdfy = Monadify.monadifyDefn (mutable, sty)
         fun transform (name, def, recursive) =
            let
               val m = mdfy (name, def, recursive)
               val d = if not (isMonadicExport ()) andalso
                          Monad.isMonadic (name, Term.primTypeOf def)
                          then Monadify.deMonadifyDefn sty m
                       else m
            in
               sConv d
            end
      in
         fn {user, name, def, recursive, ...} : Consts.defn =>
            let
               fun hasPrefix x = String.isPrefix x name
               val x = List.tabulate (width - String.size name, K #".")
                       handle General.Size => []
            in
               print (name ^ " " ^ String.implode x ^ " ");
               if hasPrefix "m'"
                  then NONE before printn "skip."
               else if user
                  then let
                          val r = transform (name, def, recursive)
                          val ok = isOkay r
                          val isfun =
                             Monad.isFunctional (name, Term.primTypeOf def)
                          val () = popt "bad" ok "ok"
                          val () = popt0 recursive "-rec"
                          val () = popt0 isfun "-fun"
                          val () = printn "."
                       in
                          SOME (name, recursive, r)
                       end
               else SOME (name, recursive, sConv def) before printn "sys."
            end
      end
end

fun isabelleBoiler name =
   let
      val name = if name = "" then "Screen" else name
      val date = Date.fmt "%x" (Date.fromTimeLocal (Time.now ()))
   in
     ([PP.ppS ("(* " ^ name ^ ".thy - generated by L3 - " ^ date ^ " *)\n"),
       PP.ppS ("theory " ^ name ^ "\n"),
       PP.ppS "imports \"$ISABELLE_HOME/src/HOL/Word/Word\" \"L3_Lib\"\n",
       PP.ppS "begin\n\n",
       PP.ppS "ML_file \"$ISABELLE_HOME/src/HOL/Word/Tools/word_lib.ML\"\n",
       PP.ppS "ML_file \"L3.ML\"\n\n"],
      [PP.ppS "end"])
   end

fun out dir s e =
   PP.savePP
      (OS.Path.joinDirFile
          {dir = dir, file = OS.Path.joinBaseExt {base = s, ext = SOME e}})

val newline_sep = Lib.mapSeparate I [PP.ppS "\n"]
fun termLine s =
   if s = "" then NONE
   else SOME (PP.ppS ("termination " ^ s ^ " by lexicographic_order\n"))


fun hasQty x =
   case x of
      PolyML.PrettyString "qTy" => true
    | PolyML.PrettyBlock (_, _, _, l) => List.exists hasQty l
    | _ => false

fun export path =
   let
      val {file = name, dir} = OS.Path.splitDirFile path
      val out = out dir
      val st = name ^ "_state"
      val () = Monad.stateName st
      val cnv = conv ()
      fun def_boiler x =
         [PP.ppS "\nML \\<open>\nlocal", PP.ppB (1, 2),
          PP.ppS "open L3", PP.ppB (1, 0)] @
         (if List.exists hasQty x
             then [PP.ppS ("val qTy = @{typ " ^ st ^ "}"), PP.ppB (1, 0)]
          else []) @ [PP.ppS "in\n"] @ x @ [PP.ppS "end\n\\<close>\n"]
      val (terms, defs) =
         (List.mapPartial termLine ##
          (List.concat o List.map (def_boiler o Lib.singleton)))
            (ListPair.unzip (IsaPP.ppDefinitions cnv))
      val tys = newline_sep (IsaPP.ppTypeDefs ())
      val bl = IsaPP.ppBoolifyList ()
      val l = tys @ IsaPP.ppTypeCasts name @ bl @ defs @ terms
      val (head, foot) = isabelleBoiler name
   in
      PP.ppWidth := 100
      ; (if name = "" then PP.savePP "" else out name "thy") (head @ l @ foot)
      ; PP.ppWidth := 74
      ; printn "Done."
   end

fun spec (specfiles, name) =
   let
      val b = Parser.raiseErrors NONE
      val _ = Parser.raiseErrors (SOME true)
      val err = (Runtime.LoadF specfiles; NONE) handle exc => SOME exc
   in
      case err of
         SOME exc => (print "Export aborted.\n"; raise exc)
       | NONE => (PP.sExpExport false; export name)
      ; General.ignore (Parser.raiseErrors (SOME b))
   end

end (* structure IsabelleExport *)
