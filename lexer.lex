datatype tok = Name of string
             | EName of string
             | Num of string
             | String of string
             | Reserved of string
             | Symbol of string
             | Other of string

type lexresult = int * tok

fun incr r = (r := !r + 1);
fun decr r = (r := !r - 1);

val linenum = ref 1

val comment_line = ref 0
val comment_depth = ref 0

local
   fun un [] = []
     | un [#"\""] = []
     | un (#"\\" :: #"\\" :: t) = #"\\" :: un t
     | un (#"\\" :: #"t" :: t) = #"\t" :: un t
     | un (#"\\" :: #"n" :: t) = #"\n" :: un t
     | un (#"\\" :: #"\"" :: t) = #"\"" :: un t
     | un (h::t) = h :: un t
in
   val unescape = String.implode o un o tl o String.explode
end

fun e (s, n) = String.translate (fn #"_" => "" | c => String.str c)
                 (String.extract (s, n, NONE))

val eof = fn () => (~1, Other "EOF")

%%

%s comment;

%structure Lex

alpha = [A-Za-z];
alphanum = [A-Za-z0-9_\\!$];
bin = [0-1];
dec = [0-9];
hex = [0-9A-Fa-f];
binary = {bin} ("_"?{bin})*;
decimal = {dec} ("_"?{dec})*;
hexadecimal = "x"{hex} ("_"?{hex})*;
mergeless = [',\;\\_[(){}\.];
symbol = [-!@$%^&*#+=|:~`<>?/];
ast = "@"[1-9][0-9]*;
ws = [\ \t];

%%

<INITIAL> \n             => ( incr linenum; lex() );
<INITIAL> {ws}+          => ( lex() );
<INITIAL> "--"[^\n]*     => ( lex() );
<INITIAL> "{-"           => ( comment_depth := 1;
                              comment_line := !linenum;
                              YYBEGIN comment; lex() );

<INITIAL> "if"        | "then"    | "else"      |
          "match"     | "case"    |
          "when"      | "for"     | "foreach"   | "do"       |
          "type"      | "record"  | "construct" | "register" |
          "var"       | "declare" | "exception" |
          "clear"     | "pattern" | "patterns"  |
          "component" | "assign"  | "define"    |
          "return"    | "nothing" | "UNKNOWN"   |
          "UNK!"      | "RAZ!"    | "RAO!"      |
          "set"       | "in"      | "notin"     | "insert"   | "list" |
          "true"      | "false"   | "not"       | "or"       | "and"  |
          "div"       | "mod"     | "quot"      | "rem"      |
          "fields"    | "tokens"  | "splitl"    | "splitr"
          => ( (!linenum, Reserved yytext) );

<INITIAL> "0"[wnis]"d"{decimal}   => ( (!linenum, Num (e (yytext, 1))) );
<INITIAL> "0"[wnis]"b"{binary}    => ( (!linenum, Num (e (yytext, 1))) );
<INITIAL> "0"[wnis]{hexadecimal}  => ( (!linenum, Num (e (yytext, 1))) );
<INITIAL> "0"[wni]{decimal}       => ( (!linenum,
                                        Num
                                         (String.str (String.sub (yytext, 1)) ^
                                          "?" ^ e (yytext, 2))) );
<INITIAL> "0s"{binary}            => ( (!linenum, Num ("sb" ^ e (yytext, 2))) );

<INITIAL> "0d"{decimal}           => ( (!linenum, Num ("?" ^ e (yytext, 1))) );
<INITIAL> "0b"{binary}            => ( (!linenum, Num ("?" ^ e (yytext, 1))) );
<INITIAL> "0"{hexadecimal}        => ( (!linenum, Num ("?" ^ e (yytext, 1))) );

<INITIAL> {decimal}               => ( (!linenum, Num ("??" ^ e (yytext, 0))) );

<INITIAL> "#\"".["]               => ( (!linenum,
                                        String
                                          ("#" ^ String.extract
                                                    (yytext, 2, SOME 1))) );
<INITIAL> "#"{alpha}{alphanum}*    => ( (!linenum, EName yytext) );
<INITIAL> {alpha}{alphanum}*{ast}? => ( (!linenum, Name yytext) );
<INITIAL> ["]([^"] | "\\"["])*["]  => ( (!linenum,
                                         String ("\"" ^ unescape yytext)) );
<INITIAL> "."*                     => ( (!linenum, Symbol yytext) );
<INITIAL> "]"                      => ( (!linenum, Symbol "]") );
<INITIAL> {mergeless}              => ( (!linenum, Symbol yytext) );
<INITIAL> {symbol}+                => ( (!linenum, Symbol yytext) );
<INITIAL> .                        => ( (!linenum, Other yytext) );

<comment> \n     => ( incr linenum; lex() );
<comment> "{-"   => ( incr comment_depth; lex() );
<comment> "-}"   => ( decr comment_depth;
                      if 0 < !comment_depth
                        then lex()
                      else (YYBEGIN INITIAL; lex()) );
<comment> .      => ( lex() );
