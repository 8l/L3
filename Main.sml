datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a;

use "Export.sml";
use "HolExport.sml";
use "IsabelleExport.sml";
use "SMLExport.sml";

structure Parse =
struct
   val Term = Runtime.evalQ
end;

local
   fun main () = (TextIO.print "<< L3 >>\n"; PolyML.rootFunction ())
in
   val () = PolyML.shareCommonData main
   val () = PolyML.export ("l3hol", main)
end
