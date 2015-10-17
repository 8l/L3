# Path to Poly/ML libraries
LIBPATH = ${HOME}/opt/lib

# Linux
#POLYLIB = -L${LIBPATH} -lpolymain -lpolyml
# Mac -- needs exta flags
POLYLIB = -L${LIBPATH} -lpolymain -lpolyml -lpthread -lgmp -lm -ldl -lstdc++ -Wl,-no_pie

default: bin/unquote bin/l3hol.run

clean:
	rm -f l3hol.o
	rm -f quote/unquote.o

cleanAll: clean
	rm -f lexer.lex.sml
	rm -f bin/l3hol.run
	rm -f bin/unquote

quote/unquote.o: quote/unquote.sml quote/filter.sml
	@echo "Compiling quotation filter..."
	@cd quote && poly -q < unquote.sml > /dev/null

bin/unquote: quote/unquote.o
	@echo "Making quotation filter..."
	@cc -o unquote quote/unquote.o ${POLYLIB} && mv unquote bin/

lexer.lex.sml: lexgen.sml lexer.lex
	@echo "Making lexer..."
	@echo "LexGen.lexGen \"lexer.lex\"" | poly -q --use "lexgen.sml" > /dev/null

l3hol.o: Base.sml Eval.sml Export.sml HolExport.sml IsabelleExport.sml \
         Lib.sml Parser.sml Main.sml Matches.sml SMLExport.sml \
         Stringmap.sml Stringset.sml \
         lexer.lex.sml \
         lib/IntExtra.sig lib/IntExtra.sml \
         lib/Bitstring.sig lib/Bitstring.sml \
         lib/BitsN.sig lib/BitsN.sml \
         lib/FP64.sig lib/FP64.sml \
         lib/L3.sig lib/L3.sml \
         lib/Nat.sig lib/Nat.sml
	@echo "Compiling L3..."
	@poly < Main.sml

bin/l3hol.run: l3hol.o
	@echo "Building L3..."
	@cc -o l3hol.run l3hol.o ${POLYLIB} && echo "L3 successfully built." && mv l3hol.run bin/
