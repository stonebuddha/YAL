OCB_FLAGS = -use-ocamlfind -use-menhir
OCB = ocamlbuild $(OCB_FLAGS)

all: native byte

clean:
	$(OCB) -clean

native:
	$(OCB) main.native

byte:
	$(OCB) main.byte

profile: native
	$(OCB) -tag profile main.native

debug: byte
	$(OCB) -tag debug main.byte

test: native
	./main.native

.PHONY: all clean native byte profile debug test
