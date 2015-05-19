# Makefile

OCAMLBUILD = ocamlbuild


# name of the compiled executable
#
TARGET = main


# compile either to byte code or native code
#
# uncomment only one of the two lines!
#
#all: $(TARGET).byte
all: $(TARGET).native


$(TARGET).byte:
	$(OCAMLBUILD) -use-ocamlfind $@

$(TARGET).native:
	$(OCAMLBUILD) -use-ocamlfind $@

clean:
	ocamlbuild -clean

.PHONY:all $(TARGET).byte $(TARGET).native clean
