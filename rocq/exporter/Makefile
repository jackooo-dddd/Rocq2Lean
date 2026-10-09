# Builds the rocq2lean-export plugin in place (no installation into the opam switch).
all: Makefile.rocq
	$(MAKE) -f Makefile.rocq

Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean
	rm -f Makefile.rocq Makefile.rocq.conf

.PHONY: all clean
