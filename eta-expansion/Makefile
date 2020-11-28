SED = `which gsed || which sed`

all: theory

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

Makefile.etaexpand: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.etaexpand $(DEPS)

theory: Makefile.etaexpand
	$(MAKE) -f Makefile.etaexpand

install: theory
	$(MAKE) -f Makefile.etaexpand install

uninstall: theory
	$(MAKE) -f Makefile.etaexpand uninstall

clean: Makefile.etaexpand
	make -f Makefile.etaexpand clean

mrproper:
	rm -f Makefile.etaexpand
