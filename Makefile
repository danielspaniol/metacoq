TIMED ?=

all: template-coq checker pcuic safechecker erasure etaexpand examples

.PHONY: all template-coq checker pcuic erasure etaexpand install html clean mrproper .merlin test-suite translations

install: all
	$(MAKE) -C template-coq install
	$(MAKE) -C checker install
	$(MAKE) -C pcuic install
	$(MAKE) -C safechecker install
	$(MAKE) -C erasure install
	$(MAKE) -C eta-expansion install
	$(MAKE) -C translations install

uninstall: all
	$(MAKE) -C template-coq uninstall
	$(MAKE) -C checker uninstall
	$(MAKE) -C pcuic uninstall
	$(MAKE) -C safechecker uninstall
	$(MAKE) -C erasure uninstall
	$(MAKE) -C eta-expansion uninstall
	$(MAKE) -C translations uninstall

html: all
	"coqdoc" -toc -utf8 -interpolate -l -html \
		-R template-coq/theories MetaCoq.Template \
		-R checker/theories MetaCoq.Checker \
		-R pcuic/theories MetaCoq.PCUIC \
		-R safechecker/theories MetaCoq.SafeChecker \
		-R erasure/theories MetaCoq.Erasure \
		-R eta-expansion/theories MetaCoq.EtaExpansion \
		-R translations MetaCoq.Translations \
		-d html */theories/*.v translations/*.v

clean:
	$(MAKE) -C template-coq clean
	$(MAKE) -C checker clean
	$(MAKE) -C pcuic clean
	$(MAKE) -C safechecker clean
	$(MAKE) -C erasure clean
	$(MAKE) -C eta-expansion clean
	$(MAKE) -C examples clean
	$(MAKE) -C test-suite clean
	$(MAKE) -C translations clean

mrproper:
	$(MAKE) -C template-coq mrproper
	$(MAKE) -C pcuic mrproper
	$(MAKE) -C safechecker mrproper
	$(MAKE) -C erasure mrproper
	$(MAKE) -C eta-expansion mrproper
	$(MAKE) -C checker mrproper
	$(MAKE) -C examples mrproper
	$(MAKE) -C test-suite mrproper
	$(MAKE) -C translations mrproper

.merlin:
	$(MAKE) -C template-coq .merlin
	$(MAKE) -C pcuic .merlin
	$(MAKE) -C safechecker .merlin
	$(MAKE) -C erasure .merlin
	$(MAKE) -C checker .merlin

template-coq:
	$(MAKE) -C template-coq

pcuic: template-coq
	$(MAKE) -C pcuic

safechecker: template-coq pcuic
	$(MAKE) -C safechecker

erasure: template-coq safechecker pcuic
	$(MAKE) -C erasure

etaexpand: template-coq safechecker pcuic
	$(MAKE) -C eta-expansion

checker: template-coq
	$(MAKE) -C checker

examples: template-coq checker
	$(MAKE) -C examples

test-suite: template-coq checker safechecker erasure
	$(MAKE) -C test-suite

translations: template-coq checker
	$(MAKE) -C translations

cleanplugins:
	$(MAKE) -C template-coq cleanplugin
	$(MAKE) -C pcuic cleanplugin
	$(MAKE) -C checker cleanplugin
	$(MAKE) -C safechecker cleanplugin
	$(MAKE) -C erasure cleanplugin

ci-local:
	./configure.sh local
	$(MAKE) all test-suite TIMED=pretty-timed

ci-opam:
	# Use -v so that regular output is produced
	opam install -v -y .
	opam remove -y coq-metacoq coq-metacoq-template
