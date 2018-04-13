#############################################################################
##  v      #                   The Coq Proof Assistant                     ##
## <O___,, #                INRIA - CNRS - LIX - LRI - PPS                 ##
##   \VV/  #                                                               ##
##    //   #  Makefile automagically generated by coq_makefile V8.6.1      ##
#############################################################################

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile -f _CoqProject -o Makefile.coq 
#

.DEFAULT_GOAL := all

# This Makefile may take arguments passed as environment variables:
# COQBIN to specify the directory where Coq binaries resides;
# TIMECMD set a command to log .v compilation time;
# TIMED if non empty, use the default time command as TIMECMD;
# ZDEBUG/COQDEBUG to specify debug flags for ocamlc&ocamlopt/coqc;
# DSTROOT to specify a prefix to install path.
# VERBOSE to disable the short display of compilation rules.

VERBOSE?=
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)

# Here is a hack to make $(eval $(shell works:
define donewline


endef
includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
$(call includecmdwithout@,$(COQBIN)coqtop -config)

TIMED?=
TIMECMD?=
STDTIME?=/usr/bin/time -f "$* (user: %U mem: %M ko)"
TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))

vo_to_obj = $(addsuffix .o,\
  $(filter-out Warning: Error:,\
  $(shell $(COQBIN)coqtop -q -noinit -batch -quiet -print-mod-uid $(1))))

##########################
#                        #
# Libraries definitions. #
#                        #
##########################

OCAMLLIBS?=-I "src/lib"\
  -I "src/spells"\
  -I "src"
COQLIBS?=\
  -Q "theories" Magic\
  -I "src/lib"\
  -I "src/spells"\
  -I "src"
COQCHKLIBS?=\
  -R "theories" Magic
COQDOCLIBS?=\
  -R "theories" Magic

##########################
#                        #
# Variables definitions. #
#                        #
##########################


OPT?=
COQDEP?="$(COQBIN)coqdep" -c
COQFLAGS?=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
COQCHKFLAGS?=-silent -o
COQDOCFLAGS?=-interpolate -utf8
COQC?=$(TIMER) "$(COQBIN)coqc"
GALLINA?="$(COQBIN)gallina"
COQDOC?="$(COQBIN)coqdoc"
COQCHK?="$(COQBIN)coqchk"
COQMKTOP?="$(COQBIN)coqmktop"

COQSRCLIBS?=-I "$(COQLIB)kernel" \
-I "$(COQLIB)lib" \
-I "$(COQLIB)library" \
-I "$(COQLIB)parsing" \
-I "$(COQLIB)pretyping" \
-I "$(COQLIB)interp" \
-I "$(COQLIB)printing" \
-I "$(COQLIB)intf" \
-I "$(COQLIB)proofs" \
-I "$(COQLIB)tactics" \
-I "$(COQLIB)tools" \
-I "$(COQLIB)ltacprof" \
-I "$(COQLIB)toplevel" \
-I "$(COQLIB)stm" \
-I "$(COQLIB)grammar" \
-I "$(COQLIB)config" \
-I "$(COQLIB)ltac" \
-I "$(COQLIB)engine" \
 \
  -I "$(COQLIB)/plugins/btauto" \
  -I "$(COQLIB)/plugins/cc" \
  -I "$(COQLIB)/plugins/decl_mode" \
  -I "$(COQLIB)/plugins/derive" \
  -I "$(COQLIB)/plugins/extraction" \
  -I "$(COQLIB)/plugins/firstorder" \
  -I "$(COQLIB)/plugins/fourier" \
  -I "$(COQLIB)/plugins/funind" \
  -I "$(COQLIB)/plugins/ltac" \
  -I "$(COQLIB)/plugins/micromega" \
  -I "$(COQLIB)/plugins/nsatz" \
  -I "$(COQLIB)/plugins/omega" \
  -I "$(COQLIB)/plugins/quote" \
  -I "$(COQLIB)/plugins/romega" \
  -I "$(COQLIB)/plugins/rtauto" \
  -I "$(COQLIB)/plugins/setoid_ring" \
  -I "$(COQLIB)/plugins/ssrmatching" \
  -I "$(COQLIB)/plugins/syntax" \
  -I "$(COQLIB)/plugins/xml"
ZFLAGS=$(OCAMLLIBS) $(COQSRCLIBS) -I $(CAMLP4LIB)

CAMLC?=$(OCAMLFIND) ocamlc -c -rectypes -thread
CAMLOPTC?=$(OCAMLFIND) opt -c -rectypes -thread
CAMLLINK?=$(OCAMLFIND) ocamlc -rectypes -thread
CAMLOPTLINK?=$(OCAMLFIND) opt -rectypes -thread
CAMLDEP?=$(OCAMLFIND) ocamldep -slash -ml-synonym .ml4 -ml-synonym .mlpack
CAMLLIB?=$(shell $(OCAMLFIND) printconf stdlib)
GRAMMARS?=grammar.cma
ifeq ($(CAMLP4),camlp5)
CAMLP4EXTEND=pa_extend.cmo q_MLast.cmo pa_macro.cmo
else
CAMLP4EXTEND=
endif
PP?=-pp '$(CAMLP4O) -I $(CAMLLIB) -I $(COQLIB)/grammar compat5.cmo \
  $(CAMLP4EXTEND) $(GRAMMARS) $(CAMLP4OPTIONS) -impl'

##################
#                #
# Install Paths. #
#                #
##################

ifdef USERINSTALL
XDG_DATA_HOME?="$(HOME)/.local/share"
COQLIBINSTALL=$(XDG_DATA_HOME)/coq
COQDOCINSTALL=$(XDG_DATA_HOME)/doc/coq
else
COQLIBINSTALL="${COQLIB}user-contrib"
COQDOCINSTALL="${DOCDIR}user-contrib"
COQTOPINSTALL="${COQLIB}toploop"
endif

######################
#                    #
# Files dispatching. #
#                    #
######################

VFILES:=theories/Wand.v

ifneq ($(filter-out archclean clean cleanall printenv,$(MAKECMDGOALS)),)
-include $(addsuffix .d,$(VFILES))
else
ifeq ($(MAKECMDGOALS),)
-include $(addsuffix .d,$(VFILES))
endif
endif

.SECONDARY: $(addsuffix .d,$(VFILES))

VO=vo
VOFILES:=$(VFILES:.v=.$(VO))
VOFILES0=$(patsubst theories/%,%,$(filter theories/%,$(VOFILES)))
VFILES0=$(patsubst theories/%,%,$(filter theories/%,$(VFILES)))
GLOBFILES:=$(VFILES:.v=.glob)
GFILES:=$(VFILES:.v=.g)
HTMLFILES:=$(VFILES:.v=.html)
GHTMLFILES:=$(VFILES:.v=.g.html)
OBJFILES=$(call vo_to_obj,$(VOFILES))
ALLNATIVEFILES=$(OBJFILES:.o=.cmi) $(OBJFILES:.o=.cmo) $(OBJFILES:.o=.cmx) $(OBJFILES:.o=.cmxs)
NATIVEFILES=$(foreach f, $(ALLNATIVEFILES), $(wildcard $f))
NATIVEFILES0=$(patsubst theories/%,%,$(filter theories/%,$(NATIVEFILES)))
ML4FILES:=src/magic.ml4

ifneq ($(filter-out archclean clean cleanall printenv,$(MAKECMDGOALS)),)
-include $(addsuffix .d,$(ML4FILES))
else
ifeq ($(MAKECMDGOALS),)
-include $(addsuffix .d,$(ML4FILES))
endif
endif

.SECONDARY: $(addsuffix .d,$(ML4FILES))

MLFILES:=src/lib/collections.ml\
  src/lib/basics.ml\
  src/lib/coqterms.ml\
  src/lib/printing.ml\
  src/lib/hofs.ml\
  src/lib/debruijn.ml\
  src/lib/substitution.ml\
  src/spells/sectumsempra.ml\
  src/spells/levicorpus.ml

ifneq ($(filter-out archclean clean cleanall printenv,$(MAKECMDGOALS)),)
-include $(addsuffix .d,$(MLFILES))
else
ifeq ($(MAKECMDGOALS),)
-include $(addsuffix .d,$(MLFILES))
endif
endif

.SECONDARY: $(addsuffix .d,$(MLFILES))

MLPACKFILES:=src/wand.mlpack

ifneq ($(filter-out archclean clean cleanall printenv,$(MAKECMDGOALS)),)
-include $(addsuffix .d,$(MLPACKFILES))
else
ifeq ($(MAKECMDGOALS),)
-include $(addsuffix .d,$(MLPACKFILES))
endif
endif

.SECONDARY: $(addsuffix .d,$(MLPACKFILES))

MLIFILES:=src/lib/collections.mli\
  src/lib/basics.mli\
  src/lib/coqterms.mli\
  src/lib/printing.mli\
  src/lib/hofs.mli\
  src/lib/debruijn.mli\
  src/lib/substitution.mli\
  src/spells/sectumsempra.mli\
  src/spells/levicorpus.mli

ifneq ($(filter-out archclean clean cleanall printenv,$(MAKECMDGOALS)),)
-include $(addsuffix .d,$(MLIFILES))
else
ifeq ($(MAKECMDGOALS),)
-include $(addsuffix .d,$(MLIFILES))
endif
endif

.SECONDARY: $(addsuffix .d,$(MLIFILES))

ALLCMOFILES:=$(ML4FILES:.ml4=.cmo) $(MLFILES:.ml=.cmo) $(MLPACKFILES:.mlpack=.cmo)
CMOFILES=$(filter-out $(addsuffix .cmo,$(foreach lib,$(MLLIBFILES:.mllib=_MLLIB_DEPENDENCIES) $(MLPACKFILES:.mlpack=_MLPACK_DEPENDENCIES),$($(lib)))),$(ALLCMOFILES))
CMOFILESINC=$(filter $(wildcard src/lib/*),$(CMOFILES)) $(filter $(wildcard src/spells/*),$(CMOFILES)) $(filter $(wildcard src/*),$(CMOFILES)) 
CMXFILES=$(CMOFILES:.cmo=.cmx)
OFILES=$(CMXFILES:.cmx=.o)
CMIFILES=$(sort $(ALLCMOFILES:.cmo=.cmi) $(MLIFILES:.mli=.cmi))
CMIFILESINC=$(filter $(wildcard src/lib/*),$(CMIFILES)) $(filter $(wildcard src/spells/*),$(CMIFILES)) $(filter $(wildcard src/*),$(CMIFILES)) 
CMXSFILES=$(CMXFILES:.cmx=.cmxs)
CMXSFILESINC=$(filter $(wildcard src/lib/*),$(CMXSFILES)) $(filter $(wildcard src/spells/*),$(CMXSFILES)) $(filter $(wildcard src/*),$(CMXSFILES)) 
ifeq '$(HASNATDYNLINK)' 'true'
HASNATDYNLINK_OR_EMPTY := yes
else
HASNATDYNLINK_OR_EMPTY :=
endif

#######################################
#                                     #
# Definition of the toplevel targets. #
#                                     #
#######################################

all: $(VOFILES) $(CMOFILES) $(if $(HASNATDYNLINK_OR_EMPTY),$(CMXSFILES)) 

mlihtml: $(MLIFILES:.mli=.cmi)
	 mkdir $@ || rm -rf $@/*
	$(OCAMLFIND) ocamldoc -html -rectypes -d $@ -m A $(ZDEBUG) $(ZFLAGS) $(^:.cmi=.mli)

all-mli.tex: $(MLIFILES:.mli=.cmi)
	$(OCAMLFIND) ocamldoc -latex -rectypes -o $@ -m A $(ZDEBUG) $(ZFLAGS) $(^:.cmi=.mli)

quick: $(VOFILES:.vo=.vio)

vio2vo:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -schedule-vio2vo $(J) $(VOFILES:%.vo=%.vio)
checkproofs:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -schedule-vio-checking $(J) $(VOFILES:%.vo=%.vio)
gallina: $(GFILES)

html: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html $(COQDOCLIBS) -d html $(VFILES)

gallinahtml: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html -g $(COQDOCLIBS) -d html $(VFILES)

all.ps: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -ps $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all-gal.ps: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -ps -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all.pdf: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -pdf $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all-gal.pdf: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -pdf -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

validate: $(VOFILES)
	$(COQCHK) $(COQCHKFLAGS) $(COQCHKLIBS) $(notdir $(^:.vo=))

beautify: $(VFILES:=.beautified)
	for file in $^; do mv $${file%.beautified} $${file%beautified}old && mv $${file} $${file%.beautified}; done
	@echo 'Do not do "make clean" until you are sure that everything went well!'
	@echo 'If there were a problem, execute "for file in $$(find . -name \*.v.old -print); do mv $${file} $${file%.old}; done" in your shell/'

.PHONY: all archclean beautify byte clean cleanall gallina gallinahtml html install install-doc install-natdynlink install-toploop opt printenv quick uninstall userinstall validate vio2vo

#####################################
#                                   #
# Ad-hoc implicit rules for mlpack. #
#                                   #
#####################################

$(addsuffix .cmx,$(filter $(basename $(MLFILES)),$(src/wand_MLPACK_DEPENDENCIES))): %.cmx: %.ml
	$(SHOW)'CAMLOPT -c -for-pack Wand $<'
	$(HIDE)$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) -for-pack Wand $<

$(addsuffix .cmx,$(filter $(basename $(ML4FILES)),$(src/wand_MLPACK_DEPENDENCIES))): %.cmx: %.ml4
	$(SHOW)'CAMLOPT -c -pp -for-pack Wand $<'
	$(HIDE)$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) -for-pack Wand $(PP) -impl $<

####################
#                  #
# Special targets. #
#                  #
####################

byte:
	$(MAKE) all "OPT:=-byte"

opt:
	$(MAKE) all "OPT:=-opt"

userinstall:
	+$(MAKE) USERINSTALL=true install

install-natdynlink:
	install -d "$(DSTROOT)"$(COQLIBINSTALL)/Magic; \
	for i in $(CMXSFILESINC); do \
	 install -m 0755 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Magic/`basename $$i`; \
	done

install-toploop: $(MLLIBFILES:.mllib=.cmxs)
	 install -d "$(DSTROOT)"$(COQTOPINSTALL)/
	 install -m 0755 $?  "$(DSTROOT)"$(COQTOPINSTALL)/

install:$(if $(HASNATDYNLINK_OR_EMPTY),install-natdynlink)
	cd "theories" && for i in $(NATIVEFILES0) $(GLOBFILES0) $(VFILES0) $(VOFILES0); do \
	 install -d "`dirname "$(DSTROOT)"$(COQLIBINSTALL)/Magic/$$i`"; \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Magic/$$i; \
	done
	for i in $(CMIFILESINC) $(CMOFILESINC); do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Magic/`basename $$i`; \
	done

install-doc:
	install -d "$(DSTROOT)"$(COQDOCINSTALL)/Magic/html
	for i in html/*; do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQDOCINSTALL)/Magic/$$i;\
	done
	install -d "$(DSTROOT)"$(COQDOCINSTALL)/Magic/mlihtml
	for i in mlihtml/*; do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQDOCINSTALL)/Magic/$$i;\
	done

uninstall_me.sh: Makefile.coq
	echo '#!/bin/sh' > $@
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/Magic && \\\nfor i in $(CMXSFILESINC); do rm -f "`basename "$$i"`"; done && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "Magic" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/Magic && rm -f $(NATIVEFILES0) $(GLOBFILES0) $(VFILES0) $(VOFILES0) && \\\nfor i in $(CMIFILESINC) $(CMOFILESINC); do rm -f "`basename "$$i"`"; done && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "Magic" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQDOCINSTALL)/Magic \\\n' >> "$@"
	printf '&& rm -f $(shell find "html" -maxdepth 1 -and -type f -print)\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQDOCINSTALL) && find Magic/html -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQDOCINSTALL)/Magic \\\n' >> "$@"
	printf '&& rm -f $(shell find "mlihtml" -maxdepth 1 -and -type f -print)\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQDOCINSTALL) && find Magic/mlihtml -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	chmod +x $@

uninstall: uninstall_me.sh
	sh $<

.merlin:
	@echo 'FLG -rectypes' > .merlin
	@echo "B $(COQLIB)kernel" >> .merlin
	@echo "B $(COQLIB)lib" >> .merlin
	@echo "B $(COQLIB)library" >> .merlin
	@echo "B $(COQLIB)parsing" >> .merlin
	@echo "B $(COQLIB)pretyping" >> .merlin
	@echo "B $(COQLIB)interp" >> .merlin
	@echo "B $(COQLIB)printing" >> .merlin
	@echo "B $(COQLIB)intf" >> .merlin
	@echo "B $(COQLIB)proofs" >> .merlin
	@echo "B $(COQLIB)tactics" >> .merlin
	@echo "B $(COQLIB)tools" >> .merlin
	@echo "B $(COQLIB)ltacprof" >> .merlin
	@echo "B $(COQLIB)toplevel" >> .merlin
	@echo "B $(COQLIB)stm" >> .merlin
	@echo "B $(COQLIB)grammar" >> .merlin
	@echo "B $(COQLIB)config" >> .merlin
	@echo "B $(COQLIB)ltac" >> .merlin
	@echo "B $(COQLIB)engine" >> .merlin
	@echo "B /home/tringer/magic/src/lib" >> .merlin
	@echo "S /home/tringer/magic/src/lib" >> .merlin
	@echo "B /home/tringer/magic/src/spells" >> .merlin
	@echo "S /home/tringer/magic/src/spells" >> .merlin
	@echo "B /home/tringer/magic/src" >> .merlin
	@echo "S /home/tringer/magic/src" >> .merlin

clean::
	rm -f $(ALLCMOFILES) $(CMIFILES) $(CMAFILES)
	rm -f $(ALLCMOFILES:.cmo=.cmx) $(CMXAFILES) $(CMXSFILES) $(ALLCMOFILES:.cmo=.o) $(CMXAFILES:.cmxa=.a)
	rm -f $(addsuffix .d,$(MLFILES) $(MLIFILES) $(ML4FILES) $(MLLIBFILES) $(MLPACKFILES))
	rm -f $(OBJFILES) $(OBJFILES:.o=.native) $(NATIVEFILES)
	find . -name .coq-native -type d -empty -delete
	rm -f $(VOFILES) $(VOFILES:.vo=.vio) $(GFILES) $(VFILES:.v=.v.d) $(VFILES:=.beautified) $(VFILES:=.old)
	rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) all-mli.tex
	- rm -rf html mlihtml uninstall_me.sh

cleanall:: clean
	rm -f $(foreach f,$(VFILES:.v=),$(dir $(f)).$(notdir $(f)).aux)

archclean::
	rm -f *.cmx *.o

printenv:
	@"$(COQBIN)coqtop" -config
	@echo 'OCAMLFIND =	$(OCAMLFIND)'
	@echo 'PP =	$(PP)'
	@echo 'COQFLAGS =	$(COQFLAGS)'
	@echo 'COQLIBINSTALL =	$(COQLIBINSTALL)'
	@echo 'COQDOCINSTALL =	$(COQDOCINSTALL)'

Makefile.coq: _CoqProject
	mv -f $@ $@.bak
	"$(COQBIN)coq_makefile" -f $< -o $@


###################
#                 #
# Implicit rules. #
#                 #
###################

$(MLIFILES:.mli=.cmi): %.cmi: %.mli
	$(SHOW)'CAMLC -c $<'
	$(HIDE)$(CAMLC) $(ZDEBUG) $(ZFLAGS) $<

$(addsuffix .d,$(MLIFILES)): %.mli.d: %.mli
	$(SHOW)'CAMLDEP $<'
	$(HIDE)$(CAMLDEP) $(OCAMLLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

$(ML4FILES:.ml4=.cmo): %.cmo: %.ml4
	$(SHOW)'CAMLC -pp -c $<'
	$(HIDE)$(CAMLC) $(ZDEBUG) $(ZFLAGS) $(PP) -impl $<

$(filter-out $(addsuffix .cmx,$(foreach lib,$(MLPACKFILES:.mlpack=_MLPACK_DEPENDENCIES),$($(lib)))),$(ML4FILES:.ml4=.cmx)): %.cmx: %.ml4
	$(SHOW)'CAMLOPT -pp -c $<'
	$(HIDE)$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) $(PP) -impl $<

$(addsuffix .d,$(ML4FILES)): %.ml4.d: %.ml4
	$(SHOW)'CAMLDEP -pp $<'
	$(HIDE)$(CAMLDEP) $(OCAMLLIBS) $(PP) -impl "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

$(MLFILES:.ml=.cmo): %.cmo: %.ml
	$(SHOW)'CAMLC -c $<'
	$(HIDE)$(CAMLC) $(ZDEBUG) $(ZFLAGS) $<

$(filter-out $(addsuffix .cmx,$(foreach lib,$(MLPACKFILES:.mlpack=_MLPACK_DEPENDENCIES),$($(lib)))),$(MLFILES:.ml=.cmx)): %.cmx: %.ml
	$(SHOW)'CAMLOPT -c $<'
	$(HIDE)$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) $<

$(addsuffix .d,$(MLFILES)): %.ml.d: %.ml
	$(SHOW)'CAMLDEP $<'
	$(HIDE)$(CAMLDEP) $(OCAMLLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

$(filter-out $(MLLIBFILES:.mllib=.cmxs),$(MLFILES:.ml=.cmxs) $(ML4FILES:.ml4=.cmxs) $(MLPACKFILES:.mlpack=.cmxs)): %.cmxs: %.cmx
	$(SHOW)'CAMLOPT -shared -o $@'
	$(HIDE)$(CAMLOPTLINK) $(ZDEBUG) $(ZFLAGS) -shared -o $@ $<

$(MLLIBFILES:.mllib=.cmxs): %.cmxs: %.cmxa
	$(SHOW)'CAMLOPT -shared -o $@'
	$(HIDE)$(CAMLOPTLINK) $(ZDEBUG) $(ZFLAGS) -linkall -shared -o $@ $<

$(MLPACKFILES:.mlpack=.cmo): %.cmo: | %.mlpack
	$(SHOW)'CAMLC -pack -o $@'
	$(HIDE)$(CAMLLINK) $(ZDEBUG) $(ZFLAGS) -pack -o $@ $^

$(MLPACKFILES:.mlpack=.cmx): %.cmx: | %.mlpack
	$(SHOW)'CAMLOPT -pack -o $@'
	$(HIDE)$(CAMLOPTLINK) $(ZDEBUG) $(ZFLAGS) -pack -o $@ $^

$(addsuffix .d,$(MLPACKFILES)): %.mlpack.d: %.mlpack
	$(SHOW)'COQDEP $<'
	$(HIDE)$(COQDEP) $(OCAMLLIBS) -c "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

$(VOFILES): %.vo: %.v
	$(SHOW)COQC $<
	$(HIDE)$(COQC) $(COQDEBUG) $(COQFLAGS) $<

$(GLOBFILES): %.glob: %.v
	$(COQC) $(COQDEBUG) $(COQFLAGS) $<

$(VFILES:.v=.vio): %.vio: %.v
	$(COQC) -quick $(COQDEBUG) $(COQFLAGS) $<

$(GFILES): %.g: %.v
	$(GALLINA) $<

$(VFILES:.v=.tex): %.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex $< -o $@

$(HTMLFILES): %.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS) -html $< -o $@

$(VFILES:.v=.g.tex): %.g.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex -g $< -o $@

$(GHTMLFILES): %.g.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS)  -html -g $< -o $@

$(addsuffix .d,$(VFILES)): %.v.d: %.v
	$(SHOW)'COQDEP $<'
	$(HIDE)$(COQDEP) $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

$(addsuffix .beautified,$(VFILES)): %.v.beautified:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -beautify $*.v

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

