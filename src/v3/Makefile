obj = \
	unionfind.cmo util.cmo lexer.cmo parser.cmo pp.cmo env.cmo \
	lambda.cmo tyutil.cmo tysem.cmo typing.cmo eval.cmo main.cmo
opt_obj = ${obj:.cmo=.cmx}
target = et
OCAMLC = ocamlc -g
OCAMLC_OPT = ocamlopt

CMA_LIBS = 

all: $(target) fake-ast
native: opt
opt: $(target).opt

$(target): $(obj)
	$(OCAMLC) -o $@ $(CMA_LIBS) $(obj)
	-copy $(target) $(target).exe

$(target).opt: $(opt_obj)
	$(OCAMLC_OPT) -o $@ ${CMA_LIBS:.cma=.cmax} $(opt_obj)

.PHONY: tags

tags:
	otags -vi *.ml *.mli

.SECONDARY: parser.ml lexer.ml parser.mli
.PHONY: t

%.cmo: %.ml
	$(OCAMLC) -c $<

%.cmi: %.mli
	$(OCAMLC) -c $<

%.cmx: %.ml
	$(OCAMLC_OPT) -c $<

%.ml: %.mll
	ocamllex $<

%.ml %.mli: %.mly
	ocamlyacc -v $<

# ocamldebug is stupid and needs it
fake-ast: ast.cmo

ast.cmo: ast.mli
	$(OCAMLC) -c -impl ast.mli

.deps: parser.ml lexer.ml Makefile
	ocamldep *.ml *.mli > .deps

-include .deps

clean:
	rm -f *.cmo *.cmi *.o *.cmx core $(target) $(target).opt parser.output

nuke: clean
	rm -f parser.ml parser.mli lexer.ml parser.output 
	rm -f .deps TAGS tags

count:
	wc `ls *.ml *.mli *.mly *.mll | egrep -v '(parser|lexer)\.(ml|mli)$$'`

VER := $(shell cat VERSION)
DISTDIR := et-$(VER)

dist:
	update-svn-changelog || :
	rm -rf $(DISTDIR)
	svn export . $(DISTDIR)
	-cp ChangeLog $(DISTDIR)
	$(MAKE) -C $(DISTDIR)/doc
	$(MAKE) -C $(DISTDIR)/doc dist-clean
	tar cf - $(DISTDIR) | gzip -9nf > $(DISTDIR).tar.gz
	rm -rf $(DISTDIR)

t:
	cd tests; ./run
