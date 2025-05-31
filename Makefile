# Cours "Semantics and applications to verification"
#
# Ecole normale supérieure, Paris, France / CNRS / INRIA

.PHONY: all clean cleantest doc compress

all:
	@dune build analyzer @install

clean: cleantest
	@dune clean
	@rm -rf _build/ bin/ lib/ *~ */*~
	@rm -rf *.dot *.pdf *.svg */*.dot */*.pdf */*.svg *.tar.gz

cleantest:
	@rm -rf results

test: cleantest all
	@scripts/test.sh .

doc: all
	@dune build @doc-private

rapport: rapport.tex
	latexmk -pdf rapport.tex

compress: clean
	@tar -czvf ../boussaa.tgz --exclude=".git*" $(shell pwd)
	@mv ../boussaa.tgz .
