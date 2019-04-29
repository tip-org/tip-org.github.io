
TARGETS=format.html bnf.html

all: $(TARGETS)

clean:
	rm -f $(TARGETS)

.PHONY: all clean

%.html: %.md Filter
	pandoc $< -o $@ --standalone --filter ./Filter --bibliography=bibfile.bib --template ./template.html

Filter: Filter.hs
	ghc --make -O $<
