
TARGETS=format.html bnf.html

all: $(TARGETS)

clean:
	rm -f $(TARGETS)

.PHONY: all clean

%.html: %.md
	pandoc $< -o $@ --standalone --filter ./Filter.hs --bibliography=bibfile.bib --template ./template.html

