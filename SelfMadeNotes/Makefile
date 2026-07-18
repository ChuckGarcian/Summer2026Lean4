SRC := selfStudyGroupTheory
PDF_ENGINE := xelatex
HEADER := build/header.tex
FILTER := build/filter.lua

all: $(SRC)_questions.pdf $(SRC)_full.pdf

# Version with Questions ONLY
$(SRC)_questions.pdf: $(SRC).md $(FILTER)
	pandoc $< \
	--lua-filter=$(FILTER) \
	--pdf-engine=$(PDF_ENGINE) \
	-H $(HEADER) \
	-V fontsize=11pt \
	-o $@

# Version with Questions AND Answers
$(SRC)_full.pdf: $(SRC).md $(FILTER)
	pandoc $< \
	--lua-filter=$(FILTER) \
	-M show_answers=true \
	--pdf-engine=$(PDF_ENGINE) \
	-H $(HEADER) \
	-V fontsize=11pt \
	-o $@

clean:
	rm -f *.pdf