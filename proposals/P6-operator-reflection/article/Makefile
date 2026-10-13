.PHONY: all clean

all: contender7.pdf

contender7.pdf: contender7.tex ../repo_overlay/BusyLean/MetaReflection.lean \
                ../repo_overlay/BusyLean/MetaReflectionFacts.lean \
                ../repo_overlay/BusyLean/Contender7.lean \
                ../repo_overlay/BusyLean/Comparison7.lean \
                ../repo_overlay/test/MetaReflectionSmoke.lean \
                ../repo_overlay/test/Contender7Audit.lean
	pdflatex -interaction=nonstopmode -halt-on-error contender7.tex
	pdflatex -interaction=nonstopmode -halt-on-error contender7.tex

clean:
	rm -f contender7.aux contender7.log contender7.out contender7.toc
