.PHONY: checks article clean

checks:
	./scripts/run_checks.sh

article:
	cd article && latexmk -pdf -interaction=nonstopmode -halt-on-error reflection_power_contender.tex

clean:
	cd article && latexmk -C
	rm -rf _renders contact_*.png
