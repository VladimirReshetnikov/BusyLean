.PHONY: audit reference article verify kernel-check

audit:
	python3 scripts/static_audit.py

reference:
	python3 scripts/reference_model.py

article:
	cd article && pdflatex -interaction=nonstopmode -halt-on-error contender11.tex
	cd article && pdflatex -interaction=nonstopmode -halt-on-error contender11.tex
	cd article && pdflatex -interaction=nonstopmode -halt-on-error contender11.tex

verify:
	python3 scripts/verify_package.py

kernel-check:
	@echo "usage: python3 scripts/check_in_repo.py /path/to/BusyLean"
