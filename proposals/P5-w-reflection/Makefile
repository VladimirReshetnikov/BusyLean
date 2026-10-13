.PHONY: test audit lean pdf

test:
	python3 python/test_reference.py --json evidence/python_tests.json

audit:
	python3 scripts/source_audit.py

lean:
	python3 scripts/check_lean.py

pdf:
	bash scripts/build_pdf.sh
