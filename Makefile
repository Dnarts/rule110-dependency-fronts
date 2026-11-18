.PHONY: test test-ts coverage ring20 paper lean

test:
	python3 scripts/rule110_certificate.py --coverage-time 100 --coverage-period 6 --output /tmp/rule110_check100.json

test-ts:
	tsc --strict --target ES2022 --module commonjs --skipLibCheck --outDir /tmp/rule110-ts scripts/rule110_crosscheck.ts
	node /tmp/rule110-ts/rule110_crosscheck.js

coverage:
	python3 scripts/rule110_large_coverage.py --max-time 2000 --max-period 10 --output /tmp/rule110_coverage2000.json

ring20:
	python3 scripts/rule110_ring20_numpy.py

paper:
	cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

lean:
	lean formal/rule110_complete.lean
