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
	@mkdir -p build/legacy-v1
	cd paper && latexmk -pdf -outdir=../build/legacy-v1 -interaction=nonstopmode -halt-on-error main.tex

lean:
	lean formal/rule110_complete.lean

.PHONY: verify paper-v2 package-v2
verify:
	@mkdir -p build
	python3 scripts/build.py > build/verify.log || { tail -100 build/verify.log; exit 1; }
	grep -Fx "'Rails.essential_iff' depends on axioms: [propext, Classical.choice, Quot.sound]" build/verify.log

paper-v2:
	@mkdir -p build/legacy-v2
	cd paper/v2 && for lang in en ru zh; do latexmk -outdir=../../build/legacy-v2 -xelatex -halt-on-error -interaction=nonstopmode "$$lang.tex" || exit 1; done

package-v2: paper-v2
	python3 scripts/package_v2.py

.PHONY: monograph verify-observer verify-series

verify-observer:
	python3 -B observer/verify.py
	python3 -B observer/verify_part_iii.py

verify-series: verify
	python3 -B scripts/verify_observer_lean.py
	$(MAKE) verify-observer

monograph:
	@mkdir -p build/monograph
	@if command -v tectonic >/dev/null; then \
		tectonic --untrusted --keep-logs --outdir build/monograph main.tex; \
	else \
		latexmk -xelatex -interaction=nonstopmode -halt-on-error -outdir=build/monograph main.tex; \
	fi
	cp build/monograph/main.pdf 110_OBSERVER_Preprint.pdf

.PHONY: translations monograph-en monograph-zh
translations: monograph-en monograph-zh

monograph-en monograph-zh: monograph-%:
	@mkdir -p build/monograph-$*
	@if command -v tectonic >/dev/null; then \
		tectonic --untrusted --keep-logs --outdir build/monograph-$* - < translations/$*/main.tex; \
	else \
		latexmk -xelatex -jobname=texput -interaction=nonstopmode -halt-on-error -outdir=build/monograph-$* translations/$*/main.tex; \
	fi
	cp build/monograph-$*/texput.pdf 110_OBSERVER_Preprint_$*.pdf
