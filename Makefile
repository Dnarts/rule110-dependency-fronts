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

.PHONY: verify paper-v2 package-v2
verify:
	@mkdir -p build
	python3 scripts/build.py > build/verify.log || { tail -100 build/verify.log; exit 1; }
	grep -Fx "'Rails.essential_iff' depends on axioms: [propext, Classical.choice, Quot.sound]" build/verify.log

paper-v2:
	cd paper/v2 && for lang in en ru zh; do latexmk -xelatex -halt-on-error -interaction=nonstopmode "$$lang.tex" || exit 1; done

package-v2: paper-v2
	python3 scripts/package_v2.py

.PHONY: verify-continuation paper-continuation
verify-continuation:
	python3 continuation/scripts/check_package.py
	python3 continuation/scripts/check_finite.py
	python3 continuation/scripts/verify_lean.py

paper-continuation:
	cd continuation/paper && latexmk -xelatex -interaction=nonstopmode -halt-on-error rule110-continuation-en.tex
