ROCQ ?= rocq

.PHONY: all check audit correspondence extract extract-test witness-test janus janus-check janus-audit janus-mutants janus-lv janus-lv-check janus-lv-audit janus-extract janus-extract-test clean

all: proofs.vo

proofs.vo: proofs.v
	$(ROCQ) c -Q . RCore proofs.v

check: proofs.vo
	$(ROCQ) check -Q . RCore RCore.proofs

# Enforces the axiom-free claim: no assumptions are introduced, every
# top-level result is audited, and every audit prints the closed-world
# verdict.  Print Assumptions alone does not fail a build, so this is
# what actually makes the claim checkable.
audit:
	ROCQ=$(ROCQ) ./tools/audit.sh

# Fails if a rule of the mechanized semantics is not documented against the
# rule it corresponds to in the published paper.  The diff between the two
# is where the defects were; this keeps it computed.
correspondence:
	./tools/check-correspondence.sh

# Extraction.  [eval_cmd_correct] and [step_fun_correct] are statements
# inside the kernel; extraction turns them into an executable whose
# correctness is the theorem rather than a test suite.
extract: proofs.vo extraction.v
	$(ROCQ) c -Q . RCore extraction.v

# Builds and runs the extracted interpreter.  Extraction that is never
# run is an unverified claim, so this is what makes it checkable.
extract-test: extract test_interp.ml
	ocamlc -w -a rcore_interp.mli rcore_interp.ml test_interp.ml -o test_interp
	./test_interp

# Runs the gap witnesses of Sect. 41A/41B (gap_witness, gap_witness2,
# odd_store, and the two constructed in difftest/) through the extracted
# interpreter and checks them against the outcomes proofs.v proves.  This
# is the executed third column of docs/gap-witness-table.md.
witness-test: extract difftest/witness_driver.ml
	ocamlc -w -a -I . rcore_interp.mli rcore_interp.ml difftest/witness_driver.ml -o witness_driver
	./witness_driver

# Janus extension (janus/janus.v): a control-token small-step semantics
# for a Janus core, with the same determinism / reversibility package.
# Kept out of [all] so the default target stays proofs.vo alone.
janus: janus/janus.vo

janus/janus.vo: janus/janus.v
	$(ROCQ) c -Q . RCore janus/janus.v

janus-check: janus/janus.vo
	$(ROCQ) check -Q . RCore RCore.janus.janus

janus-audit:
	SRC=janus/janus.v ROCQ=$(ROCQ) ./tools/audit.sh

# Break one definition at a time (on temporary copies) and check that the
# expected proof fails; see tools/janus-mutants.py and the paper's Table 5.
janus-mutants:
	ROCQ=$(ROCQ) python3 tools/janus-mutants.py

# The program-counter semantics of Lanese and Vidal (RC 2026) and its
# relation to janus/janus.v, with three errata of the published rules.
janus-lv: janus/lv.vo

janus/lv.vo: janus/lv.v janus/janus.vo
	$(ROCQ) c -Q . RCore janus/lv.v

janus-lv-check: janus/lv.vo
	$(ROCQ) check -Q . RCore RCore.janus.lv

janus-lv-audit: janus/janus.vo
	SRC=janus/lv.v ROCQ=$(ROCQ) ./tools/audit.sh

# The Janus interpreter extracted from janus.v, run forwards and backwards
# on the worked examples (janus/test_janus.ml).
janus-extract: janus/janus.vo janus/extraction.v
	$(ROCQ) c -Q . RCore janus/extraction.v

janus-extract-test: janus-extract janus/test_janus.ml
	ocamlc -w -a -I janus janus/janus_interp.mli janus/janus_interp.ml janus/test_janus.ml -o janus/test_janus
	./janus/test_janus

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux .lia.cache
	rm -f janus/*.vo janus/*.vos janus/*.vok janus/*.glob janus/.*.aux
	rm -f janus/janus_interp.ml janus/janus_interp.mli janus/*.cmi janus/*.cmo janus/test_janus
	rm -f rcore_interp.ml rcore_interp.mli *.cmi *.cmo test_interp
	rm -f witness_driver difftest/*.cmi difftest/*.cmo
