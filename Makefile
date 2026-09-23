ROCQ ?= rocq

.PHONY: all check audit correspondence extract extract-test janus janus-check janus-audit clean

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

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux .lia.cache
	rm -f janus/*.vo janus/*.vos janus/*.vok janus/*.glob janus/.*.aux
	rm -f rcore_interp.ml rcore_interp.mli *.cmi *.cmo test_interp
