ROCQ ?= rocq

.PHONY: all check audit clean

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

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux .lia.cache
