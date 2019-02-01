all: test
.PHONY: all test clean clobber

test: $(patsubst tests/%.expected,proofs/%.proof,$(shell find tests -name '*.expected'))
	-@echo '*** ALL TESTS OK ***'

proofs/%.proof: src/%.hs tests/%.expected
	mkdir -p $(dir $@)
	stack $< | diff - $(patsubst proofs/%.proof,tests/%.expected,$@)
	touch $@


clean:
	rm -rf crumbs proofs

clobber: clean
	rm -rf .stack-work
