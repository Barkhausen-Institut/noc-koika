include koika.mk

.PHONY: ocaml
ocaml:
	@true

TCU := $(wildcard tcu/TCU.lv) $(wildcard tcu/TCU.v)

configure:
	etc/configure $(filter %.v,${TCU})

$(foreach fname,$(filter %.v, $(TCU)),\
	$(eval $(call cuttlec_v_template,$(fname))))

.PHONY: tcu
tcu: $(call target_directories,$(TCU));

.PHONY: documentation
documentation:
	mkdir -p coqdoc
	coqdoc --parse-comments --html --directory ./coqdoc tcu/*.v

clean:
	rm -rf ./coqdoc
