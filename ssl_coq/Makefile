COMPCERT_DIR = "../../CompCert"
VST_DIR = "../../VST"
RAMIFYCOQ_DIR = "../../RamifyCoq"
CURRENT_DIR = "./"
-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

INCLUDE_COMPCERT = -R $(COMPCERT_DIR) compcert
INCLUDE_VST = -R $(VST_DIR) VST
INCLUDE_RAMIFYCOQ = -R $(RAMIFYCOQ_DIR) RamifyCoq
NORMAL_FLAG = $(INCLUDE_RAMIFYCOQ) $(INCLUDE_VST) $(INCLUDE_COMPCERT)
CLIGHT_FLAG = $(INCLUDE_COMPCERT) $(INCLUDE_RAMIFYCOQ)

SSL_FILES = \
  ssl_algebra.v ssl_logic.v ssl_logic_model.v ssl_shares.v ssl_examples.v neg_logic.v modal_logic.v logics_direct.v

NORMAL_FILES = \
  $(SSL_FILES:%.v=%.v)

$(NORMAL_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(NORMAL_FLAG) $(CURRENT_DIR)/$*.v

all: \
  $(NORMAL_FILES:%.v=%.vo)

depend:
	$(COQDEP) $(NORMAL_FLAG) $(NORMAL_FILES) > .depend

count:
	@wc $(NORMAL_FILES)

clean:
	@rm */*.vo */*.glob */.*.aux

.DEFAULT_GOAL := all

include .depend
