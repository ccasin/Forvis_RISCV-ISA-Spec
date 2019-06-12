POLICIES ?= userType heap riscv

all: build mutants unmutated

build:
	@stack build :dpl-exe --executable-profiling

unmutated:
	@make mutant MUT=NO_MUTATIONS

ifeq ($(shell uname),Darwin)
  SED = sed -i '' '/^\#/d' 
else
  SED = sed -i '/^\#/d' 
endif

$(POLICIES):
	cpp -D$(MUT) $@.dpl > .mutants/$@.dpl
	$(SED) .mutants/$@.dpl

mutant:
	@echo 
	@echo "[37;46m"
	@echo "                                  $(MUT)"
	@echo 
	@echo "[0m"
	@mkdir -p .mutants
#	@cpp -D$(MUT) $(POL) > .mutants/$(POL)
#	@$(SED) .mutants/$(POL)
	$(MAKE) $(POLICIES)
	@(cd .mutants; time stack exec dpl-exe)

mutants:
#	@make mutant MUT=OMIT_CHECKS_ON_LOAD
	@make mutant MUT=WRONG_ORDER

# Not a bug, in the simple heap safety policy
#	@make mutant MUT=OMIT_TAGGING_ON_STORE


