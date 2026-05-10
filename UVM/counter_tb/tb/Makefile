# =============================================================================
# Makefile - build & run with Cadence xrun (Xcelium)
# Waveforms are dumped to counter_waves.shm/ via $shm_open/$shm_probe in the TB
# Open with SimVision:  make waves
# =============================================================================

XRUN     = xrun
RTL_DIR  = ../rtl
TB_DIR   = .
SHM_DIR  = counter_waves.shm

# xrun compile + simulate flags
XRUN_OPTS = \
    -sv \
    -uvm \
    -uvmhome CDNS-1.2 \
    -timescale 1ns/1ps \
    -access +rwc \
    -l xrun.log \
    $(RTL_DIR)/counter.v \
    $(TB_DIR)/counter_tb_top.sv

# Default test
TEST     ?= test_basic_count
SEED     ?= 1

.PHONY: all compile sim regress waves clean help

all: sim

# Compile-only check
compile:
	$(XRUN) $(XRUN_OPTS) +UVM_TESTNAME=$(TEST) -compile

# Compile + simulate  (waveforms written to $(SHM_DIR) automatically)
sim:
	$(XRUN) $(XRUN_OPTS) \
	    +UVM_TESTNAME=$(TEST) \
	    +ntb_random_seed=$(SEED) \
	    +UVM_VERBOSITY=UVM_MEDIUM

# Run all four tests sequentially
# Usage:
#   make regress                        -> seeds 1/2/3/4 per test (default)
#   make regress REGRESS_SEED=42        -> all four tests use seed 42
#   make regress SEED_BASIC=10 SEED_REV=20 SEED_CFG=30 SEED_STRESS=40
SEED_BASIC  ?= 1
SEED_REV    ?= 2
SEED_CFG    ?= 3
SEED_STRESS ?= 4

regress:
	$(MAKE) sim TEST=test_basic_count   SEED=$(if $(REGRESS_SEED),$(REGRESS_SEED),$(SEED_BASIC))
	$(MAKE) sim TEST=test_reverse       SEED=$(if $(REGRESS_SEED),$(REGRESS_SEED),$(SEED_REV))
	$(MAKE) sim TEST=test_range_change  SEED=$(if $(REGRESS_SEED),$(REGRESS_SEED),$(SEED_CFG))
	$(MAKE) sim TEST=test_stress        SEED=$(if $(REGRESS_SEED),$(REGRESS_SEED),$(SEED_STRESS))

# Open last waveform in SimVision
waves:
	@if [ ! -d "$(SHM_DIR)" ]; then \
	    echo "No waveform found - run 'make sim' first"; exit 1; \
	fi
	simvision $(SHM_DIR) &

clean:
	rm -rf xrun.log xcelium.d INCA_libs $(SHM_DIR) *.trn *.dsn

help:
	@echo "Targets:"
	@echo "  sim      - compile + run  (TEST=<name> SEED=<n>)"
	@echo "  regress  - run all 4 tests"
	@echo "             default seeds:   1/2/3/4 per test"
	@echo "             same seed all:   make regress REGRESS_SEED=42"
	@echo "             per-test seeds:  make regress SEED_BASIC=10 SEED_REV=20 SEED_CFG=30 SEED_STRESS=40"
	@echo "  compile  - compile only"
	@echo "  waves    - open waveform in SimVision"
	@echo "  clean    - remove generated files"
	@echo ""
	@echo "Tests:"
	@echo "  test_basic_count   test_reverse"
	@echo "  test_range_change  test_stress"
	@echo ""
	@echo "Waveform DB: $(SHM_DIR)  (open with SimVision)"
