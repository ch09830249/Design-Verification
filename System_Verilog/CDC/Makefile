# =============================================================================
# Makefile — CDC Async FIFO Verification
# 支援 Synopsys VCS 和 Cadence Xcelium
# 用法：
#   make vcs   TEST=test_basic_rw
#   make xrun  TEST=test_full_boundary
#   make clean
# =============================================================================

UVM_HOME  ?= $(VCS_HOME)/etc/uvm
TEST      ?= test_basic_rw

# ─── 共用編譯選項 ─────────────────────────────────────────────────────────
TIMESCALE  = -timescale=1ns/1ps
DEFINES    = +define+UVM_NO_DEPRECATED

SRC = \
    async_fifo.v             \
    cdc_fifo_pkg.sv          \
    cdc_fifo_if.sv           \
    cdc_write_agent.sv       \
    cdc_read_agent.sv        \
    cdc_scoreboard.sv        \
    cdc_env_seq_tests.sv     \
    top_tb.sv

# ─── Synopsys VCS ─────────────────────────────────────────────────────────
VCS_OPTS = \
    -full64 -sverilog -ntb_opts uvm-1.2 \
    $(TIMESCALE) $(DEFINES) \
    -debug_acc+all -debug_region+cell

vcs: clean
	vcs $(VCS_OPTS) $(SRC) -o simv
	./simv +UVM_TESTNAME=$(TEST) +UVM_VERBOSITY=UVM_MEDIUM

# ─── Cadence Xcelium ──────────────────────────────────────────────────────
XRUN_OPTS = \
    -uvm -uvmhome CDNS-1.2 \
    -timescale 1ns/1ps $(DEFINES) \
    -access +rwc

xrun: clean
	xrun $(XRUN_OPTS) $(SRC) +UVM_TESTNAME=$(TEST) +UVM_VERBOSITY=UVM_MEDIUM

# ─── 跑所有 test ─────────────────────────────────────────────────────────
TESTS = test_basic_rw test_full_boundary test_asymmetric_rate \
        test_stress test_async_reset

regression_vcs: clean
	vcs $(VCS_OPTS) $(SRC) -o simv
	@for t in $(TESTS); do \
	    echo "====== Running $$t ======"; \
	    ./simv +UVM_TESTNAME=$$t +UVM_VERBOSITY=UVM_MEDIUM; \
	done

regression_xrun: clean
	@for t in $(TESTS); do \
	    echo "====== Running $$t ======"; \
	    xrun $(XRUN_OPTS) $(SRC) +UVM_TESTNAME=$$t +UVM_VERBOSITY=UVM_MEDIUM; \
	done

# ─── 清理 ─────────────────────────────────────────────────────────────────
clean:
	rm -rf simv simv.daidir csrc ucli.key *.log *.vcd xcelium.d \
	       .simvision novas.rc urgReport DVEfiles

.PHONY: vcs xrun regression_vcs regression_xrun clean
