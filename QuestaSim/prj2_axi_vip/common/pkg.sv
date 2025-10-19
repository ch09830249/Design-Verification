// 統一打包所有 VIP 模組
package axi_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    `include "../vip/axi_txn.sv"
    `include "../tb/axi_basic_seq.sv"
    `include "../vip/axi_sequencer.sv"
    `include "../vip/axi_driver.sv"
    `include "../vip/axi_monitor.sv"
    `include "../vip/axi_agent.sv"
    `include "../vip/axi_env.sv"
    `include "../tb/axi_test.sv"
    `include "../vip/coverage.sv"

endpackage

