// 統一打包所有 VIP 模組
package axi_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    `include "axi_txn.sv"
    `include "axi_sequencer.sv"
    `include "axi_driver.sv"
    `include "axi_monitor.sv"
    `include "axi_agent.sv"
    `include "axi_env.sv"
    `include "axi_test.sv"
    `include "coverage.sv"

endpackage
