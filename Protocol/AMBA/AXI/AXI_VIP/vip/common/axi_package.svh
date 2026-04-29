`ifndef AXI_PACKAGE_SVH
`define AXI_PACKAGE_SVH

package axi_package;
    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "axi_define.svh"
    `include "axi_interface.sv"
    `include "axi_seq_item.sv"
    `include "axi_driver_base.sv"
    `include "axi_monitor_base.sv"
    `include "axi_master_driver.sv"
    `include "axi_master_monitor.sv"
    `include "axi_slave_driver.sv"
    `include "axi_slave_monitor.sv"
    `include "axi_agent_base.sv"
    `include "axi_master_agent.sv"
    `include "axi_slave_agent.sv"
    `include "axi_scoreboard.sv"
    `include "axi_coverage.sv"
    `include "axi_env.sv"

    `include "axi_master_seq.sv"
    `include "axi_basic_rw_test.sv"

endpackage

`endif
