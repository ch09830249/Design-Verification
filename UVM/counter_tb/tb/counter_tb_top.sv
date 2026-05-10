// =============================================================================
// File : counter_tb_top.sv
// Desc : Top-level testbench - instantiates DUT + interface, starts UVM
// =============================================================================
`timescale 1ns/1ps

// UVM package
import uvm_pkg::*;
`include "uvm_macros.svh"

// TB files (compiled separately via -f option, but `include for single-file run)
`include "counter_if.sv"
`include "counter_seq_item.sv"
`include "counter_sequencer.sv"
`include "counter_driver.sv"
`include "counter_monitor.sv"
`include "counter_scoreboard.sv"
`include "counter_agent.sv"
`include "counter_env.sv"
`include "counter_sequences.sv"
`include "counter_vseq.sv"
`include "counter_tests.sv"

module counter_tb_top;

    // -------------------------------------------------------------------------
    // Clock generation
    // -------------------------------------------------------------------------
    logic clk;
    initial clk = 0;
    always #5 clk = ~clk;  // 100 MHz

    // -------------------------------------------------------------------------
    // Interface + DUT
    // -------------------------------------------------------------------------
    counter_if dut_if (.clk(clk));

    counter dut (
        .clk       (clk),
        .rst_n     (dut_if.rst_n),
        .reverse   (dut_if.reverse),
        .min_val   (dut_if.min_val),
        .max_val   (dut_if.max_val),
        .count     (dut_if.count),
        .direction (dut_if.direction)
    );

    // -------------------------------------------------------------------------
    // UVM config db + run
    // -------------------------------------------------------------------------
    initial begin
        uvm_config_db #(virtual counter_if)::set(null, "uvm_test_top.*", "vif", dut_if);
        run_test();  // test name supplied via +UVM_TESTNAME=
    end

    // -------------------------------------------------------------------------
    // Dump waveforms  (Cadence SimVision .shm format)
    //   $shm_open  - creates/opens the SHM database directory
    //   $shm_probe - selects what to record:
    //                "A"  = all signals in the scope passed as first arg
    //                "S"  = include sub-scopes recursively
    //                "AC" = include memories/arrays
    //   Passing the module handle as first arg scopes the probe to the DUT
    //   and testbench top together so nothing is missed.
    // -------------------------------------------------------------------------
    initial begin
        // Open the waveform database (creates counter_waves.shm/)
        $shm_open("counter_waves.shm");

        // Probe all signals (A) in all scopes recursively (S),
        // including packed/unpacked arrays and memories (C)
        $shm_probe(counter_tb_top, "ASC");
    end

    // -------------------------------------------------------------------------
    // Timeout watchdog
    // -------------------------------------------------------------------------
    initial begin
        #5_000_000;
        `uvm_fatal("TIMEOUT", "Simulation timeout - 5 ms elapsed")
    end

endmodule : counter_tb_top
