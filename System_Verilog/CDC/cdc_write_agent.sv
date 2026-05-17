// =============================================================================
// cdc_write_agent.sv
// Write 端 Agent：Driver + Monitor + Agent
// 全部跑在 WCLK domain
// =============================================================================
`include "uvm_macros.svh"
import uvm_pkg::*;
import cdc_fifo_pkg::*;

// ─────────────────────────────────────────────────────────────────────────────
// Write Driver
// ─────────────────────────────────────────────────────────────────────────────
class fifo_write_driver extends uvm_driver #(fifo_write_item);
    `uvm_component_utils(fifo_write_driver)

    virtual cdc_fifo_if vif;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db #(virtual cdc_fifo_if)::get(
                this, "", "vif", vif))
            `uvm_fatal("DRV", "Cannot get vif from config_db")
    endfunction

    task run_phase(uvm_phase phase);
        fifo_write_item tr;

        // 等待 reset 釋放
        @(posedge vif.WCLK iff vif.WRST_N);
        @(posedge vif.WCLK);

        forever begin
            seq_item_port.get_next_item(tr);
            drive_item(tr);
            seq_item_port.item_done();
        end
    endtask

    task drive_item(fifo_write_item tr);
        // 若 FIFO 滿，等到有空位
        while (vif.write_cb.WFULL) begin
            `uvm_info("WDRV", "FIFO full, waiting...", UVM_HIGH)
            @(vif.write_cb);
        end

        // 透過 clocking block 驅動（有固定 skew，無 race condition）
        vif.write_cb.WINC  <= 1'b1;
        vif.write_cb.WDATA <= tr.data;
        @(vif.write_cb);

        vif.write_cb.WINC  <= 1'b0;
        vif.write_cb.WDATA <= 'x;

        // 空閒週期（模擬非連續寫入）
        repeat(tr.gap_cycles) @(vif.write_cb);
    endtask
endclass

// ─────────────────────────────────────────────────────────────────────────────
// Write Monitor
// ─────────────────────────────────────────────────────────────────────────────
class fifo_write_monitor extends uvm_monitor;
    `uvm_component_utils(fifo_write_monitor)

    virtual cdc_fifo_if vif;
    uvm_analysis_port #(fifo_write_item) ap;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ap = new("ap", this);
        if (!uvm_config_db #(virtual cdc_fifo_if)::get(
                this, "", "vif", vif))
            `uvm_fatal("MON_W", "Cannot get vif from config_db")
    endfunction

    task run_phase(uvm_phase phase);
        fifo_write_item tr;

        // 等待 reset 釋放
        @(posedge vif.WCLK iff vif.WRST_N);

        forever begin
            // 等 WINC=1 且 WFULL=0（有效寫入）
            @(vif.write_mon_cb iff
                (vif.write_mon_cb.WINC && !vif.write_mon_cb.WFULL));

            tr = fifo_write_item::type_id::create("wr_tr");
            tr.data = vif.write_mon_cb.WDATA;

            `uvm_info("MON_W", tr.convert2string(), UVM_MEDIUM)
            ap.write(tr);
        end
    endtask
endclass

// ─────────────────────────────────────────────────────────────────────────────
// Write Agent
// ─────────────────────────────────────────────────────────────────────────────
class cdc_write_agent extends uvm_agent;
    `uvm_component_utils(cdc_write_agent)

    fifo_write_driver  driver;
    fifo_write_monitor monitor;
    uvm_sequencer #(fifo_write_item) sequencer;

    uvm_analysis_port #(fifo_write_item) ap;  // 轉發給 scoreboard

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ap       = new("ap", this);
        monitor  = fifo_write_monitor::type_id::create("monitor", this);

        if (get_is_active() == UVM_ACTIVE) begin
            driver    = fifo_write_driver::type_id::create("driver", this);
            sequencer = uvm_sequencer #(fifo_write_item)::type_id::create(
                            "sequencer", this);
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        if (get_is_active() == UVM_ACTIVE)
            driver.seq_item_port.connect(sequencer.seq_item_export);
        monitor.ap.connect(ap);
    endfunction
endclass
