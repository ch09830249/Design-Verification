// =============================================================================
// cdc_read_agent.sv
// Read 端 Agent：Driver + Monitor + Agent
// 全部跑在 RCLK domain
// =============================================================================
`include "uvm_macros.svh"
import uvm_pkg::*;
import cdc_fifo_pkg::*;

// ─────────────────────────────────────────────────────────────────────────────
// Read Driver
// ─────────────────────────────────────────────────────────────────────────────
class fifo_read_driver extends uvm_driver #(fifo_read_item);
    `uvm_component_utils(fifo_read_driver)

    virtual cdc_fifo_if vif;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db #(virtual cdc_fifo_if)::get(
                this, "", "vif", vif))
            `uvm_fatal("RDRV", "Cannot get vif from config_db")
    endfunction

    task run_phase(uvm_phase phase);
        fifo_read_item tr;

        // 等待 reset 釋放
        @(posedge vif.RCLK iff vif.RRST_N);
        @(posedge vif.RCLK);

        forever begin
            seq_item_port.get_next_item(tr);
            drive_item(tr);
            seq_item_port.item_done();
        end
    endtask

    task drive_item(fifo_read_item tr);
        // 若 FIFO 空，等到有資料
        while (vif.read_cb.REMPTY) begin
            `uvm_info("RDRV", "FIFO empty, waiting...", UVM_HIGH)
            @(vif.read_cb);
        end

        // 透過 clocking block 驅動
        vif.read_cb.RINC <= 1'b1;
        @(vif.read_cb);

        vif.read_cb.RINC <= 1'b0;

        // 空閒週期
        repeat(tr.gap_cycles) @(vif.read_cb);
    endtask
endclass

// ─────────────────────────────────────────────────────────────────────────────
// Read Monitor
// ─────────────────────────────────────────────────────────────────────────────
class fifo_read_monitor extends uvm_monitor;
    `uvm_component_utils(fifo_read_monitor)

    virtual cdc_fifo_if vif;
    uvm_analysis_port #(fifo_read_item) ap;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ap = new("ap", this);
        if (!uvm_config_db #(virtual cdc_fifo_if)::get(
                this, "", "vif", vif))
            `uvm_fatal("MON_R", "Cannot get vif from config_db")
    endfunction

    task run_phase(uvm_phase phase);
        fifo_read_item tr;

        // 等待 reset 釋放
        @(posedge vif.RCLK iff vif.RRST_N);

        forever begin
            // 有效讀取：RINC=1 且 REMPTY=0
            // RDATA 在同一拍有效（組合邏輯輸出），#1step 確保取樣穩定值
            @(vif.read_mon_cb iff
                (vif.read_mon_cb.RINC && !vif.read_mon_cb.REMPTY));

            tr = fifo_read_item::type_id::create("rd_tr");
            tr.data = vif.read_mon_cb.RDATA;

            `uvm_info("MON_R", tr.convert2string(), UVM_MEDIUM)
            ap.write(tr);
        end
    endtask
endclass

// ─────────────────────────────────────────────────────────────────────────────
// Read Agent
// ─────────────────────────────────────────────────────────────────────────────
class cdc_read_agent extends uvm_agent;
    `uvm_component_utils(cdc_read_agent)

    fifo_read_driver  driver;
    fifo_read_monitor monitor;
    uvm_sequencer #(fifo_read_item) sequencer;

    uvm_analysis_port #(fifo_read_item) ap;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ap      = new("ap", this);
        monitor = fifo_read_monitor::type_id::create("monitor", this);

        if (get_is_active() == UVM_ACTIVE) begin
            driver    = fifo_read_driver::type_id::create("driver", this);
            sequencer = uvm_sequencer #(fifo_read_item)::type_id::create(
                            "sequencer", this);
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        if (get_is_active() == UVM_ACTIVE)
            driver.seq_item_port.connect(sequencer.seq_item_export);
        monitor.ap.connect(ap);
    endfunction
endclass
