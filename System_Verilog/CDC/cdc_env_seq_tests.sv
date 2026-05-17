// =============================================================================
// cdc_env.sv
// UVM Environment：整合 write agent、read agent、scoreboard
// =============================================================================
`include "uvm_macros.svh"
import uvm_pkg::*;
import cdc_fifo_pkg::*;

class cdc_fifo_env extends uvm_env;
    `uvm_component_utils(cdc_fifo_env)

    cdc_write_agent  write_agent;
    cdc_read_agent   read_agent;
    cdc_scoreboard   scoreboard;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        write_agent = cdc_write_agent::type_id::create("write_agent", this);
        read_agent  = cdc_read_agent::type_id::create("read_agent",  this);
        scoreboard  = cdc_scoreboard::type_id::create("scoreboard",  this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Write Monitor → Scoreboard write_export
        write_agent.ap.connect(scoreboard.write_export);
        // Read Monitor  → Scoreboard read_export
        read_agent.ap.connect(scoreboard.read_export);
    endfunction
endclass


// =============================================================================
// cdc_sequences.sv
// 所有 Sequence：5 個場景 + 1 個壓力測試
// =============================================================================

// ─── Base sequence ───────────────────────────────────────────────────────────
class fifo_base_write_seq extends uvm_sequence #(fifo_write_item);
    `uvm_object_utils(fifo_base_write_seq)
    function new(string name="fifo_base_write_seq"); super.new(name); endfunction

    task write_data(logic [DATA_WIDTH-1:0] d, int gap=0);
        fifo_write_item tr = fifo_write_item::type_id::create("tr");
        start_item(tr);
        tr.data       = d;
        tr.gap_cycles = gap;
        finish_item(tr);
    endtask
endclass

class fifo_base_read_seq extends uvm_sequence #(fifo_read_item);
    `uvm_object_utils(fifo_base_read_seq)
    function new(string name="fifo_base_read_seq"); super.new(name); endfunction

    task read_one(int gap=0);
        fifo_read_item tr = fifo_read_item::type_id::create("tr");
        start_item(tr);
        tr.gap_cycles = gap;
        finish_item(tr);
    endtask
endclass

// ─── 場景 1：基本寫入後讀出（順序驗證）────────────────────────────────────
class seq_basic_write extends fifo_base_write_seq;
    `uvm_object_utils(seq_basic_write)
    rand int unsigned n;
    constraint c_n { n inside {[4:8]}; }
    function new(string name="seq_basic_write"); super.new(name); endfunction

    task body();
        `uvm_info("SEQ", $sformatf("Basic write: %0d items", n), UVM_LOW)
        for (int i = 0; i < n; i++)
            write_data(8'hA0 + i, 1);  // 固定資料便於 debug
    endtask
endclass

class seq_basic_read extends fifo_base_read_seq;
    `uvm_object_utils(seq_basic_read)
    rand int unsigned n;
    constraint c_n { n inside {[4:8]}; }
    function new(string name="seq_basic_read"); super.new(name); endfunction

    task body();
        `uvm_info("SEQ", $sformatf("Basic read: %0d items", n), UVM_LOW)
        for (int i = 0; i < n; i++)
            read_one(1);
    endtask
endclass

// ─── 場景 2：填滿 FIFO（WFULL 邊界）──────────────────────────────────────
class seq_fill_fifo extends fifo_base_write_seq;
    `uvm_object_utils(seq_fill_fifo)
    function new(string name="seq_fill_fifo"); super.new(name); endfunction

    task body();
        `uvm_info("SEQ", "Filling FIFO to full", UVM_LOW)
        // 寫入 DEPTH+2 筆，多出的應被 DUT 忽略（WFULL 保護）
        for (int i = 0; i < FIFO_DEPTH + 2; i++)
            write_data(8'hF0 + i[7:0], 0);
    endtask
endclass

class seq_drain_fifo extends fifo_base_read_seq;
    `uvm_object_utils(seq_drain_fifo)
    function new(string name="seq_drain_fifo"); super.new(name); endfunction

    task body();
        `uvm_info("SEQ", "Draining FIFO", UVM_LOW)
        for (int i = 0; i < FIFO_DEPTH; i++)
            read_one(0);
    endtask
endclass

// ─── 場景 3：空 FIFO 讀取（REMPTY 邊界）──────────────────────────────────
class seq_read_from_empty extends fifo_base_read_seq;
    `uvm_object_utils(seq_read_from_empty)
    function new(string name="seq_read_from_empty"); super.new(name); endfunction

    task body();
        // 嘗試多次讀取（driver 會等到有資料，assertion 驗證 REMPTY 期間 rptr 不動）
        `uvm_info("SEQ", "Attempting reads (FIFO should be empty initially)", UVM_LOW)
        for (int i = 0; i < 3; i++)
            read_one(0);
    endtask
endclass

// ─── 場景 4：Back-to-Back 填滿再清空（壓力）──────────────────────────────
class seq_stress_write extends fifo_base_write_seq;
    `uvm_object_utils(seq_stress_write)
    rand int unsigned rounds;
    constraint c_rounds { rounds inside {[2:4]}; }
    function new(string name="seq_stress_write"); super.new(name); endfunction

    task body();
        `uvm_info("SEQ", $sformatf("Stress write: %0d rounds", rounds), UVM_LOW)
        for (int r = 0; r < rounds; r++) begin
            // 連續填滿
            for (int i = 0; i < FIFO_DEPTH; i++)
                write_data($urandom_range(0, 255), 0);
            // 等讀端清空（靠 gap 讓讀端追上）
            repeat(FIFO_DEPTH * 4) begin
                fifo_write_item tr = fifo_write_item::type_id::create("idle");
                start_item(tr);
                tr.gap_cycles = 1;
                tr.data       = 0;  // idle 不會真的送，gap 讓時間過去
                finish_item(tr);
            end
        end
    endtask
endclass

class seq_stress_read extends fifo_base_read_seq;
    `uvm_object_utils(seq_stress_read)
    rand int unsigned rounds;
    constraint c_rounds { rounds inside {[2:4]}; }
    function new(string name="seq_stress_read"); super.new(name); endfunction

    task body();
        `uvm_info("SEQ", $sformatf("Stress read: %0d rounds", rounds), UVM_LOW)
        for (int r = 0; r < rounds; r++)
            for (int i = 0; i < FIFO_DEPTH; i++)
                read_one(0);
    endtask
endclass

// ─── 場景 5：非對稱速率（寫快讀慢 / 寫慢讀快）────────────────────────────
class seq_fast_write extends fifo_base_write_seq;
    `uvm_object_utils(seq_fast_write)
    function new(string name="seq_fast_write"); super.new(name); endfunction

    task body();
        `uvm_info("SEQ", "Fast write (no gap)", UVM_LOW)
        for (int i = 0; i < FIFO_DEPTH; i++)
            write_data($urandom_range(0,255), 0);  // gap=0：盡可能快
    endtask
endclass

class seq_slow_read extends fifo_base_read_seq;
    `uvm_object_utils(seq_slow_read)
    function new(string name="seq_slow_read"); super.new(name); endfunction

    task body();
        `uvm_info("SEQ", "Slow read (gap=3)", UVM_LOW)
        for (int i = 0; i < FIFO_DEPTH; i++)
            read_one(3);  // 每次讀完等 3 個 RCLK
    endtask
endclass


// =============================================================================
// cdc_tests.sv
// 所有 Test Class
// =============================================================================

// ─── Base Test ───────────────────────────────────────────────────────────────
class cdc_base_test extends uvm_test;
    `uvm_component_utils(cdc_base_test)

    cdc_fifo_env env;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = cdc_fifo_env::type_id::create("env", this);
    endfunction

    // 共用 reset task（在 top_tb 透過 vif 操作）
    task apply_reset(virtual cdc_fifo_if vif, int rst_cycles = 5);
        vif.WRST_N = 1'b0;
        vif.RRST_N = 1'b0;
        repeat(rst_cycles) @(posedge vif.WCLK);
        @(posedge vif.RCLK);
        vif.WRST_N = 1'b1;
        vif.RRST_N = 1'b1;
        `uvm_info("TEST", "Reset released", UVM_LOW)
    endtask
endclass

// ─── Test 1：基本讀寫正確性 ──────────────────────────────────────────────
class test_basic_rw extends cdc_base_test;
    `uvm_component_utils(test_basic_rw)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction

    task run_phase(uvm_phase phase);
        seq_basic_write  wseq;
        seq_basic_read   rseq;
        virtual cdc_fifo_if vif;
        phase.raise_objection(this);

        uvm_config_db #(virtual cdc_fifo_if)::get(null, "uvm_test_top", "vif", vif);
        apply_reset(vif);

        wseq = seq_basic_write::type_id::create("wseq");
        rseq = seq_basic_read::type_id::create("rseq");
        wseq.n = 8; rseq.n = 8;

        // 先寫後讀（等寫完再讀）
        fork
            wseq.start(env.write_agent.sequencer);
        join
        // 加一點延遲等同步 latency（2 RCLK）
        repeat(10) @(posedge vif.RCLK);
        fork
            rseq.start(env.read_agent.sequencer);
        join

        #500ns;
        phase.drop_objection(this);
    endtask
endclass

// ─── Test 2：WFULL 邊界 ───────────────────────────────────────────────────
class test_full_boundary extends cdc_base_test;
    `uvm_component_utils(test_full_boundary)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction

    task run_phase(uvm_phase phase);
        seq_fill_fifo  fseq;
        seq_drain_fifo dseq;
        virtual cdc_fifo_if vif;
        phase.raise_objection(this);

        uvm_config_db #(virtual cdc_fifo_if)::get(null, "uvm_test_top", "vif", vif);
        apply_reset(vif);

        fseq = seq_fill_fifo::type_id::create("fseq");
        dseq = seq_drain_fifo::type_id::create("dseq");

        fseq.start(env.write_agent.sequencer);
        repeat(10) @(posedge vif.RCLK);
        dseq.start(env.read_agent.sequencer);

        #1000ns;
        phase.drop_objection(this);
    endtask
endclass

// ─── Test 3：非對稱速率（寫快讀慢）────────────────────────────────────────
class test_asymmetric_rate extends cdc_base_test;
    `uvm_component_utils(test_asymmetric_rate)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction

    task run_phase(uvm_phase phase);
        seq_fast_write fwseq;
        seq_slow_read  srseq;
        virtual cdc_fifo_if vif;
        phase.raise_objection(this);

        uvm_config_db #(virtual cdc_fifo_if)::get(null, "uvm_test_top", "vif", vif);
        apply_reset(vif);

        fwseq = seq_fast_write::type_id::create("fwseq");
        srseq = seq_slow_read::type_id::create("srseq");

        // 寫讀同時開始（fork），寫端快、讀端慢
        fork
            fwseq.start(env.write_agent.sequencer);
            srseq.start(env.read_agent.sequencer);
        join

        #2000ns;
        phase.drop_objection(this);
    endtask
endclass

// ─── Test 4：Back-to-Back 壓力測試 ───────────────────────────────────────
class test_stress extends cdc_base_test;
    `uvm_component_utils(test_stress)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction

    task run_phase(uvm_phase phase);
        seq_stress_write swseq;
        seq_stress_read  srseq;
        virtual cdc_fifo_if vif;
        phase.raise_objection(this);

        uvm_config_db #(virtual cdc_fifo_if)::get(null, "uvm_test_top", "vif", vif);
        apply_reset(vif);

        swseq = seq_stress_write::type_id::create("swseq");
        srseq = seq_stress_read::type_id::create("srseq");
        swseq.rounds = 3;
        srseq.rounds = 3;

        fork
            swseq.start(env.write_agent.sequencer);
            srseq.start(env.read_agent.sequencer);
        join

        #2000ns;
        phase.drop_objection(this);
    endtask
endclass

// ─── Test 5：非同步 Reset（兩端 reset 時機不同）──────────────────────────
class test_async_reset extends cdc_base_test;
    `uvm_component_utils(test_async_reset)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction

    task run_phase(uvm_phase phase);
        seq_basic_write wseq;
        seq_basic_read  rseq;
        virtual cdc_fifo_if vif;
        phase.raise_objection(this);

        uvm_config_db #(virtual cdc_fifo_if)::get(null, "uvm_test_top", "vif", vif);

        // 先讓 write 端 reset，read 端晚 3 個 WCLK 才 reset
        vif.WRST_N = 1'b0;
        vif.RRST_N = 1'b1;
        repeat(3) @(posedge vif.WCLK);
        vif.RRST_N = 1'b0;
        repeat(5) @(posedge vif.WCLK);
        vif.WRST_N = 1'b1;
        repeat(2) @(posedge vif.RCLK);
        vif.RRST_N = 1'b1;
        `uvm_info("TEST", "Async reset complete", UVM_LOW)

        wseq = seq_basic_write::type_id::create("wseq");
        rseq = seq_basic_read::type_id::create("rseq");
        wseq.n = 6; rseq.n = 6;

        fork
            wseq.start(env.write_agent.sequencer);
            begin
                repeat(20) @(posedge vif.RCLK);
                rseq.start(env.read_agent.sequencer);
            end
        join

        #1000ns;
        phase.drop_objection(this);
    endtask
endclass
