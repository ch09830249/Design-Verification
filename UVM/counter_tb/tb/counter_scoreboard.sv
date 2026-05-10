// =============================================================================
// File : counter_scoreboard.sv
// Desc : Reference model - predicts next count and direction
// =============================================================================
class counter_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(counter_scoreboard)

    uvm_analysis_imp #(counter_seq_item, counter_scoreboard) analysis_export;

    // Reference model state
    logic [31:0] exp_count;
    logic        exp_dir;       // 0=up 1=down
    logic [31:0] exp_min;
    logic [31:0] exp_max;
    logic        model_init;

    int pass_cnt, fail_cnt;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        analysis_export = new("analysis_export", this);
        model_init = 0;
        pass_cnt   = 0;
        fail_cnt   = 0;
    endfunction

    function void write(counter_seq_item item);
        // On reset, re-initialise model
        if (!item.rst_n) begin
            model_init = 0;
            return;
        end

        if (!model_init) begin
            // First valid transaction after reset - seed the model
            exp_count  = item.count;
            exp_dir    = item.direction;
            exp_min    = item.min_val;
            exp_max    = item.max_val;
            model_init = 1;
            return;
        end

        // Update min/max from what was driven
        exp_min = item.min_val;
        exp_max = item.max_val;

        // Advance reference model one cycle
        begin
            logic        next_dir;
            logic [31:0] next_count;

            // Direction update (mirrors RTL)
            if (item.reverse) begin          // single-cycle pulse seen
                next_dir = ~exp_dir;
            end else if (!exp_dir && (exp_count == exp_max)) begin
                next_dir = 1'b1;
            end else if (exp_dir && (exp_count == exp_min)) begin
                next_dir = 1'b0;
            end else begin
                next_dir = exp_dir;
            end

            // Count update
            if (!exp_dir) begin              // was counting up before update
                next_count = (exp_count == exp_max) ? exp_min : exp_count + 1;
            end else begin                   // was counting down
                next_count = (exp_count == exp_min) ? exp_max : exp_count - 1;
            end

            exp_dir   = next_dir;
            exp_count = next_count;
        end

        // Compare
        if (item.count !== exp_count || item.direction !== exp_dir) begin
            `uvm_error("SCOREBOARD",
                $sformatf("MISMATCH: got count=%0d dir=%0b | exp count=%0d dir=%0b  (min=%0d max=%0d reverse=%0b)",
                    item.count, item.direction, exp_count, exp_dir,
                    exp_min, exp_max, item.reverse))
            fail_cnt++;
        end else begin
            `uvm_info("SCOREBOARD",
                $sformatf("PASS: count=%0d dir=%0b (min=%0d max=%0d reverse=%0b)",
                    item.count, item.direction, exp_min, exp_max, item.reverse),
                UVM_HIGH)
            pass_cnt++;
        end
    endfunction

    function void report_phase(uvm_phase phase);
        `uvm_info("SCOREBOARD",
            $sformatf("=== RESULTS  PASS:%0d  FAIL:%0d ===", pass_cnt, fail_cnt),
            UVM_NONE)
        if (fail_cnt > 0)
            `uvm_error("SCOREBOARD", "TEST FAILED - see mismatches above")
    endfunction
endclass : counter_scoreboard
