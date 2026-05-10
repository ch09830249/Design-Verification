// =============================================================================
// File : counter_scoreboard.sv
// Desc : Output-based checker.
//        Strategy: on each transaction, use the PREVIOUS observed outputs
//        (count, direction) plus the CURRENT inputs (reverse, min, max) to
//        predict what the DUT *should* output THIS cycle, then compare.
//        This avoids any driver/monitor timing skew because we never try to
//        predict future values -- we always compare what we just sampled
//        against what the reference model says should appear right now.
// =============================================================================
class counter_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(counter_scoreboard)

    uvm_analysis_imp #(counter_seq_item, counter_scoreboard) analysis_export;

    // Previous cycle's observed outputs (seeds the model)
    logic [31:0] prev_count;
    logic        prev_dir;
    logic [31:0] prev_min;
    logic [31:0] prev_max;
    logic        prev_reverse;
    logic        first_valid;   // false until we have one clean post-reset sample
    logic        in_reset;

    int pass_cnt, fail_cnt;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        analysis_export = new("analysis_export", this);
        first_valid  = 0;
        in_reset     = 1;
        pass_cnt     = 0;
        fail_cnt     = 0;
    endfunction

    function void write(counter_seq_item item);
        logic [31:0] exp_count;
        logic        exp_dir;

        // ---- Reset handling ----
        if (!item.rst_n) begin
            first_valid = 0;
            in_reset    = 1;
            return;
        end

        // First cycle out of reset: just record, don't check
        if (in_reset || !first_valid) begin
            prev_count   = item.count;
            prev_dir     = item.direction;
            prev_min     = item.min_val;
            prev_max     = item.max_val;
            prev_reverse = item.reverse;
            first_valid  = 1;
            in_reset     = 0;
            return;
        end

        // ----------------------------------------------------------------
        // Predict current outputs from PREVIOUS state + PREVIOUS inputs
        // (mirrors exactly what the RTL clocked in on the last posedge)
        // ----------------------------------------------------------------

        // Direction update (uses prev_reverse, prev_count, prev_min/max)
        if (prev_reverse) begin
            exp_dir = ~prev_dir;
        end else if (!prev_dir && (prev_count == prev_max)) begin
            exp_dir = 1'b1;
        end else if (prev_dir && (prev_count == prev_min)) begin
            exp_dir = 1'b0;
        end else begin
            exp_dir = prev_dir;
        end

        // Count update (uses prev_dir before the direction flip)
        if (!prev_dir) begin   // was counting up
            exp_count = (prev_count == prev_max) ? prev_min : prev_count + 1;
        end else begin         // was counting down
            exp_count = (prev_count == prev_min) ? prev_max : prev_count - 1;
        end

        // ---- Compare ----
        if (item.count !== exp_count || item.direction !== exp_dir) begin
            `uvm_error("SCOREBOARD",
                $sformatf("MISMATCH: got count=%0d dir=%0b | exp count=%0d dir=%0b  (prev_count=%0d prev_dir=%0b min=%0d max=%0d reverse=%0b)",
                    item.count, item.direction,
                    exp_count, exp_dir,
                    prev_count, prev_dir,
                    item.min_val, item.max_val, prev_reverse))
            fail_cnt++;
        end else begin
            `uvm_info("SCOREBOARD",
                $sformatf("PASS: count=%0d dir=%0b (min=%0d max=%0d)",
                    item.count, item.direction,
                    item.min_val, item.max_val),
                UVM_HIGH)
            pass_cnt++;
        end

        // ---- Advance state ----
        prev_count   = item.count;
        prev_dir     = item.direction;
        prev_min     = item.min_val;
        prev_max     = item.max_val;
        prev_reverse = item.reverse;
    endfunction

    function void report_phase(uvm_phase phase);
        `uvm_info("SCOREBOARD",
            $sformatf("=== RESULTS  PASS:%0d  FAIL:%0d ===", pass_cnt, fail_cnt),
            UVM_NONE)
        if (fail_cnt > 0)
            `uvm_error("SCOREBOARD", "TEST FAILED - see mismatches above")
    endfunction
endclass : counter_scoreboard
