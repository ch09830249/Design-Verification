// =============================================================================
// Desc : Virtual sequences orchestrate sub-sequences across the environment
//        Uses `uvm_declare_p_sequencer on virtual_sequencer.
// =============================================================================

// ---------------------------------------------------------------------------
// Virtual sequencer - holds handle to the real sequencer
// ---------------------------------------------------------------------------
class counter_virtual_sequencer extends uvm_sequencer;
    `uvm_component_utils(counter_virtual_sequencer)

    counter_sequencer counter_seqr;  // real sequencer reference

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass : counter_virtual_sequencer

// ---------------------------------------------------------------------------
// Base virtual sequence
// ---------------------------------------------------------------------------
class counter_base_vseq extends uvm_sequence;
    `uvm_object_utils(counter_base_vseq)
    `uvm_declare_p_sequencer(counter_virtual_sequencer)  //  p_sequencer on vseqr

    function new(string name = "counter_base_vseq");
        super.new(name);
    endfunction

    // Convenience task: run a sub-sequence on the real sequencer
    task run_seq(counter_base_seq seq);
        seq.start(p_sequencer.counter_seqr);
    endtask
endclass : counter_base_vseq

// ===========================================================================
// Virtual Sequence 1 : Basic up-count verification
// ===========================================================================
class vseq_basic_count extends counter_base_vseq;
    `uvm_object_utils(vseq_basic_count)

    function new(string name = "vseq_basic_count");
        super.new(name);
    endfunction

    task body();
        counter_reset_seq   rst_seq;
        counter_count_seq   cnt_seq;

        // Configure range
        p_sequencer.counter_seqr.cfg_min = 32'd0;
        p_sequencer.counter_seqr.cfg_max = 32'd7;

        `uvm_info("VSEQ_BASIC", "=== Basic Count Test ===", UVM_NONE)

        rst_seq = counter_reset_seq::type_id::create("rst_seq");
        run_seq(rst_seq);

        cnt_seq = counter_count_seq::type_id::create("cnt_seq");
        cnt_seq.num_cycles = 32;   // cover > 4 full sweeps of [0..7]
        run_seq(cnt_seq);
    endtask
endclass : vseq_basic_count

// ===========================================================================
// Virtual Sequence 2 : Reverse-pulse test
// ===========================================================================
class vseq_reverse extends counter_base_vseq;
    `uvm_object_utils(vseq_reverse)

    function new(string name = "vseq_reverse");
        super.new(name);
    endfunction

    task body();
        counter_reset_seq   rst_seq;
        counter_count_seq   cnt_seq;
        counter_reverse_seq rev_seq;

        p_sequencer.counter_seqr.cfg_min = 32'd2;
        p_sequencer.counter_seqr.cfg_max = 32'd10;

        `uvm_info("VSEQ_REV", "=== Reverse Pulse Test ===", UVM_NONE)

        rst_seq = counter_reset_seq::type_id::create("rst_seq");
        run_seq(rst_seq);

        // Count up a few cycles then reverse
        cnt_seq = counter_count_seq::type_id::create("cnt_seq");
        cnt_seq.num_cycles = 5;
        run_seq(cnt_seq);

        rev_seq = counter_reverse_seq::type_id::create("rev1");
        rev_seq.post_cycles = 8;
        run_seq(rev_seq);

        // Reverse again mid-downcount
        rev_seq = counter_reverse_seq::type_id::create("rev2");
        rev_seq.post_cycles = 6;
        run_seq(rev_seq);

        // Let it run to boundary bounce
        cnt_seq = counter_count_seq::type_id::create("cnt_seq2");
        cnt_seq.num_cycles = 20;
        run_seq(cnt_seq);
    endtask
endclass : vseq_reverse

// ===========================================================================
// Virtual Sequence 3 : Dynamic range change
// ===========================================================================
class vseq_range_change extends counter_base_vseq;
    `uvm_object_utils(vseq_range_change)

    function new(string name = "vseq_range_change");
        super.new(name);
    endfunction

    task body();
        counter_reset_seq rst_seq;
        counter_cfg_seq   cfg_seq;

        `uvm_info("VSEQ_CFG", "=== Dynamic Range Change Test ===", UVM_NONE)

        p_sequencer.counter_seqr.cfg_min = 32'd0;
        p_sequencer.counter_seqr.cfg_max = 32'd5;

        rst_seq = counter_reset_seq::type_id::create("rst_seq");
        run_seq(rst_seq);

        // Phase 1: count in [0..5]
        cfg_seq = counter_cfg_seq::type_id::create("cfg1");
        cfg_seq.new_min    = 32'd0;
        cfg_seq.new_max    = 32'd5;
        cfg_seq.run_cycles = 14;
        run_seq(cfg_seq);

        // Phase 2: widen to [3..15]
        cfg_seq = counter_cfg_seq::type_id::create("cfg2");
        cfg_seq.new_min    = 32'd3;
        cfg_seq.new_max    = 32'd15;
        cfg_seq.run_cycles = 30;
        run_seq(cfg_seq);

        // Phase 3: narrow to [10..12]
        cfg_seq = counter_cfg_seq::type_id::create("cfg3");
        cfg_seq.new_min    = 32'd10;
        cfg_seq.new_max    = 32'd12;
        cfg_seq.run_cycles = 12;
        run_seq(cfg_seq);
    endtask
endclass : vseq_range_change

// ===========================================================================
// Virtual Sequence 4 : Boundary stress + random reverses
// ===========================================================================
class vseq_stress extends counter_base_vseq;
    `uvm_object_utils(vseq_stress)

    function new(string name = "vseq_stress");
        super.new(name);
    endfunction

    task body();
        counter_reset_seq   rst_seq;
        counter_boundary_seq bnd_seq;
        counter_reverse_seq  rev_seq;
        int rnd_delay;

        p_sequencer.counter_seqr.cfg_min = 32'd5;
        p_sequencer.counter_seqr.cfg_max = 32'd12;

        `uvm_info("VSEQ_STRESS", "=== Boundary Stress Test ===", UVM_NONE)

        rst_seq = counter_reset_seq::type_id::create("rst_seq");
        run_seq(rst_seq);

        // Interleave boundary runs and random reverses
        repeat(4) begin
            bnd_seq = counter_boundary_seq::type_id::create("bnd");
            run_seq(bnd_seq);

            if (!std::randomize(rnd_delay) with { rnd_delay inside {[1:5]}; })
                rnd_delay = 2;

            rev_seq = counter_reverse_seq::type_id::create("rev");
            rev_seq.post_cycles = rnd_delay;
            run_seq(rev_seq);
        end
    endtask
endclass : vseq_stress
