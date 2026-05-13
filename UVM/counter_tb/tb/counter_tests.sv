// =============================================================================
// Desc : All UVM tests
// =============================================================================

// ---------------------------------------------------------------------------
// Base test
// ---------------------------------------------------------------------------
class counter_base_test extends uvm_test;
    `uvm_component_utils(counter_base_test)

    counter_env              env;
    counter_virtual_sequencer vseqr;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env   = counter_env             ::type_id::create("env",   this);
        vseqr = counter_virtual_sequencer::type_id::create("vseqr", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Wire virtual sequencer -> real sequencer inside env
        vseqr.counter_seqr = env.agent.sequencer;
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        run_vseq(phase);
        #100;
        phase.drop_objection(this);
    endtask

    // Override in child tests
    virtual task run_vseq(uvm_phase phase);
    endtask
endclass : counter_base_test

// ---------------------------------------------------------------------------
// Test 1: Basic count
// ---------------------------------------------------------------------------
class test_basic_count extends counter_base_test;
    `uvm_component_utils(test_basic_count)
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    task run_vseq(uvm_phase phase);
        vseq_basic_count vseq;
        vseq = vseq_basic_count::type_id::create("vseq");
        vseq.start(vseqr);
    endtask
endclass : test_basic_count

// ---------------------------------------------------------------------------
// Test 2: Reverse pulse
// ---------------------------------------------------------------------------
class test_reverse extends counter_base_test;
    `uvm_component_utils(test_reverse)
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    task run_vseq(uvm_phase phase);
        vseq_reverse vseq;
        vseq = vseq_reverse::type_id::create("vseq");
        vseq.start(vseqr);
    endtask
endclass : test_reverse

// ---------------------------------------------------------------------------
// Test 3: Dynamic range change
// ---------------------------------------------------------------------------
class test_range_change extends counter_base_test;
    `uvm_component_utils(test_range_change)
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    task run_vseq(uvm_phase phase);
        vseq_range_change vseq;
        vseq = vseq_range_change::type_id::create("vseq");
        vseq.start(vseqr);
    endtask
endclass : test_range_change

// ---------------------------------------------------------------------------
// Test 4: Boundary stress
// ---------------------------------------------------------------------------
class test_stress extends counter_base_test;
    `uvm_component_utils(test_stress)
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    task run_vseq(uvm_phase phase);
        vseq_stress vseq;
        vseq = vseq_stress::type_id::create("vseq");
        vseq.start(vseqr);
    endtask
endclass : test_stress
