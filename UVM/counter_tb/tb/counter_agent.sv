class counter_agent extends uvm_agent;
    `uvm_component_utils(counter_agent)

    counter_driver     driver;
    counter_monitor    monitor;
    counter_sequencer  sequencer;

    uvm_analysis_port #(counter_seq_item) ap; // forwarded from monitor

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ap        = new("ap", this);
        monitor   = counter_monitor       ::type_id::create("monitor",   this);
        if (get_is_active() == UVM_ACTIVE) begin
            driver    = counter_driver    ::type_id::create("driver",    this);
            sequencer = counter_sequencer ::type_id::create("sequencer", this);
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        if (get_is_active() == UVM_ACTIVE)
            driver.seq_item_port.connect(sequencer.seq_item_export);
        monitor.ap.connect(ap);         // monitor => agent, and then agent would send item to scb
    endfunction
endclass : counter_agent
