class axi_agent extends uvm_agent;
    `uvm_component_utils(axi_agent)

    axi_sequencer               sequencer;
    axi_driver                  driver;
    axi_monitor                 monitor;
    uvm_active_passive_enum     is_active;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if (!uvm_config_db#(uvm_active_passive_enum)::get(this, "", "is_active", is_active))
            `uvm_fatal("AXI_AGT", "Get is_active failed!")

        if (is_active == UVM_ACTIVE) begin
            sequencer = axi_sequencer::type_id::create("sequencer", this);
            driver    = axi_driver::type_id::create("driver", this);
        end

        monitor = axi_monitor::type_id::create("monitor", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        if (is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);            // driver 和 sequencer 連接
        end
    endfunction
endclass
