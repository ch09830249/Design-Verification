// 整合 driver、sequencer、monitor，支援 active/passive 兩種模式
class axi_agent extends uvm_agent;
    `uvm_component_utils(axi_agent)

    axi_sequencer     sequencer;
    axi_driver        driver;
    axi_monitor       monitor;

    virtual axi_if    vif;
    bit               is_master;
    uvm_active_passive_enum is_active;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if (!uvm_config_db#(virtual axi_if)::get(this, "", "vif", vif))
            `uvm_fatal("AXI_AGENT", "Virtual interface not found")

        if (!uvm_config_db#(bit)::get(this, "", "is_master", is_master))
            is_master = 1;

        if (!uvm_config_db#(uvm_active_passive_enum)::get(this, "", "is_active", is_active))
            is_active = UVM_ACTIVE;

        if (is_active == UVM_ACTIVE) begin
            sequencer = axi_sequencer::type_id::create("sequencer", this);
            driver    = axi_driver::type_id::create("driver", this);
        end

        monitor = axi_monitor::type_id::create("monitor", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        if (is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction
endclass
