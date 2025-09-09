class ahb_write_agent extends uvm_agent;
  `uvm_component_utils(ahb_write_agent)

  ahb_write_driver     drv;
  ahb_write_monitor    mon;
  uvm_sequencer #(ahb_transaction) sequencer;

  virtual ahb_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual ahb_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "No virtual interface")

    drv = ahb_write_driver::type_id::create("drv", this);
    mon = ahb_write_monitor::type_id::create("mon", this);
    sequencer = uvm_sequencer#(ahb_transaction)::type_id::create("seqr", this);

    uvm_config_db#(virtual ahb_if)::set(this, "drv", "vif", vif);
    uvm_config_db#(virtual ahb_if)::set(this, "mon", "vif", vif);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    drv.seq_item_port.connect(sequencer.seq_item_export);
  endfunction
endclass
