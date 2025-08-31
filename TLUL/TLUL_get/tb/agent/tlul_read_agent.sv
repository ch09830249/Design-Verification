class tlul_get_agent extends uvm_agent;
  `uvm_component_utils(tlul_get_agent)

  tlul_get_sequencer sequencer;
  tlul_get_driver    driver;
  tlul_get_monitor   monitor;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    sequencer = tlul_get_sequencer::type_id::create("sequencer", this);
    driver    = tlul_get_driver   ::type_id::create("driver", this);
    monitor   = tlul_get_monitor  ::type_id::create("monitor", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);
  endfunction
endclass
