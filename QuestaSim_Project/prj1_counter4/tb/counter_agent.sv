`include "uvm_macros.svh"
import uvm_pkg::*;

class counter_agent extends uvm_agent;
  counter_driver drv;
  counter_monitor mon;
  uvm_sequencer #(counter_seq_item) seqr;

  virtual counter_if vif;

  `uvm_component_utils(counter_agent)

  function new(string name="counter_agent", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if(!uvm_config_db#(virtual counter_if)::get(this, "", "vif", vif))
        `uvm_fatal("NOVIF", "virtual interface must be set for counter_agent")

    drv  = counter_driver::type_id::create("drv", this);
    mon  = counter_monitor::type_id::create("mon", this);
    seqr = uvm_sequencer#(counter_seq_item)::type_id::create("seqr", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    drv.seq_item_port.connect(seqr.seq_item_export);
    mon.vif = vif;
    drv.vif = vif;
  endfunction
endclass