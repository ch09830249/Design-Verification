`include "uvm_macros.svh"
import uvm_pkg::*;

class counter_env extends uvm_env;
  counter_agent agt;
  counter_scoreboard scb;

  `uvm_component_utils(counter_env)

  function new(string name="counter_env", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agt = counter_agent::type_id::create("agt", this);
    scb = counter_scoreboard::type_id::create("scb", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    agt.mon.ap.connect(scb.imp);
    scb.vif = agt.vif;
  endfunction
endclass