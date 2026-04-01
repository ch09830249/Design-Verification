`include "uvm_macros.svh"
import uvm_pkg::*;

class counter_test extends uvm_test;
  counter_env env;

  `uvm_component_utils(counter_test)

  function new(string name="counter_test", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = counter_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    counter_sequence seq;
    phase.raise_objection(this);
    seq = counter_sequence::type_id::create("seq");
    seq.start(env.agt.seqr);
    #100ns;
    phase.drop_objection(this);
  endtask
endclass