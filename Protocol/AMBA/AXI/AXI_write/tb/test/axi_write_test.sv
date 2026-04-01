class axi_write_test extends uvm_test;
  `uvm_component_utils(axi_write_test)

  axi_write_env env;
  axi_write_sequence seq;

  function new(string name = "axi_write_test", uvm_component parent = null); 
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    env = axi_write_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    seq = axi_write_sequence::type_id::create("seq");
    seq.start(env.write_agent.sequencer);
    phase.drop_objection(this);
  endtask
endclass
