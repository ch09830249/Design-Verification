class apb_write_test extends uvm_test;
  `uvm_component_utils(apb_write_test)

  apb_write_env env;
  apb_write_sequence seq;

  function new(string name = "apb_write_test", uvm_component parent = null); 
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = apb_write_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    seq = apb_write_sequence::type_id::create("seq");
    seq.start(env.write_agent.sequencer);
    phase.drop_objection(this);
  endtask
endclass
