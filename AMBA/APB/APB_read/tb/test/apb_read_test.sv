class apb_read_test extends uvm_test;
  `uvm_component_utils(apb_read_test)

  apb_read_env env;
  apb_read_sequence seq;

  function new(string name = "apb_read_test", uvm_component parent = null); 
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = apb_read_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    seq = apb_read_sequence::type_id::create("seq");
    seq.start(env.read_agent.sequencer);
    phase.drop_objection(this);
  endtask
endclass
